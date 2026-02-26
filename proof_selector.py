"""
Score, rank, and select the best LLM proof candidates.

Pipeline:
  1. Verify each proof candidate via Lean 4 REPL.
  2. Classify errors (Semantic > Missing Constant > Syntax).
  3. Score & rank candidates based on error severity and location.
  4. For top candidates: run Sorrifier -> ProofRepairer -> Extract Subgoals.
"""

import os
import re
import json
import argparse
from dataclasses import dataclass, field
from concurrent.futures import ThreadPoolExecutor, as_completed
from typing import List, Dict, Any, Tuple

from prover.lean.verifier import verify_lean4_file
from utils.syntax_repair import SyntaxCorrector
from utils.scope_sorrifier import Sorrifier
from utils.hint_repair import ProofRepairer
from utils.proof_state_extractor import extract_queries


# ===========================================================================
# 1. ERROR CLASSIFICATION
# ===========================================================================

# Pre-compile regex patterns for performance
ERROR_PATTERNS = {
    "semantic": re.compile(
        r"type mismatch|failed to synthesize|linarith failed|omega failed|"
        r"nlinarith failed|ring_nf failed|simp made no progress|unsolved goals|"
        r"tactic .+ failed|application type mismatch|has type.*but is expected to have type|"
        r"function expected|no goals to be solved|mod_cast|norm_num failed|norm_cast failed", 
        re.IGNORECASE
    ),
    "missing_constant": re.compile(
        r"unknown constant|unknown identifier|unknown namespace|not found", 
        re.IGNORECASE
    ),
    "syntax": re.compile(
        r"unexpected token|expected command|expected '.+'|unterminated|"
        r"unexpected end of input|expected token|unknown tactic|invalid escape sequence", 
        re.IGNORECASE
    )
}

CATEGORY_WEIGHT = {
    "semantic": 0,          # Best: survived parsing and logical checks
    "missing_constant": 1,
    "other": 2,
    "syntax": 3,            # Worst: code is malformed
}

def classify_error(error_msg: str) -> str:
    """Classifies a Lean 4 error message into predefined categories."""
    for category, pattern in ERROR_PATTERNS.items():
        if pattern.search(error_msg):
            return category
    return "other"

def classify_errors(errors: List[Dict]) -> Dict[str, List[Dict]]:
    """Groups a list of REPL errors by their category."""
    groups = {"semantic": [], "missing_constant": [], "syntax": [], "other": []}
    for e in errors:
        groups[classify_error(e["data"])].append(e)
    return groups


# ===========================================================================
# 2. DATA STRUCTURES & SCORING
# ===========================================================================

@dataclass
class ScoredProof:
    idx: int
    code: str
    status: str                         # COMPLETE / PASS / FAIL
    verify_time: float
    errors: List[Dict] = field(default_factory=list)
    sorries: List[Dict] = field(default_factory=list)
    error_groups: Dict = field(default_factory=dict)
    
    # Computed during Stage 1
    worst_category: str = "syntax"
    first_error_line: int = 9999
    raw_score: float = 999.0            
    
    # Computed during Stage 2 (Sorrify & Repair)
    sorrified_code: str = ""
    num_sorries: int = 9999
    num_preserved_steps: int = 0
    final_score: float = 999.0          

    def compute_raw_score(self):
        """Scores initial candidate based on verification status and first error line."""
        if self.status == "COMPLETE":
            self.raw_score = -1000.0
            return
        if self.status == "PASS":
            self.raw_score = -500.0
            return
        if not self.errors:
            self.raw_score = 0.0
            return

        # Filter out consequence errors to find the root cause
        real_errors = [e for e in self.errors if not re.search(r"unsolved goals|no goals", e["data"], re.IGNORECASE)]
        real_errors = real_errors or self.errors
        real_errors.sort(key=lambda e: e["pos"]["line"])
        
        first_err = real_errors[0]
        self.first_error_line = first_err["pos"]["line"]
        self.worst_category = classify_error(first_err["data"])

        # Formula: Category Penalty - Depth Bonus - Time Penalty
        cat_score = CATEGORY_WEIGHT.get(self.worst_category, 2) * 1000
        line_bonus = self.first_error_line * 10
        self.raw_score = cat_score - line_bonus - self.verify_time

    def compute_final_score(self):
        """Scores structural quality: more preserved steps = better, fewer sorries = tiebreaker."""
        if self.status == "COMPLETE":
            self.final_score = -1000.0
        elif not self.sorrified_code:
            self.final_score = self.raw_score
        else:
            self.final_score = -(self.num_preserved_steps * 100) + (self.num_sorries * 50)


# ===========================================================================
# 3. PIPELINE STAGES
# ===========================================================================

def _verify_one(idx: int, code: str, timeout: int) -> ScoredProof:
    """Worker function for Stage 1."""
    r = verify_lean4_file(code, timeout=timeout)
    status = "COMPLETE" if r.get("complete") else ("PASS" if r.get("pass") else "FAIL")
    sp = ScoredProof(
        idx=idx,
        code=code,
        status=status,
        verify_time=r.get("verify_time", 0),
        errors=r.get("errors", []),
        sorries=r.get("sorries", []),
        error_groups=classify_errors(r.get("errors", [])),
    )
    sp.compute_raw_score()
    return sp

def _sorrify_and_repair_one(sp: ScoredProof) -> ScoredProof:
    """Worker function for Stage 2."""
    if sp.status == "COMPLETE":
        sp.sorrified_code, sp.num_sorries = sp.code, 0
        sp.num_preserved_steps = len([l for l in sp.code.splitlines() if l.strip()])
    else:
        try:
            code_corrected = SyntaxCorrector(sp.code).correct_text()
            checker = Sorrifier(verify_lean4_file, max_cycles=20)
            sorrified = checker.verify_and_fix(code_corrected)
            repairer = ProofRepairer(sorrified, verify_lean4_file)
            repaired = repairer.repair_proof()
            
            sp.sorrified_code = repaired
            lines = [l.strip() for l in repaired.splitlines() if l.strip()]
            sp.num_sorries = lines.count("sorry")
            sp.num_preserved_steps = len(lines) - sp.num_sorries
        except Exception as e:
            print(f"  [sorrify+repair] failed for #{sp.idx}: {e}")
            sp.sorrified_code, sp.num_sorries, sp.num_preserved_steps = "", 9999, 0

    sp.compute_final_score()
    return sp

def _extract_one(sp: ScoredProof, original_target: str = "") -> List[Dict]:
    """Worker function for Stage 3."""
    if sp.status == "COMPLETE" or not sp.sorrified_code:
        return []
    try:
        results = []
        for q in extract_queries(sp.sorrified_code):
            normalized = re.sub(r"\(([^()]+?)\s*:\s*[^()]+?\)", r"\1", q["goal"])
            normalized = re.sub(r"\s+", " ", normalized).strip()
            
            if original_target and normalized == original_target:
                continue # Skip trivial goals (identical to original target)
                
            results.append({
                "source_idx": sp.idx,
                "line": q["line"],
                "goal": q["goal"],
                "hypotheses": q["hypotheses"],
                "raw": q["raw"],
                "code_prefix": sp.sorrified_code,
            })
        return results
    except Exception as e:
        print(f"  [extract] failed for #{sp.idx}: {e}")
        return []

def select_and_extract(header: str, proof_bodies: List[str], top_k: int = 5, verify_timeout: int = 300, max_workers: int = 4) -> Dict:
    """Orchestrates the 3-stage proof extraction pipeline."""
    
    # --- Stage 1: Verify & Raw Score ---
    print(f"\n=== Stage 1: Scoring {len(proof_bodies)} candidates ===")
    codes = [header + body for body in proof_bodies]
    ranked = [None] * len(codes)

    with ThreadPoolExecutor(max_workers=max_workers) as pool:
        futures = {pool.submit(_verify_one, idx, code, verify_timeout): idx for idx, code in enumerate(codes)}
        for fut in as_completed(futures):
            idx = futures[fut]
            ranked[idx] = fut.result()
            sp = ranked[idx]
            print(f"  [scored] #{sp.idx:2d} | Status: {sp.status:8s} | Cat: {sp.worst_category:15s} | Line: {sp.first_error_line:<4} | Time: {sp.verify_time:.1f}s")

    ranked.sort(key=lambda s: s.raw_score)
    # filtered = [s for s in ranked if s.worst_category != "syntax" or s.status != "FAIL"]
    filtered = ranked
    
    # if not filtered:
    #     filtered = ranked[:top_k]
    #     print(f"\n  [!] All candidates have syntax errors. Falling back to top {len(filtered)}.")
    # else:
    #     print(f"\n  [+] Kept {len(filtered)} non-syntax candidates (Dropped {len(ranked) - len(filtered)}).")

    # --- Stage 2: Sorrify & Repair ---
    print(f"\n=== Stage 2: Sorrifying {len(filtered)} candidates ===")
    with ThreadPoolExecutor(max_workers=max_workers) as pool:
        futures = [pool.submit(_sorrify_and_repair_one, sp) for sp in filtered]
        sorrified = [fut.result() for fut in as_completed(futures)]
        
    for sp in sorrified:
        print(f"  [repaired] #{sp.idx:2d} | Score: {sp.final_score:7.1f} | Sorries: {sp.num_sorries:<3} | Preserved: {sp.num_preserved_steps}")

    sorrified.sort(key=lambda s: s.final_score)
    selected = sorrified[:top_k]

    # --- Stage 3: Extract Subgoals ---
    print(f"\n=== Stage 3: Extracting subgoals from top {len(selected)} candidates ===")
    all_subgoals = []
    seen_goals = set()
    
    # Determine original target to filter trivial subgoals
    original_target, lemma_name = "", "unknown"
    if selected:
        decl_match = re.search(r"(?:lemma|theorem)\s+(\w+)", selected[0].code)
        lemma_name = decl_match.group(1) if decl_match else "unknown"
        
        idx = selected[0].code.find(":= by")
        if idx != -1:
            matches = list(re.finditer(r"\)\s*:\s*", selected[0].code[:idx]))
            if matches:
                target_raw = selected[0].code[:idx][matches[-1].end():].strip()
                original_target = re.sub(r"\s+", " ", re.sub(r"\(([^()]+?)\s*:\s*[^()]+?\)", r"\1", target_raw))

    with ThreadPoolExecutor(max_workers=max_workers) as pool:
        futures = {pool.submit(_extract_one, sp, original_target): sp for sp in selected}
        for fut in as_completed(futures):
            sp = futures[fut]
            for sub_idx, sg in enumerate(fut.result(), 1):
                if sg["goal"] not in seen_goals:
                    seen_goals.add(sg["goal"])
                    sg["name"] = f"{lemma_name}_c{sp.idx}_s{sub_idx}"
                    sg["sorry_index"] = sub_idx
                    all_subgoals.append(sg)
                    print(f"  [extracted] {sg['name']} | Goal: {sg['goal'][:60]}...")

    print(f"\n=== Pipeline Complete. Total unique subgoals: {len(all_subgoals)} ===")
    return {"ranked": ranked, "selected": selected, "subgoals": all_subgoals}


# ===========================================================================
# 4. CLI ENTRY POINT & PARSER
# ===========================================================================

def parse_log_file(file_path: str) -> Tuple[str, List[str]]:
    """Parses the prompt log to extract the hardcoded header and proof bodies."""
    with open(file_path, 'r', encoding='utf-8') as f:
        lines = f.readlines()

    header = '''import Mathlib
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
lemma aime_1983_p3_1_1
  (f : ℝ → ℝ)
  (h₀ : ∀ (x : ℝ), f x = x ^ (2 : ℕ) + ((18 : ℝ) * x + (30 : ℝ)) - (2 : ℝ) * √(x ^ (2 : ℕ) + ((18 : ℝ) * x + (45 : ℝ))))
  (h₁ : Fintype (↑(f ⁻¹' {(0 : ℝ)}) : Type)) :
  ∏ x ∈ (f ⁻¹' {(0 : ℝ)}).toFinset, x = (20 : ℝ) := by
'''
    proof_bodies = []
    
    in_parsed_block = False
    current_body = []

    for idx, line in enumerate(lines):
        # Extract Proof Bodies
        stripped = line.strip()
        if stripped == "--- PARSED OUTPUT ---":
            in_parsed_block = True
            current_body = []
            continue
            
        if in_parsed_block:
            if stripped.startswith("--- ") or stripped.startswith("===== "):
                in_parsed_block = False
                content = "".join(current_body).strip()
                if content and re.search(r"(have |sorry|rw |simp|linarith|omega|calc|intro |apply |exact )", content):
                    proof_bodies.append(content)
            else:
                current_body.append(line)

    return header, proof_bodies


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Score proof candidates and extract subgoals")
    parser.add_argument("--input", type=str, default="logs.log")
    parser.add_argument("--top-k", type=int, default=10)
    parser.add_argument("--verify-timeout", type=int, default=300)
    parser.add_argument("--workers", type=int, default=16, help="Max parallel verification workers")
    parser.add_argument("--output", type=str, default="output/subgoals.json", help="Save results to JSON file")
    args = parser.parse_args()

    header, proof_bodies = parse_log_file(args.input)

    if not proof_bodies:
        print(f"[!] No proof bodies found in {args.input}.")
        exit(1)

    print(f"[*] Loaded {len(proof_bodies)} proof candidates. Extracted header size: {len(header)} chars.")

    result = select_and_extract(
        header=header,
        proof_bodies=proof_bodies,
        top_k=args.top_k,
        verify_timeout=args.verify_timeout,
        max_workers=args.workers,
    )

    # Save to JSON
    if args.output:
        out_data = {
            "ranked": [
                {
                    "idx": s.idx, "raw_score": s.raw_score, "final_score": s.final_score,
                    "status": s.status, "worst_category": s.worst_category,
                    "first_error_line": s.first_error_line, "num_sorries": s.num_sorries,
                    "num_preserved_steps": s.num_preserved_steps, "verify_time": s.verify_time
                }
                for s in result["ranked"]
            ],
            "subgoals": result["subgoals"],
        }
        os.makedirs(os.path.dirname(args.output) or ".", exist_ok=True)
        with open(args.output, "w", encoding='utf-8') as f:
            json.dump(out_data, f, indent=2, ensure_ascii=False)
        print(f"\n[+] Results successfully saved to {args.output}")