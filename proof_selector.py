"""
Score, rank and select the best LLM proof candidates.

Pipeline:
  1. Verify each proof candidate via REPL
  2. Classify errors (semantic > missing_constant > syntax)
  3. Score & rank candidates
  4. For selected candidates, run sorrify -> repair -> extract subgoals
"""

import os
import re
import json
from dataclasses import dataclass, field
from concurrent.futures import ThreadPoolExecutor, as_completed
from prover.lean.verifier import verify_lean4_file
from utils.syntax_repair import SyntaxCorrector
from utils.sorrify import Sorrifier, ProofTree
from utils.hint_repair import ProofRepairer
from utils.extract_proof_state import extract_queries


# ---------------------------------------------------------------------------
# Error classification
# ---------------------------------------------------------------------------

SEMANTIC_PATTERNS = [
    r"type mismatch",
    r"failed to synthesize",
    r"linarith failed",
    r"omega failed",
    r"nlinarith failed",
    r"ring_nf failed",
    r"simp made no progress",
    r"unsolved goals",
    r"tactic .+ failed",
    r"application type mismatch",
    r"has type.*but is expected to have type",
    r"function expected",
    r"no goals to be solved",
    r"mod_cast",
    r"norm_num failed",
    r"norm_cast failed",
]

MISSING_CONSTANT_PATTERNS = [
    r"unknown constant",
    r"unknown identifier",
    r"unknown namespace",
    r"not found",
]

SYNTAX_PATTERNS = [
    r"unexpected token",
    r"expected command",
    r"expected '.+'",
    r"unterminated",
    r"unexpected end of input",
    r"expected token",
    r"unknown tactic",
    r"invalid escape sequence"
]


def classify_error(error_msg: str) -> str:
    """Return one of: 'semantic', 'missing_constant', 'syntax', 'other'."""
    for pat in SEMANTIC_PATTERNS:
        if re.search(pat, error_msg, re.IGNORECASE):
            return "semantic"
    for pat in MISSING_CONSTANT_PATTERNS:
        if re.search(pat, error_msg, re.IGNORECASE):
            return "missing_constant"
    for pat in SYNTAX_PATTERNS:
        if re.search(pat, error_msg, re.IGNORECASE):
            return "syntax"
    return "other"


def classify_errors(errors: list[dict]) -> dict[str, list[dict]]:
    """Group a list of REPL errors by category."""
    groups: dict[str, list[dict]] = {
        "semantic": [],
        "missing_constant": [],
        "syntax": [],
        "other": [],
    }
    for e in errors:
        cat = classify_error(e["data"])
        groups[cat].append(e)
    return groups


# ---------------------------------------------------------------------------
# Scoring
# ---------------------------------------------------------------------------

CATEGORY_WEIGHT = {
    "semantic": 0,        # best – survived parsing
    "missing_constant": 1,
    "other": 2,
    "syntax": 3,          # worst
}


@dataclass
class ScoredProof:
    idx: int
    code: str
    status: str                         # COMPLETE / PASS / FAIL
    verify_time: float
    errors: list[dict] = field(default_factory=list)
    sorries: list[dict] = field(default_factory=list)
    error_groups: dict = field(default_factory=dict)
    worst_category: str = "syntax"
    first_error_line: int = 9999
    raw_score: float = 999.0            # from initial verify (lower = better)
    # populated after sorrification
    sorrified_code: str = ""
    num_sorries: int = 9999
    num_preserved_steps: int = 0
    final_score: float = 999.0          # after sorrify (lower = better)

    def compute_raw_score(self):
        if self.status == "COMPLETE":
            self.raw_score = -1000.0
            return
        if self.status == "PASS":
            self.raw_score = -500.0
            return
        if not self.errors:
            self.raw_score = 0.0
            return

        real_errors = [e for e in self.errors if not re.search(r"unsolved goals|no goals", e["data"], re.IGNORECASE)]
        if not real_errors:
            real_errors = self.errors

        real_errors.sort(key=lambda e: e["pos"]["line"])
        first_err = real_errors[0]
        self.first_error_line = first_err["pos"]["line"]
        self.worst_category = classify_error(first_err["data"])

        cat_score = CATEGORY_WEIGHT.get(self.worst_category, 2) * 1000
        line_bonus = self.first_error_line * 10
        self.raw_score = cat_score - line_bonus - self.verify_time

    def compute_final_score(self):
        """Score: more preserved steps = better (main), fewer sorries = tiebreaker."""
        if self.status == "COMPLETE":
            self.final_score = -1000.0
            return
        if not self.sorrified_code:
            self.final_score = self.raw_score
            return
        self.final_score = -(self.num_preserved_steps * 100) + self.num_sorries * 50


def _verify_one(idx: int, code: str, timeout: int) -> ScoredProof:
    code = SyntaxCorrector(code).correct_text()
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


def score_candidates(header: str, proofs: list[str], timeout: int = 300,
                     max_workers: int = None) -> list[ScoredProof]:
    """Stage 1: verify and quick-score candidates in parallel."""
    if max_workers is None:
        max_workers = min(len(proofs), os.cpu_count() or 4)

    codes = [header + body for body in proofs]
    results = [None] * len(proofs)

    with ThreadPoolExecutor(max_workers=max_workers) as pool:
        futures = {
            pool.submit(_verify_one, idx, code, timeout): idx
            for idx, code in enumerate(codes)
        }
        for fut in as_completed(futures):
            idx = futures[fut]
            results[idx] = fut.result()
            sp = results[idx]
            print(f"  [scored] #{sp.idx:2d}  status={sp.status}  "
                  f"cat={sp.worst_category}  err_line={sp.first_error_line}  "
                  f"time={sp.verify_time:.1f}s")

    results.sort(key=lambda s: s.raw_score)
    return results


# ---------------------------------------------------------------------------
# Stage 2: Sorrify + Repair (parallel) to assess structural quality
# ---------------------------------------------------------------------------

def _sorrify_and_repair_one(sp: ScoredProof) -> ScoredProof:
    """Sorrify + auto-repair a candidate, then count remaining sorries."""
    if sp.status == "COMPLETE":
        sp.sorrified_code = sp.code
        sp.num_sorries = 0
        sp.num_preserved_steps = len([l for l in sp.code.splitlines() if l.strip()])
        sp.compute_final_score()
        return sp
    try:
        pt = ProofTree(sp.code)
        pt.parse_lean_with_dot_subcases(clean_empty_lines=True, clean_comments=False)
        checker = Sorrifier(pt, verify_lean4_file, clean_empty_lines=True, clean_comments=False, max_cycles=20)
        sorrified = checker.verify_and_fix_tree()

        repairer = ProofRepairer(sorrified, verify_lean4_file, verbose=False)
        repaired = repairer.repair_proof()
        sp.sorrified_code = repaired

        lines = [l.strip() for l in repaired.splitlines() if l.strip()]
        sp.num_sorries = sum(1 for l in lines if l == "sorry")
        sp.num_preserved_steps = sum(1 for l in lines if l != "sorry")
    except Exception as e:
        print(f"  [sorrify+repair] failed for #{sp.idx}: {e}")
        sp.sorrified_code = ""
        sp.num_sorries = 9999
        sp.num_preserved_steps = 0

    sp.compute_final_score()
    return sp


def sorrify_candidates(candidates: list[ScoredProof],
                       max_workers: int = None) -> list[ScoredProof]:
    """Stage 2: sorrify + repair candidates in parallel and re-score."""
    if max_workers is None:
        max_workers = min(len(candidates), os.cpu_count() or 4)

    with ThreadPoolExecutor(max_workers=max_workers) as pool:
        futures = {pool.submit(_sorrify_and_repair_one, sp): sp.idx for sp in candidates}
        for fut in as_completed(futures):
            sp = fut.result()
            print(f"  [sorrified+repaired] #{sp.idx:2d}  sorries={sp.num_sorries}  "
                  f"preserved={sp.num_preserved_steps}  "
                  f"final_score={sp.final_score:.1f}")

    candidates.sort(key=lambda s: s.final_score)
    return candidates


# ---------------------------------------------------------------------------
# Stage 3: Extract subgoals from already-repaired code
# ---------------------------------------------------------------------------

def _normalize_goal(s: str) -> str:
    """Strip type annotations and whitespace for goal comparison."""
    s = re.sub(r"\(([^()]+?)\s*:\s*[^()]+?\)", r"\1", s)
    s = re.sub(r"\s+", " ", s).strip()
    return s


def _extract_lemma_name(code: str) -> str:
    """Extract lemma/theorem name from declaration."""
    m = re.search(r"(?:lemma|theorem)\s+(\w+)", code)
    return m.group(1) if m else "unknown"


def _extract_original_target(code: str) -> str:
    """
    Extract the theorem conclusion: text after the last ') :' before ':= by'.
    Handles: no params (lemma foo : ...), tight ') :', multi-line statement.
    Returns "" if not found (then we skip filtering by target).
    """
    idx = code.find(":= by")
    if idx == -1:
        return ""
    decl = code[:idx]
    # Last ') :' or '):' before := by (conclusion starts after it)
    matches = list(re.finditer(r"\)\s*:\s*", decl))
    if not matches:
        return ""
    target = decl[matches[-1].end() :].strip()
    return _normalize_goal(target)


def _extract_one(sp: ScoredProof, original_target: str = "") -> list[dict]:
    """Extract subgoals, filtering out ones identical to original target."""
    if sp.status == "COMPLETE" or not sp.sorrified_code:
        return []
    try:
        queries = extract_queries(sp.sorrified_code)
        results = []
        for q in queries:
            goal = q["goal"].strip()
            normalized = _normalize_goal(goal)
            if original_target and normalized == original_target:
                print(f"  [filter] #{sp.idx} skipped subgoal (== original target)")
                continue
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


# ---------------------------------------------------------------------------
# Main pipeline
# ---------------------------------------------------------------------------

def select_and_extract(
    header: str,
    proof_bodies: list[str],
    top_k: int = 5,
    verify_timeout: int = 300,
    max_workers: int = None,
) -> dict:
    """
    3-stage pipeline:
      1. Quick verify all candidates (parallel) -> filter out syntax failures
      2. Sorrify + repair non-syntax candidates (parallel) -> score by structural quality
      3. Pick top-k -> extract subgoals (parallel)
    """
    # -- Stage 1: quick verify + raw score --
    print(f"=== Stage 1: Scoring {len(proof_bodies)} candidates ===")
    ranked = score_candidates(header, proof_bodies, timeout=verify_timeout, max_workers=max_workers)
    
    print(f"=== Ranked {len(ranked)} candidates ===")
    for sp in ranked:
        tag = sp.worst_category if sp.status == "FAIL" else sp.status
        print(f"  #{sp.idx:2d}  raw_score={sp.raw_score:7.1f}  status={sp.status:8s}  "
              f"cat={tag:18s}  err_line={sp.first_error_line}  "
              f"time={sp.verify_time:.1f}s")

    filtered = [s for s in ranked if s.worst_category != "syntax" or s.status != "FAIL"]
    if not filtered:
        filtered = ranked[:top_k]
        print(f"\n  All candidates have syntax errors, falling back to top {len(filtered)}")
    else:
        print(f"\n  Kept {len(filtered)} non-syntax candidates (dropped {len(ranked) - len(filtered)} syntax)")

    # -- Stage 2: sorrify + re-score --
    print(f"\n=== Stage 2: Sorrifying {len(filtered)} candidates ===")
    sorrified = sorrify_candidates(filtered, max_workers=max_workers)

    print(f"\n  Re-ranked by structural quality:")
    for sp in sorrified:
        print(f"  #{sp.idx:2d}  final_score={sp.final_score:7.1f}  "
              f"sorries={sp.num_sorries}  preserved={sp.num_preserved_steps}")

    selected = sorrified[:top_k]

    # -- Stage 3: extract subgoals --
    original_target = ""
    lemma_name = "unknown"
    if selected:
        original_target = _extract_original_target(selected[0].code)
        lemma_name = _extract_lemma_name(selected[0].code)
        if original_target:
            print(f"\n  Original target: {original_target[:80]}...")
        print(f"  Lemma name: {lemma_name}")

    print(f"\n=== Stage 3: Extracting subgoals from top {len(selected)} candidates ===")
    all_subgoals = []
    seen_goals = set()
    workers = max_workers or min(len(selected), os.cpu_count() or 4)

    with ThreadPoolExecutor(max_workers=workers) as pool:
        futures = {
            pool.submit(_extract_one, sp, original_target): sp
            for sp in selected
        }
        for fut in as_completed(futures):
            sp = futures[fut]
            subs = fut.result()
            for sub_idx, sg in enumerate(subs, 1):
                goal_key = sg["goal"]
                if goal_key not in seen_goals:
                    seen_goals.add(goal_key)
                    sg["name"] = f"{lemma_name}_c{sp.idx}_s{sub_idx}"
                    sg["sorry_index"] = sub_idx
                    all_subgoals.append(sg)
                    print(f"  [subgoal] {sg['name']}  goal={sg['goal'][:80]}...")

    print(f"\n=== Total unique subgoals: {len(all_subgoals)} ===")
    return {
        "ranked": ranked,
        "selected": selected,
        "subgoals": all_subgoals,
    }


# ---------------------------------------------------------------------------
# CLI entry point (works with parsed_outputs.txt format from extract_and_verify)
# ---------------------------------------------------------------------------

if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(description="Score proof candidates and extract subgoals")
    parser.add_argument("--input", type=str, default="logs.log")
    parser.add_argument("--top-k", type=int, default=10)
    parser.add_argument("--verify-timeout", type=int, default=300)
    parser.add_argument("--workers", type=int, default=16,
                        help="Max parallel verification workers (default: cpu_count)")
    parser.add_argument("--output", type=str, default=None,
                        help="Save results to JSON file")
    args = parser.parse_args()

    # Read input
    with open(args.input) as f:
        lines = f.readlines()

    # Read or auto-extract header
    for idx, line in enumerate(lines):
        if line.strip() == "--- PROMPT ---":
            prompt_block = []
            for j in range(idx + 1, len(lines)):
                if lines[j].strip().startswith("--- "):
                    break
                prompt_block.append(lines[j])
            prompt_text = "".join(prompt_block)
            m = re.search(r"```lean4?\s*\n(.*?)\n```", prompt_text, re.DOTALL)
            if m:
                header = m.group(1).strip() + "\n"
                print(f"Auto-extracted header from prompt ({len(header)} chars)")
            break

    if not header:
        print("No header found. Provide --header or ensure log contains --- PROMPT ---.")
        exit(1)

    # Parse proof bodies
    proof_bodies = []
    i = 0
    while i < len(lines):
        if lines[i].strip() == "--- PARSED OUTPUT ---":
            i += 1
            block = []
            while i < len(lines) and not lines[i].strip().startswith("--- ") and not lines[i].strip().startswith("===== "):
                block.append(lines[i])
                i += 1
            content = "".join(block).strip()
            if content and re.search(r"(have |sorry|rw |simp|linarith|omega|calc|intro |apply |exact )", content):
                proof_bodies.append(content)
        else:
            i += 1

    if not proof_bodies:
        print("No proof bodies found in input file.")
        exit(1)

    print(f"Loaded {len(proof_bodies)} proof candidates from {args.input}\n")

    result = select_and_extract(
        header=header,
        proof_bodies=proof_bodies,
        top_k=args.top_k,
        verify_timeout=args.verify_timeout,
        max_workers=args.workers,
    )

    # Pretty print subgoals
    print("\n" + "=" * 60)
    print("SUBGOAL SUMMARY")
    print("=" * 60)
    for i, sg in enumerate(result["subgoals"], 1):
        print(f"\n--- Subgoal #{i} (from candidate #{sg['source_idx']}) ---")
        print(f"Goal: {sg['goal']}")
        if sg["hypotheses"]:
            print("Hypotheses:")
            for h in sg["hypotheses"]:
                if isinstance(h, dict):
                    print(f"  {h.get('name', '?')} : {h.get('type', '?')}")
                else:
                    print(f"  {h}")

    # Save to JSON
    if args.output:
        out_data = {
            "ranked": [
                {"idx": s.idx, "raw_score": s.raw_score, "final_score": s.final_score,
                 "status": s.status, "worst_category": s.worst_category,
                 "first_error_line": s.first_error_line, "num_sorries": s.num_sorries,
                 "num_preserved_steps": s.num_preserved_steps,
                 "verify_time": s.verify_time}
                for s in result["ranked"]
            ],
            "subgoals": result["subgoals"],
        }
        os.makedirs(os.path.dirname(args.output) or ".", exist_ok=True)
        with open(args.output, "w") as f:
            json.dump(out_data, f, indent=2, ensure_ascii=False)
        print(f"\nResults saved to {args.output}")
