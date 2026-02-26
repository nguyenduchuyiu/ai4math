import json
import re
from typing import Dict, List
import textwrap
from LLM import generate_reply

def extract_lean_tactic(llm_output: str) -> str:
    """
    Remove <think> tags, strip theorem/lemma wrappers,
    and PRESERVE INDENTATION at line heads for Lean 4 tactics.
    """
    text_without_think = llm_output
    code_blocks = re.findall(r'```(?:lean4?)(.*?)```', text_without_think, flags=re.DOTALL | re.IGNORECASE)
    # Strip only leading/trailing newlines, not indentation
    raw_code = code_blocks[-1].strip('\n') if code_blocks else text_without_think.strip('\n')
    raw_code = raw_code.replace('<|im_start|>', '').replace('<|im_end|>', '')

    # Remove spurious theorem/lemma at head, keep tactic block
    if raw_code.lstrip().startswith("theorem ") or raw_code.lstrip().startswith("lemma "):
        parts = raw_code.split(":= by", 1)
        if len(parts) > 1:
            return parts[1].strip('\n')
    return raw_code.strip('\n')

def load_cached_tactics_from_log(log_path: str = "solve.txt") -> List[str]:
    """
    Reload 'LLM Output (raw):' blocks from solve.txt,
    extract clean Lean tactics using extract_lean_tactic as during runtime.
    """
    raw_blocks: List[str] = []
    current: List[str] = []
    in_raw = False
    try:
        with open(log_path, "r", encoding="utf-8") as f:
            for line in f:
                if line.startswith("LLM Output (raw):"):
                    if in_raw and current:
                        raw_blocks.append("".join(current))
                        current = []
                    in_raw = True
                    continue
                if in_raw:
                    # End a raw block at '--- Extracted Lean tactics ---'
                    if line.startswith("--- Extracted Lean tactics ---"):
                        if current:
                            raw_blocks.append("".join(current))
                            current = []
                        in_raw = False
                        continue
                    current.append(line)
        if in_raw and current:
            raw_blocks.append("".join(current))
    except FileNotFoundError:
        return []

    # Extract and keep only non-empty tactics
    tactics: List[str] = []
    for raw in raw_blocks:
        t = extract_lean_tactic(raw)
        if t.strip():
            tactics.append(t)
    return tactics

# ========== 1. PROMPT CONSTRUCTION & CLEANUP UTILITIES ==========

def clean_lean_types(text: str) -> str:
    """
    Strip Lean 4 explicit type casts (e.g. (2 : ℕ), (18 : ℝ))
    for easier prompt readability.
    """
    text = re.sub(r'\(([^()]+?)\s*:\s*[ℕℝ]\)', r'\1', text)
    return text

def build_prompt(subgoal: dict) -> str:
    """
    Build a concise Lean 4 tactical prompt for the LLM.
    Only outputs the tactic sequence, not declarations/context.
    """
    tactic_state = clean_lean_types(subgoal.get('raw', '').strip())
    prompt = textwrap.dedent(f"""
        <|im_start|>system
        You are an expert Lean 4 tactician.
        You are provided with a specific Lean 4 Tactic State (Context and Goal).
        Your task is to write ONLY the sequence of tactics required to solve this exact goal.
        DO NOT write the `lemma` or `theorem` declaration.
        DO NOT rewrite the context.
        <|im_end|>
        <|im_start|>user
        Solve this isolated Lean 4 tactic state:

        ```lean
        {tactic_state}
        ```
        <|im_end|>
        <|im_start|>assistant
        """).strip()
    return prompt

# ========== 2. SAFE (INDENTATION-PRESERVING) CODE MERGE ==========

def merge_llm_solutions(skeleton_code: str, solutions: dict) -> str:
    """
    Replace 'sorry' lines with LLM Lean tactics, preserving indentation.
    """
    lines = skeleton_code.splitlines()
    sorted_lines = sorted(solutions.keys(), reverse=True)
    for line_num in sorted_lines:
        idx = line_num - 1
        target_line = lines[idx]
        # Target indentation (spaces before 'sorry')
        target_indent_spaces = len(target_line) - len(target_line.lstrip())
        target_indent_str = " " * target_indent_spaces

        # Handle non-breaking spaces, tabs
        llm_tactic_raw = solutions[line_num]
        llm_tactic_raw = llm_tactic_raw.replace('\xa0', ' ').expandtabs(4)
        llm_lines = llm_tactic_raw.splitlines()

        # Filter out markdown or empty lines
        clean_lines = []
        for l in llm_lines:
            if l.strip() and not l.strip().startswith("```"):
                clean_lines.append(l)

        if not clean_lines:
            continue

        # Find base indent (minimum indent among block lines)
        base_indent = min(len(l) - len(l.lstrip()) for l in clean_lines)

        # Reindent block lines relative to target
        indented_tactics = []
        for l in clean_lines:
            current_indent = len(l) - len(l.lstrip())
            relative_indent = current_indent - base_indent
            final_line = target_indent_str + (" " * relative_indent) + l.lstrip()
            indented_tactics.append(final_line)

        # Replace the sorry line with the indented tactic block
        lines = lines[:idx] + indented_tactics + lines[idx+1:]
    return "\n".join(lines)

# ========== 3. MAIN PIPELINE ==========

def main():
    # 1. Load JSON with subgoals
    with open("output/subgoals.json", "r", encoding="utf-8") as f:
        data = json.load(f)

    all_subgoals = data.get("subgoals", [])

    # 2. Select subgoals for Candidate #4 (source_idx: 4)
    target_candidate_idx = 4
    target_subgoals = [sg for sg in all_subgoals if sg["source_idx"] == target_candidate_idx]

    if not target_subgoals:
        print(f"No subgoals found for Candidate #{target_candidate_idx}")
        return

    print(f"Starting to solve {len(target_subgoals)} subgoals for Candidate #{target_candidate_idx}...")

    # Final code "skeleton" = code_prefix of the last subgoal (contains whole file)
    skeleton_code = target_subgoals[-1]["code_prefix"]
    if skeleton_code.strip().endswith("sorry"):
        pass
    else:
        print(f"Warning: Using code_prefix as Skeleton.")
    solutions_dict = {}
    cached_tactics = load_cached_tactics_from_log()
    cache_idx = 0
    for sg in target_subgoals:
        print(f"\n--- Solving: {sg['name']} (Line {sg['line']}) ---")
        prompt = build_prompt(sg)

        # Prefer cache if available
        if cache_idx < len(cached_tactics):
            tactic_only = cached_tactics[cache_idx]
            cache_idx += 1
            print("\n--- Using cached Lean tactics from solve.txt ---")
            print(tactic_only)
        else:
            print("Waiting for LLM response...")
            print(prompt)
            print("------------------------------------------")
            try:
                solution_raw = generate_reply(prompt, max_new_tokens=4096, temperature=0.6, top_p=0.95)
            except Exception as e:
                print(f"API Error: {e}")
                solution_raw = "sorry"
            print("\nLLM Output (raw):")
            print(solution_raw)
            tactic_only = extract_lean_tactic(solution_raw)
            print("\n--- Extracted Lean tactics ---")
            print(tactic_only)

        solutions_dict[sg["line"]] = tactic_only

    # 4. Merge tactics into skeleton
    print("\n==========================================")
    print("Merging code (Merge)...")
    final_code = merge_llm_solutions(skeleton_code, solutions_dict)

    # 5. Write to output
    out_file = "final_proof.lean"
    with open(out_file, "w", encoding="utf-8") as f:
        f.write(final_code)

    print(f"Success! Complete file saved to: {out_file}")
    print("Please use Lean REPL to verify this file!")

if __name__ == "__main__":
    main()