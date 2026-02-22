from LLM import generate_reply
import textwrap
import json
import re

with open("output/subgoals.json", "r") as f:
    logs = json.load(f)
    all_subgoals = logs["subgoals"]

# Extract header from code_prefix using regex
def extract_header(code_prefix):
    # Match everything from start until the lemma declaration
    header_match = re.match(r'^(.*?)(?=lemma\s)', code_prefix, re.DOTALL)
    if header_match:
        return header_match.group(1).strip()
    return ""

for i, subgoal in enumerate(all_subgoals):
    print(f"\n=== Solving subgoal {i+1}/{len(all_subgoals)}: {subgoal['name']} ===")
    
    # Extract header from this subgoal's code_prefix
    header = extract_header(subgoal['code_prefix'])
    
    # Build hypotheses string
    hypotheses_str = ""
    for hyp in subgoal["hypotheses"]:
        hypotheses_str += f"    ({hyp['name']} : {hyp['type']})\n"
    
    prompt = textwrap.dedent(
        f"""
        <|im_start|>system
        You are an expert in mathematics and Lean 4.
        Given a Lean proof state, produce valid Lean 4 tactics to solve the current goal.
        Do NOT analyze unrelated hypotheses.
        If the goal is directly implied by a hypothesis, use it immediately.
        Prefer exact/apply over heavy tactics.
        <|im_end|>

        <|im_start|>user
        Solve the following Lean 4 proof state.

        lean4
        {header}

        lemma {subgoal['name']}
{hypotheses_str.rstrip()}
        :
        {subgoal['goal']} := by
        Continue the proof using Lean tactics.
        <|im_end|>

        <|im_start|>assistant

        """
    ).strip()
    
    print("Generated prompt:")
    print(prompt)
    print("\n" + "="*50)
    
    # Generate solution
    solution = generate_reply(prompt, max_new_tokens=8192, temperature=0.6, top_p=0.95)
    
    print(f"\nSolution for {subgoal['name']}:")
    print(solution)
    print("\n" + "="*80)