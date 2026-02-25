from LLM import generate_reply
import textwrap
import json
import re

# Load JSON
with open("output/subgoals.json", "r", encoding="utf-8") as f:
    data = json.load(f)
    all_subgoals = data.get("subgoals", []) if isinstance(data, dict) else data

for i, subgoal in enumerate(all_subgoals):
    print(f"\n=== Solving subgoal {i+1}/{len(all_subgoals)}: {subgoal['name']} ===")
    
    # 1. Xử lý code_prefix: Cắt bỏ chữ 'sorry' cuối cùng để chừa chỗ trống cho LLM điền vào
    code_prefix = subgoal.get('code_prefix', '')
    if code_prefix.strip().endswith('sorry'):
        # Dùng rsplit để chỉ cắt chữ sorry ở vị trí con trỏ hiện tại
        code_prefix = code_prefix.rsplit('sorry', 1)[0].rstrip()
    
    # 2. Lấy Tactic State gốc (chuẩn xịn từ REPL)
    tactic_state = subgoal.get('raw', '').strip()
    
    # 3. Xây dựng Prompt "Sát thủ"
    prompt = textwrap.dedent(f"""
        <|im_start|>system
        You are an expert in mathematics and Lean 4 theorem proving.
        Your task is to provide the next Lean 4 tactics to solve the current goal.
        Output ONLY the raw Lean 4 code to replace the `sorry`. Do not include markdown formatting (```lean), explanations, or unrelated hypotheses.
        Prefer exact/apply over heavy tactics if the goal is simple.
        <|im_end|>
        <|im_start|>user
        Here is the current Lean 4 code up to the point of the missing proof:

        ```lean
        {code_prefix}
        ```

        Here is the exact tactic state at this point:

        ```lean
        {tactic_state}
        ```

        Write the Lean 4 tactics to close this goal.
        <|im_end|>
        <|im_start|>assistant
        """).strip()
    
    print("Generated prompt:")
    print(prompt)
    print("\n" + "="*50)
    
    # Generate solution
    solution = generate_reply(prompt, max_new_tokens=8192, temperature=0.6, top_p=0.95)
    
    # Dọn dẹp rác markdown nếu LLM cố tình sinh ra
    solution = solution.replace("```lean", "").replace("```", "").strip()
    
    print(f"\nSolution for {subgoal['name']}:")
    print(solution)
    print("\n" + "="*80)