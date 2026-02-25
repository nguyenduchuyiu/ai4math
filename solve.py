import json
import re
from typing import Dict, List
import textwrap
# Thay bằng hàm gọi API thực tế của cậu
from LLM import generate_reply 

import re

def extract_lean_tactic(llm_output: str) -> str:
    """
    1. Xóa <think>
    2. Lấy code trong block ```lean
    3. Xé bỏ vỏ bọc 'theorem ... := by' nếu LLM tự bịa ra.
    """
    # 1. Xóa sạch block <think> (nếu sau này có)
    # text_without_think = re.sub(r'<think>.*?(?:</think>|(?=```))', '', llm_output, flags=re.DOTALL | re.IGNORECASE)
    text_without_think = llm_output
    # 2. Tìm block code Lean
    code_blocks = re.findall(r'```(?:lean?)(.*?)```', text_without_think, flags=re.DOTALL | re.IGNORECASE)
    
    if code_blocks:
        raw_code = code_blocks[-1].strip()
    else:
        # Fallback
        raw_code = text_without_think.strip().replace('<|im_start|>', '').replace('<|im_end|>', '')

    # 3. CHÉM VỎ BỌC THEOREM/LEMMA (Chỉ lấy lõi Tactic)
    # Nếu code bắt đầu bằng chữ theorem hoặc lemma
    if raw_code.startswith("theorem ") or raw_code.startswith("lemma "):
        # Tách chuỗi bằng chữ ':= by' đầu tiên gặp được
        parts = raw_code.split(":= by", 1)
        if len(parts) > 1:
            # Lấy toàn bộ phần ruột phía sau
            pure_tactic = parts[1].strip()
            return pure_tactic
    return raw_code.strip()


def load_cached_tactics_from_log(log_path: str = "solve.txt") -> List[str]:
    """
    Đọc lại các block sau dòng '--- Extracted Lean tactics ---' trong solve.txt.
    Trả về list tactics theo đúng thứ tự subgoal đã chạy lần trước.
    """
    blocks: List[str] = []
    current: List[str] = []
    in_block = False
    try:
        with open(log_path, "r", encoding="utf-8") as f:
            for line in f:
                if line.startswith("--- Extracted Lean tactics ---"):
                    if in_block and current:
                        blocks.append("".join(current).rstrip())
                        current = []
                    in_block = True
                    continue
                if in_block:
                    # Kết thúc block khi sang section mới
                    if line.startswith("--- ") and "Extracted Lean tactics" not in line:
                        if current:
                            blocks.append("".join(current).rstrip())
                            current = []
                        in_block = False
                        continue
                    current.append(line)
        if in_block and current:
            blocks.append("".join(current).rstrip())
    except FileNotFoundError:
        return []
    # Làm sạch block rỗng
    return [b.strip() for b in blocks if b.strip()]

# ==========================================
# 1. HÀM CHUẨN BỊ PROMPT VÀ DỌN RÁC
# ==========================================
def clean_lean_types(text: str) -> str:
    """Xóa các ép kiểu rác của Lean 4 (ví dụ: (2 : ℕ), (18 : ℝ)) để LLM dễ đọc hơn."""
    # Xóa (X : ℕ) hoặc (X : ℝ) -> chỉ giữ lại X
    text = re.sub(r'\(([^()]+?)\s*:\s*[ℕℝ]\)', r'\1', text)
    return text

def build_prompt(subgoal: dict) -> str:
    # Lấy đúng cái Tactic State đã được dọn sạch ép kiểu rác
    tactic_state = clean_lean_types(subgoal.get('raw', '').strip())
    
    # 🚨 VIẾT LẠI PROMPT: Bỏ hoàn toàn code_prefix, ép nó làm "Tactician" thay vì "Prover"
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

# ==========================================
# 2. HÀM GHÉP CODE (MERGE) SIÊU AN TOÀN
# ==========================================
def merge_llm_solutions(skeleton_code: str, solutions: dict) -> str:
    """
    Ghép tactic của LLM vào file gốc bằng cách thay thế các chữ 'sorry'.
    Giữ nguyên cấu trúc thụt lề lồng nhau (nested indentation) của LLM.
    """
    lines = skeleton_code.splitlines()
    sorted_lines = sorted(solutions.keys(), reverse=True)
    
    for line_num in sorted_lines:
        idx = line_num - 1
        target_line = lines[idx]
        
        # 1. Đo lề mục tiêu (Lề của chữ 'sorry' cũ)
        target_indent_spaces = len(target_line) - len(target_line.lstrip())
        target_indent_str = " " * target_indent_spaces
        
        # 2. Xử lý code LLM
        llm_tactic_raw = solutions[line_num]
        llm_lines = llm_tactic_raw.splitlines()
        
        # 3. Tìm "Lề cơ sở" (Base indent) của khối code LLM
        # (Đo lề của dòng code thực sự đầu tiên)
        base_indent = 0
        for line in llm_lines:
            if line.strip() and not line.strip().startswith("```"):
                base_indent = len(line) - len(line.lstrip())
                break
                
        indented_tactics = []
        for line in llm_lines:
            # Bỏ rác markdown và dòng trống
            if line.strip() in ["```lean", "```", "lean4", ""]:
                continue
            
            # 4. Tính toán độ thụt lề tương đối của từng dòng so với lề cơ sở
            current_indent = len(line) - len(line.lstrip())
            relative_indent = max(0, current_indent - base_indent)
            
            # 5. Lắp ghép: Lề của sorry + Lề tương đối bên trong khối code + Nội dung
            final_line = target_indent_str + (" " * relative_indent) + line.lstrip()
            indented_tactics.append(final_line)
            
        # 6. Thay thế vào file
        if indented_tactics:
            lines = lines[:idx] + indented_tactics + lines[idx+1:]
        
    return "\n".join(lines)


# ==========================================
# 3. LUỒNG CHẠY CHÍNH (PIPELINE)
# ==========================================
def main():
    # 1. Đọc file JSON của cậu
    with open("output/subgoals.json", "r", encoding="utf-8") as f:
        data = json.load(f)
        
    all_subgoals = data.get("subgoals", [])
    
    # 2. Lọc ra các subgoals của Candidate #4 (Vì nó là Candidate tốt nhất)
    # Trong JSON của cậu, Candidate 4 có "source_idx": 4
    target_candidate_idx = 4
    target_subgoals = [sg for sg in all_subgoals if sg["source_idx"] == target_candidate_idx]
    
    if not target_subgoals:
        print(f"Không tìm thấy subgoal nào cho Candidate #{target_candidate_idx}")
        return
        
    print(f"Bắt đầu giải {len(target_subgoals)} subgoals của Candidate #{target_candidate_idx}...")
    
    # Lấy Skeleton Code (chính là code_prefix của subgoal cuối cùng, nó chứa toàn bộ file)
    # Ta sẽ dùng nó làm cái khung để nhét code vào
    skeleton_code = target_subgoals[-1]["code_prefix"] 
    # Nếu code_prefix bị cắt mất cái sorry cuối cùng, ta khôi phục lại (vì ta cần skeleton gốc)
    if skeleton_code.strip().endswith("sorry"):
        pass # Đã có sorry
    else:
        # Trường hợp lấy subgoal khác, ta nên lấy file gốc từ Candidate
        print("Cảnh báo: Đang dùng code_prefix làm Skeleton.")

    # Dictionary lưu trữ kết quả: { số_dòng: "code_tactic" }
    solutions_dict = {}

    # 3. Gọi LLM giải từng Subgoal (hoặc dùng cache từ solve.txt nếu có)
    cached_tactics = load_cached_tactics_from_log()
    cache_idx = 0

    for sg in target_subgoals:
        print(f"\n--- Đang giải: {sg['name']} (Dòng {sg['line']}) ---")
        prompt = build_prompt(sg)

        # Nếu đã có cache thì ưu tiên dùng, không gọi LLM nữa
        if cache_idx < len(cached_tactics):
            tactic_only = cached_tactics[cache_idx]
            cache_idx += 1
            print("\n--- Using cached Lean tactics from solve.txt ---")
            print(tactic_only)
        else:
            # GỌI API THỰC TẾ Ở ĐÂY (Nên để temperature=0.0 cho Toán)
            print("Đang chờ LLM trả lời...")
            print(prompt)
            print("------------------------------------------")
            try:
                solution_raw = generate_reply(prompt, max_new_tokens=4096, temperature=0.6, top_p=0.95)
            except Exception as e:
                print(f"Lỗi API: {e}")
                solution_raw = "sorry"  # Fail-safe, trả lại sorry nếu API sập

            print("\nLLM Output (raw):")
            print(solution_raw)

            # Chỉ lấy Lean tactics, bỏ phần giải thích/markdown
            tactic_only = extract_lean_tactic(solution_raw)
            print("\n--- Extracted Lean tactics ---")
            print(tactic_only)

        solutions_dict[sg["line"]] = tactic_only

    # 4. Ghép code
    print("\n==========================================")
    print("Đang tiến hành ghép code (Merge)...")
    final_code = merge_llm_solutions(skeleton_code, solutions_dict)
    
    # 5. Lưu ra file
    out_file = "final_proof.lean"
    with open(out_file, "w", encoding="utf-8") as f:
        f.write(final_code)
        
    print(f"Thành công! File hoàn chỉnh đã được lưu tại: {out_file}")
    print("Cậu hãy dùng Lean REPL để Verify file này nhé!")

if __name__ == "__main__":
    main()