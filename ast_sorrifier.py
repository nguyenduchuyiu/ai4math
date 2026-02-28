import os
import json
import subprocess
from tatics_extractor import extract_leaf_tactics_from_ast

# --- CẤU HÌNH ---
PROJECT_PATH = "/home/huy/Project/formal_proof/repl"
FILE_PATH = "/home/huy/Project/formal_proof/broken_proof.lean"

def get_lean_errors():
    """Lấy danh sách tọa độ lỗi từ Lean (trả về danh sách rỗng nếu không có lỗi)"""
    res = subprocess.run(
        ["lake", "env", "lean", "--json", FILE_PATH], 
        cwd=PROJECT_PATH, capture_output=True, text=True
    )
    full_output = res.stdout + "\n" + res.stderr
    errors = []

    for line in full_output.splitlines():
        line = line.strip()
        if not line.startswith("{"): continue
        try:
            msg = json.loads(line)
            if msg.get("severity") == "error" or msg.get("severity") == 2:
                pos = msg.get("pos", {})
                line_num = pos.get("line")
                col_num = pos.get("column")
                if line_num is not None and col_num is not None:
                    errors.append((line_num, col_num))
        except json.JSONDecodeError:
            continue
    return errors

def get_error_byte_indices(file_path, error_coords):
    with open(file_path, "rb") as f:
        raw_bytes = f.read()
    lines = raw_bytes.split(b'\n')
    byte_indices = []
    for line_num, col_num in error_coords:
        # Tính byte offset
        byte_offset = sum(len(l) + 1 for l in lines[:line_num - 1]) 
        byte_indices.append(byte_offset + col_num)
    return byte_indices

def sorrify_loop():
    print("🚀 Bắt đầu quá trình Sorrification (AST Loop)...")
    
    max_iters = 20 # Đề phòng lặp vô tận
    for i in range(max_iters):
        print(f"\n--- 🔄 Vòng lặp thứ {i + 1} ---")
        
        # 1. Tìm lỗi
        error_coords = get_lean_errors()
        if not error_coords:
            print("🎉 BINGOOO! File đã biên dịch trót lọt không còn 1 hạt sạn nào!")
            break
            
        print(f"⚠️ Phát hiện {len(error_coords)} lỗi từ Compiler.")
        error_byte_indices = get_error_byte_indices(FILE_PATH, error_coords)
        
        # 2. Xây lại cây AST (vì file vừa bị đổi byte ở vòng trước)
        leaf_nodes = extract_leaf_tactics_from_ast(FILE_PATH)
        
        # 3. Tìm các Tactic lá bị dính đạn
        bad_tactics = set()
        for err_idx in error_byte_indices:
            for node in leaf_nodes:
                if node["start_byte"] <= err_idx <= node["end_byte"]:
                    bad_tactics.add((node["start_byte"], node["end_byte"]))
                    break
        
        if not bad_tactics:
            print("❌ Bế tắc: Có lỗi nhưng không map được vào Tactic nào trong AST!")
            break
            
        # 4. Cắt gọt và chèn 'sorry' (sắp xếp ngược từ dưới lên để không làm lệch index)
        sorted_bad = sorted(list(bad_tactics), key=lambda x: x[0], reverse=True)
        
        with open(FILE_PATH, "rb") as f:
            final_bytes = bytearray(f.read())
            
        for start, end in sorted_bad:
            final_bytes[start:end] = b"sorry"
            
        with open(FILE_PATH, "wb") as f:
            f.write(final_bytes)
            
        print(f"✅ Đã dập xong {len(bad_tactics)} ngọn lửa. Đang biên dịch lại...")
        
    else:
        print("\n⚠️ Dừng lại do chạm giới hạn vòng lặp.")

if __name__ == "__main__":
    sorrify_loop()