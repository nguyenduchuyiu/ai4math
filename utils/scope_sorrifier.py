"""
The Ultimate Hybrid Auto-Sorrifier (AST + Classification)
Dựa trên thuật toán phân loại Scope của Nguyễn Đức Huy kết hợp Lean 4 AST Coordinates.
"""

import subprocess
import json
import re
import sys
import os
from tqdm import tqdm

# Cậu sửa lại biến này cho khớp với thư mục của cậu nhé
REPL_DIR = "/workspace/npthai/APOLLO/repl" 

class HybridSorrifier:
    def __init__(self, file_path: str, max_cycles: int = 15):
        self.file_path = os.path.abspath(file_path)
        self.max_cycles = max_cycles

    def get_lean_errors(self):
        """Phân loại lỗi từ Lean thành 2 rổ: Fatal (Sai logic) và Unsolved (Chưa xong)."""
        res = subprocess.run(
            ["lake", "env", "lean", self.file_path],
            capture_output=True, text=True, cwd=REPL_DIR
        )
        
        output = res.stdout + "\n" + res.stderr
        fatal_errors = []
        unsolved_errors = []
        
        current_error_line = None
        current_error_msg = ""
        
        # Parse từng dòng log của Lean
        for line in output.splitlines():
            match = re.match(r'^.*?:(\d+):\d+:\s*error:\s*(.*)', line)
            if match:
                # Lưu lỗi trước đó vào rổ
                if current_error_line is not None:
                    if "unsolved goals" in current_error_msg:
                        unsolved_errors.append(current_error_line)
                    else:
                        fatal_errors.append(current_error_line)
                        
                current_error_line = int(match.group(1))
                current_error_msg = match.group(2)
            elif current_error_line is not None:
                current_error_msg += " " + line
                
        # Nhét lỗi cuối cùng vào rổ
        if current_error_line is not None:
            if "unsolved goals" in current_error_msg:
                unsolved_errors.append(current_error_line)
            else:
                fatal_errors.append(current_error_line)
                
        # Sắp xếp từ trên xuống dưới
        return sorted(fatal_errors), sorted(unsolved_errors)

    def _line_to_byte_offset(self, target_line: int) -> int:
        """Đổi dòng sang RAW BYTES (né lỗi ký tự Toán học ℝ, ∀)."""
        with open(self.file_path, "rb") as f:
            raw_bytes = f.read()
        lines = raw_bytes.split(b"\n")
        offset = 0
        for i in range(min(target_line - 1, len(lines))):
            offset += len(lines[i]) + 1 
        
        # Tịnh tiến qua khoảng trắng
        if target_line - 1 < len(lines):
            line_bytes = lines[target_line - 1]
            offset += len(line_bytes) - len(line_bytes.lstrip(b" \t"))
        return offset

    def _get_ast_blocks(self) -> list[dict]:
        res = subprocess.run(
            ["lake", "env", "lean", "--run", "dump_ast.lean", self.file_path],
            capture_output=True, text=True, cwd=REPL_DIR
        )
        blocks = []
        for line in res.stdout.splitlines():
            if line.strip().startswith("{"):
                try: blocks.append(json.loads(line))
                except: pass
        return blocks

    def fix_fatal_error(self, error_line: int) -> bool:
        """Chiến thuật 1: Lỗi Sai Logic -> Cắt bỏ cục ruột và thay bằng sorry."""
        error_byte = self._line_to_byte_offset(error_line)
        blocks = self._get_ast_blocks()
        
        # VÙNG CẤM: Tuyệt đối không cắt rụng đầu các lệnh khai báo!
        target_prefixes = ["lean.parser.tactic", "lean.parser.term.bytactic"]
        forbidden_keywords = ["tactichave", "tacticcases", "tacticmatch", "tacticlet", "decl", "command"]
        
        valid_blocks = [
            b for b in blocks 
            if b["start_byte"] <= error_byte <= b["end_byte"]
            and any(p in b["kind"].lower() for p in target_prefixes)
            and not any(f in b["kind"].lower() for f in forbidden_keywords)
        ]
        
        if not valid_blocks:
            # Fallback nếu bó tay
            valid_blocks = [b for b in blocks if b["start_byte"] <= error_byte <= b["end_byte"] and "command" not in b["kind"].lower()]
            if not valid_blocks: return False

        # Lấy node nhỏ nhất (cục ruột)
        target = min(valid_blocks, key=lambda x: x["end_byte"] - x["start_byte"])
        start_b, end_b = target["start_byte"], target["end_byte"]
        
        with open(self.file_path, "rb") as f:
            raw_bytes = f.read()
            
        if "sorry" in target["kind"].lower():
            tqdm.write(f"🧹 Xóa rác [sorry] byte {start_b}..{end_b}")
            repaired = raw_bytes[:start_b] + raw_bytes[end_b:]
        else:
            tqdm.write(f"🔪 Phẫu thuật Fatal [{target['kind']}] byte {start_b}..{end_b}")
            repaired = raw_bytes[:start_b] + b"sorry\n" + raw_bytes[end_b:]
            
        with open(self.file_path, "wb") as f: f.write(repaired)
        return True

    def fix_unsolved_goal(self, error_line: int) -> bool:
        """Chiến thuật 2: Chưa chứng minh xong -> Chèn sorry vào cuối block."""
        error_byte = self._line_to_byte_offset(error_line)
        blocks = self._get_ast_blocks()
        
        enclosing = [b for b in blocks if b["start_byte"] <= error_byte <= b["end_byte"]]
        if not enclosing: return False
        
        # Tìm block bọc bên ngoài (tacticSeq hoặc byTactic) để đóng nắp
        seq_blocks = [b for b in enclosing if "seq" in b["kind"].lower() or "bytactic" in b["kind"].lower()]
        target = min(seq_blocks, key=lambda x: x["end_byte"] - x["start_byte"]) if seq_blocks else min(enclosing, key=lambda x: x["end_byte"] - x["start_byte"])
        
        end_b = target["end_byte"]
        tqdm.write(f"🩹 Đóng nắp Unsolved [{target['kind']}] tại byte {end_b}")
        
        with open(self.file_path, "rb") as f:
            raw_bytes = f.read()
            
        repaired = raw_bytes[:end_b] + b"\nsorry\n" + raw_bytes[end_b:]
        
        with open(self.file_path, "wb") as f: f.write(repaired)
        return True

    def run(self):
        tqdm.write(f"🚀 Khởi động Hybrid AST-Sorrifier cho {self.file_path}")
        
        with tqdm(total=self.max_cycles, desc="Tiến trình", unit="vòng") as pbar:
            for _ in range(self.max_cycles):
                fatal_errs, unsolved_errs = self.get_lean_errors()
                
                if not fatal_errs and not unsolved_errs:
                    tqdm.write("✅ XONG! File đã xanh lè (Well-typed).")
                    break
                    
                # Ưu tiên xử lý Fatal Error (vỡ logic) trước, Unsolved xử lý sau
                if fatal_errs:
                    err_line = fatal_errs[0]
                    pbar.set_postfix_str(f"Sửa Fatal dòng {err_line}")
                    success = self.fix_fatal_error(err_line)
                else:
                    err_line = unsolved_errs[0]
                    pbar.set_postfix_str(f"Sửa Unsolved dòng {err_line}")
                    success = self.fix_unsolved_goal(err_line)
                    
                if not success:
                    tqdm.write(f"🛑 Dừng: Bác sĩ bó tay ở dòng {err_line}.")
                    break
                    
                pbar.update(1)

if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Sử dụng: python auto_sorrifier.py <file.lean>")
        sys.exit(1)
    
    bot = HybridSorrifier(sys.argv[1])
    bot.run()