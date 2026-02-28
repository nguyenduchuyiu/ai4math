"""
The Ultimate AST-Line Hybrid Sorrifier
Lấy tọa độ Dòng từ AST -> Cắt và Đóng nắp bằng Heuristics chuẩn lề.
Tích hợp: Vi phẫu bảo tồn (Microsurgeon) + Thanos Snap (Dọn mồ côi).
"""

import subprocess
import json
import re
import sys
import os
from tqdm import tqdm

REPL_DIR = "/home/huy/Project/formal_proof/repl"

class UltimateHybridSorrifier:
    def __init__(self, file_path: str, max_cycles: int = 20):
        self.file_path = os.path.abspath(file_path)
        self.max_cycles = max_cycles
        self.block_starters = ("have", "·", ".", "cases ", "cases' ", "induction ", "induction' ", "rintro ", "intro ", "calc", "match", "lemma", "theorem", "def")

    def get_lean_errors(self):
        res = subprocess.run(["lake", "env", "lean", self.file_path], capture_output=True, text=True, cwd=REPL_DIR)
        output = res.stdout + "\n" + res.stderr
        fatal, unsolved = [], []
        curr_line, curr_msg = None, ""
        for line in output.splitlines():
            match = re.match(r'^.*?:(\d+):\d+:\s*error:\s*(.*)', line)
            if match:
                if curr_line:
                    if "unsolved goals" in curr_msg: unsolved.append((curr_line, curr_msg))
                    else: fatal.append((curr_line, curr_msg))
                curr_line = int(match.group(1))
                curr_msg = match.group(2)
            elif curr_line:
                curr_msg += " " + line
        if curr_line:
            if "unsolved goals" in curr_msg: unsolved.append((curr_line, curr_msg))
            else: fatal.append((curr_line, curr_msg))
        return sorted(fatal, key=lambda x: x[0]), sorted(unsolved, key=lambda x: x[0])

    def _byte_to_line(self, raw_bytes: bytes, byte_offset: int) -> int:
        return raw_bytes[:byte_offset].count(b"\n") + 1

    def _get_ast_lines(self) -> list[dict]:
        res = subprocess.run(["lake", "env", "lean", "--run", "dump_ast.lean", self.file_path], capture_output=True, text=True, cwd=REPL_DIR)
        blocks = []
        with open(self.file_path, "rb") as f: raw_bytes = f.read()
        for line in res.stdout.splitlines():
            if line.strip().startswith("{"):
                try:
                    b = json.loads(line)
                    b["start_line"] = self._byte_to_line(raw_bytes, b["start_byte"])
                    b["end_line"] = self._byte_to_line(raw_bytes, b["end_byte"])
                    blocks.append(b)
                except: pass
        return blocks

    def _is_block_starter(self, line: str) -> bool:
        stripped = line.strip()
        if not any(stripped.startswith(cmd) for cmd in self.block_starters): return False
        if stripped.startswith("have") and ":=" not in stripped: return False
        return True

    def fix_error(self, error_line: int, is_fatal: bool, err_msg: str = "") -> bool:
        blocks = self._get_ast_lines()
        enclosing = [b for b in blocks if b["start_line"] <= error_line <= b["end_line"]]
        
        with open(self.file_path, "r", encoding="utf-8") as f:
            lines = f.read().splitlines()

        # 🚑 CƠ CHẾ BẤT TỬ: Nếu AST nát bét (không có node hợp lệ), chém chay bằng text!
        def emergency_fallback():
            tqdm.write(f"🚑 AST vỡ tại dòng {error_line}! Tiến hành chém chay...")
            indent = len(lines[error_line - 1]) - len(lines[error_line - 1].lstrip())
            lines[error_line - 1] = " " * indent + "sorry"
            with open(self.file_path, "w", encoding="utf-8") as f:
                f.write("\n".join(lines) + "\n")
            return True

        if is_fatal:
            valid = [b for b in enclosing if "tactic" in b["kind"].lower() or "seq" in b["kind"].lower()]
            if not valid: return emergency_fallback()
            
            # [CHÂN LÝ VI PHẪU]: Bỏ ưu tiên seq/byTactic. Bắt buộc chọn Node nhỏ nhất.
            target = min(valid, key=lambda x: x["end_line"] - x["start_line"])

            L_start, L_end = target["start_line"], target["end_line"]
            start_line_str = lines[L_start - 1]
            new_lines = lines[:L_start - 1]
            
            # --- KIỂM TRA MỒ CÔI (ORPHAN) ---
            is_orphan = "no goals" in err_msg.lower() or "goals accomplished" in err_msg.lower()
            
            if is_orphan:
                # [ĐÒN THANOS SNAP]: Quét sạch anh em bên dưới cùng block
                indent = len(start_line_str) - len(start_line_str.lstrip())
                new_lines.append(" " * indent + "sorry")
                tqdm.write(f"🧹 Dọn rác mồ côi {target['kind']} từ dòng {L_start} đến {L_end}")
                new_lines.extend(lines[L_end:])
            elif self._is_block_starter(start_line_str) and ":=" in start_line_str:
                # Phẫu thuật bảo tồn
                clean_header = start_line_str.split(":=")[0] + ":= by sorry"
                new_lines.append(clean_header)
                tqdm.write(f"🔪 Moi ruột {target['kind']} trên dòng {L_start}")
                new_lines.extend(lines[L_end:])
            else:
                # Cắt đúng cái tactic lá nhỏ xíu
                indent = len(start_line_str) - len(start_line_str.lstrip())
                new_lines.append(" " * indent + "sorry")
                tqdm.write(f"🔪 Cắt phăng {target['kind']} dòng {L_start}..{L_end} (Lề: {indent})")
                new_lines.extend(lines[L_end:])
                
        else:
            scopes = ["declaration", "tactichave", "tacticcases", "tacticmatch", "tacticlet"]
            valid = [b for b in enclosing if any(s in b["kind"].lower() for s in scopes)]
            if not valid:
                valid = [b for b in enclosing if "seq" in b["kind"].lower() or "bytactic" in b["kind"].lower()]
                if not valid: return emergency_fallback()
                target = max(valid, key=lambda x: x["end_line"] - x["start_line"])
            else:
                target = min(valid, key=lambda x: x["end_line"] - x["start_line"])

            L_start = target["start_line"]
            L_end = target["end_line"]
            
            # [SỬA LỖI ĐÓNG NẮP]: Quét nội dung block để tìm lề chuẩn
            base_line = lines[L_start - 1]
            base_indent = len(base_line) - len(base_line.lstrip())
            indent = base_indent + 2  # Mặc định thụt vô 2 space
            
            for i in range(L_start, L_end):
                line = lines[i]
                if line.strip() and not line.strip().startswith("--"):
                    curr_indent = len(line) - len(line.lstrip())
                    if curr_indent > base_indent:
                        indent = curr_indent
                        break

            tqdm.write(f"🩹 Đóng nắp {target['kind']} tại dòng {L_end} (Lề: {indent})")
            new_lines = lines[:L_end]
            new_lines.append(" " * indent + "sorry")
            new_lines.extend(lines[L_end:])

        # Thuật toán dọn rác bất tử của Huy
        cleaned = []
        for line in new_lines:
            if line.strip() == "sorry" and cleaned and cleaned[-1].strip() == "sorry": continue
            cleaned.append(line)

        with open(self.file_path, "w", encoding="utf-8") as f: 
            f.write("\n".join(cleaned) + "\n")
        return True

    def run(self):
        tqdm.write(f"🚀 Khởi động Ultimate Hybrid Sorrifier cho {self.file_path}")
        
        # BỘ NHỚ CHỐNG PING-PONG LOOP
        seen_states = set()
        
        with tqdm(total=self.max_cycles, desc="Tiến trình", unit="vòng") as pbar:
            for _ in range(self.max_cycles):
                # Chụp hình file hiện tại
                with open(self.file_path, "r", encoding="utf-8") as f:
                    current_content = f.read()
                    
                fatal, unsolved = self.get_lean_errors()
                
                if not fatal and not unsolved:
                    tqdm.write("\n✅ XONG! File xanh lè hoàn hảo!")
                    break
                    
                if fatal:
                    err_line, err_msg = fatal[0]
                    is_fatal = True
                else:
                    err_line, err_msg = unsolved[0]
                    is_fatal = False

                # ⚔️ ĐOẢN KIẾM CHỐNG KẸT: Kích hoạt nếu file không đổi sau 1 thao tác
                if current_content in seen_states:
                    tqdm.write(f"\n⚠️ Bắt quả tang Ping-Pong Loop tại dòng {err_line}! Kích hoạt chém chay dứt điểm...")
                    lines = current_content.splitlines()
                    indent = len(lines[err_line - 1]) - len(lines[err_line - 1].lstrip())
                    lines[err_line - 1] = " " * indent + "sorry" # Đè thẳng sorry vào dòng gây kẹt
                    
                    # Dọn rác liền kề
                    cleaned = []
                    for line in lines:
                        if line.strip() == "sorry" and cleaned and cleaned[-1].strip() == "sorry": continue
                        cleaned.append(line)
                        
                    with open(self.file_path, "w", encoding="utf-8") as f:
                        f.write("\n".join(cleaned) + "\n")
                    pbar.update(1)
                    continue # Chuyển sang vòng sau luôn
                    
                # Ghi nhớ trạng thái file để đối chiếu vòng sau
                seen_states.add(current_content)

                if is_fatal:
                    pbar.set_postfix_str(f"Fatal {err_line}")
                else:
                    pbar.set_postfix_str(f"Unsolved {err_line}")
                    
                success = self.fix_error(err_line, is_fatal, err_msg)
                if not success:
                    tqdm.write(f"\n🛑 Dừng: Bác sĩ bó tay ở dòng {err_line}.")
                    break
                pbar.update(1)

if __name__ == "__main__":
    UltimateHybridSorrifier(sys.argv[1]).run()