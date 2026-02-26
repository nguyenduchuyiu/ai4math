import subprocess
import json
import re
import sys
import os
from tqdm import tqdm

REPL_DIR = "/workspace/npthai/APOLLO/repl"

class PureASTSorrifier:
    def __init__(self, file_path: str, max_cycles: int = 15):
        self.file_path = os.path.abspath(file_path)
        self.max_cycles = max_cycles

    def get_lean_errors(self):
        res = subprocess.run(["lake", "env", "lean", self.file_path], capture_output=True, text=True, cwd=REPL_DIR)
        output = res.stdout + "\n" + res.stderr
        fatal, unsolved = [], []
        curr_line, curr_msg = None, ""
        for line in output.splitlines():
            match = re.match(r'^.*?:(\d+):\d+:\s*error:\s*(.*)', line)
            if match:
                if curr_line:
                    if "unsolved goals" in curr_msg: unsolved.append(curr_line)
                    else: fatal.append(curr_line)
                curr_line = int(match.group(1))
                curr_msg = match.group(2)
            elif curr_line:
                curr_msg += " " + line
        if curr_line:
            if "unsolved goals" in curr_msg: unsolved.append(curr_line)
            else: fatal.append(curr_line)
        return sorted(fatal), sorted(unsolved)

    def _line_to_byte(self, target_line: int) -> int:
        with open(self.file_path, "rb") as f: raw_bytes = f.read()
        lines = raw_bytes.split(b"\n")
        offset = sum(len(lines[i]) + 1 for i in range(min(target_line - 1, len(lines))))
        if target_line - 1 < len(lines):
            line_bytes = lines[target_line - 1]
            offset += len(line_bytes) - len(line_bytes.lstrip(b" \t"))
        return offset

    def _get_full_ast(self) -> list[dict]:
        res = subprocess.run(["lake", "env", "lean", "--run", "dump_ast.lean", self.file_path], capture_output=True, text=True, cwd=REPL_DIR)
        blocks = []
        for line in res.stdout.splitlines():
            if line.strip().startswith("{"):
                try: blocks.append(json.loads(line))
                except: pass
        return blocks

    def fix_ast(self, error_line: int, is_fatal: bool) -> bool:
        err_byte = self._line_to_byte(error_line)
        all_nodes = self._get_full_ast()
        
        # Tìm CẤU TRÚC PHÂN CẤP bọc lấy điểm lỗi (từ nhỏ nhất đến lớn nhất)
        enclosing = [n for n in all_nodes if n["start_byte"] <= err_byte <= n["end_byte"]]
        chain = sorted(enclosing, key=lambda x: x["end_byte"] - x["start_byte"])
        
        if not chain:
            tqdm.write("⚠️ AST không parse được tọa độ này! Cú pháp có thể đang bị vỡ.")
            return False

        with open(self.file_path, "rb") as f: raw_bytes = f.read()

        if is_fatal:
            target = None
            for node in chain:
                kind = node["kind"].lower()
                if "declaration" in kind or "command" in kind: continue
                if "tactic" in kind or "seq" in kind:
                    target = node
                    break
            
            if not target: return False
                
            start_b, end_b = target["start_byte"], target["end_byte"]
            
            if "sorry" in target["kind"].lower():
                tqdm.write(f"🧹 Dọn rác [TacticSorry] byte {start_b}..{end_b}")
                repaired = raw_bytes[:start_b] + raw_bytes[end_b:]
            else:
                tqdm.write(f"🔪 Phẫu thuật Fatal [{target['kind']}] byte {start_b}..{end_b}")
                repaired = raw_bytes[:start_b] + b"sorry" + raw_bytes[end_b:]

        else:
            target = None
            # ƯU TIÊN 1: Tìm xem lỗi có nằm trong Tactic Scope nào không
            for node in chain:
                kind = node["kind"].lower()
                if any(k in kind for k in ["tacticseq", "bytactic", "tactichave", "tacticcases", "tacticmatch"]):
                    target = node
                    break
            
            # ƯU TIÊN 2: Nếu lỗi nằm ngay Đề bài (chữ ∏) -> Túm lấy node Declaration
            if not target:
                for node in chain:
                    kind = node["kind"].lower()
                    if "declaration" in kind or "command" in kind:
                        # Tuyệt đối không đóng nắp ở declSig vì nó chỉ là cái vỏ
                        if "declsig" in kind or "declid" in kind: continue
                        target = node
                        break
            
            # FALLBACK CUỐI CÙNG: Nhặt cái node to nhất có thể
            if not target: target = chain[-1]
                
            end_b = target["end_byte"]
            
            # Tự động đo lề cho đẹp
            line_start = raw_bytes.rfind(b"\n", 0, end_b) + 1
            line_bytes = raw_bytes[line_start:end_b]
            indent_count = len(line_bytes) - len(line_bytes.lstrip(b" \t"))
            if indent_count == 0: indent_count = 2 # Lề chuẩn cho bài toán
            
            tqdm.write(f"🩹 Đóng nắp Unsolved [{target['kind']}] tại byte {end_b} (Lề: {indent_count})")
            
            # Đảm bảo xuống dòng trước khi đắp sorry
            prefix = b"\n" if not raw_bytes[:end_b].endswith(b"\n") else b""
            repaired = raw_bytes[:end_b] + prefix + (b" " * indent_count) + b"sorry\n" + raw_bytes[end_b:]

        with open(self.file_path, "wb") as f: f.write(repaired)
        return True

    def run(self):
        tqdm.write(f"🚀 Khởi động Pure AST Sorrifier cho {self.file_path}")
        with tqdm(total=self.max_cycles, desc="Tiến trình", unit="vòng") as pbar:
            for _ in range(self.max_cycles):
                fatal, unsolved = self.get_lean_errors()
                if not fatal and not unsolved:
                    tqdm.write("\n✅ XONG! File xanh lè!")
                    break
                if fatal:
                    err_line = fatal[0]
                    pbar.set_postfix_str(f"Fatal {err_line}")
                    success = self.fix_ast(err_line, True)
                else:
                    err_line = unsolved[0]
                    pbar.set_postfix_str(f"Unsolved {err_line}")
                    success = self.fix_ast(err_line, False)
                if not success:
                    tqdm.write(f"\n🛑 Dừng: Bác sĩ bó tay ở dòng {err_line}.")
                    break
                pbar.update(1)

if __name__ == "__main__":
    PureASTSorrifier(sys.argv[1]).run()