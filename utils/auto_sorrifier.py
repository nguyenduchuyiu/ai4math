"""
AST-Based Automated Proof Patcher for Lean 4
--------------------------------------------
This module automates the process of fixing broken Lean 4 proofs by replacing 
faulty tactics with the `sorry` axiom. 

Architecture:
1. AST-Guided Truncation: Uses Lean's AST to precisely locate tactic boundaries.
2. Indentation Heuristics: Infers structural hierarchy where AST lacks context (e.g., closing scopes).
3. Oscillation Fallback: Detects infinite correction loops caused by Lean's syntax 
   intolerance and resets the parent block to prevent halting.
"""

import subprocess
import json
import re
import sys
import os
import tempfile
from typing import Tuple, List, Dict, Optional
from tqdm import tqdm

# Constants
REPL_DIR = "/home/huy/Project/formal_proof/repl"
BLOCK_STARTERS = (
    "have", "·", ".", "cases ", "cases' ", "induction ", 
    "induction' ", "rintro ", "intro ", "calc", "match", 
    "lemma", "theorem", "def"
)

class AutoSorrifier:
    def __init__(self, code: str, max_cycles: int = 20, log_path: Optional[str] = None):
        self.current_content = code
        self.max_cycles = max_cycles
        self.log_path = log_path
        self.temp_file_path = ""
        self._last_action_msg = ""

    def fix_code(self) -> str:
        """
        Main execution loop to iteratively fix Lean 4 errors.
        Tracks previous program states to prevent oscillation, manages
        temp file resources, and coordinates progressive code repair.
        """
        tqdm.write("Starting Automated Proof Patcher (In-Memory I/O)")
        
        # Track previous file states to detect infinite loops (oscillation)
        seen_states = set()
        
        # Initialize an invisible temporary file for Lean compiler
        with tempfile.NamedTemporaryFile(mode="w", suffix=".lean", dir=REPL_DIR, delete=False, encoding="utf-8") as temp_file:
            self.temp_file_path = temp_file.name

        try:
            self._log_state("Initial State")
            
            with tqdm(total=self.max_cycles, desc="Processing", unit="cycle") as pbar:
                for _ in range(self.max_cycles):
                    self._write_to_temp_file()
                    
                    fatal_errors, unsolved_goals = self._get_lean_errors()
                    
                    # Exit condition: Compilation is fully successful
                    if not fatal_errors and not unsolved_goals:
                        tqdm.write("\nSUCCESS: File is fully compiled with sorries.")
                        return self.current_content
                        
                    # Prioritize fatal syntax/type errors over unsolved goals
                    is_fatal = bool(fatal_errors)
                    err_line, err_msg = fatal_errors[0] if is_fatal else unsolved_goals[0]

                    # Infinite loop detection fallback (oscillation resolution)
                    if self.current_content in seen_states:
                        tqdm.write(f"\nOscillation detected at line {err_line}. Triggering Parent Block Reset...")
                        self._resolve_infinite_loop(err_line)
                        self._log_state("Fallback: Oscillation Resolution")
                        pbar.update(1)
                        continue 
                        
                    seen_states.add(self.current_content)
                    pbar.set_postfix_str(f"{'Fatal' if is_fatal else 'Unsolved'} @ L{err_line}")
                        
                    # Apply standard AST-based fix
                    success = self._apply_normal_fix(err_line, is_fatal, err_msg)
                    if not success:
                        tqdm.write(f"\nHALTED: Unrecoverable error at line {err_line}.")
                        break
                        
                    self._log_state(getattr(self, "_last_action_msg", "Post-Fix State"))
                    pbar.update(1)
                    
        finally:
            # Cleanup temporary file to prevent storage leaks
            if os.path.exists(self.temp_file_path):
                os.remove(self.temp_file_path)

        return self.current_content

    # ==========================================
    # CORE FIXING LOGIC
    # ==========================================

    def _resolve_infinite_loop(self, err_line: int):
        """
        Fallback resolution for correction oscillations.
        If error correction oscillates, this method attempts to resolve by 
        replacing the parent block with `sorry` and removing more deeply indented code
        belonging to that block.
        """
        lines = self.current_content.splitlines()
        
        # 1. Search backward for nearest parent block by string match
        boss_idx = -1
        for i in range(err_line - 1, -1, -1):
            line_str = lines[i].strip()
            if any(line_str.startswith(kw) for kw in ["have ", "lemma ", "theorem ", "def ", "·", "cases ", "match "]):
                boss_idx = i
                break
        
        if boss_idx != -1:
            boss_line = lines[boss_idx]
            boss_indent = len(boss_line) - len(boss_line.lstrip())
            
            # 2. Replace parent block body with sorry, retain declaration
            if ":=" in boss_line:
                lines[boss_idx] = boss_line.split(":=")[0] + ":= by sorry"
            elif boss_line.strip().startswith("·"):
                lines[boss_idx] = " " * boss_indent + "· sorry"
            elif "=>" in boss_line:
                lines[boss_idx] = boss_line.split("=>")[0] + "=> sorry"
            
            tqdm.write(f"Reset parent block at line {boss_idx + 1}")
            
            # 3. Remove all child lines (greater indent) following parent
            i = boss_idx + 1
            while i < len(lines):
                if not lines[i].strip():
                    lines[i] = ""
                    i += 1
                    continue
                curr_indent = len(lines[i]) - len(lines[i].lstrip())
                if curr_indent > boss_indent:
                    lines[i] = ""
                    i += 1
                else:
                    break
        else:
            # If parent block is not found, simply remove the problematic line
            tqdm.write("Parent block not found, deleting problematic line.")
            lines[err_line - 1] = ""
            
        self.current_content = self._clean_redundant_sorries(lines)

    def _apply_normal_fix(self, error_line: int, is_fatal: bool, err_msg: str) -> bool:
        """
        Applies standard correction based on error type:
        - Fatal (Syntax/Type): Replaces the problematic leaf tactic with `sorry`.
        - Unsolved Goal: Appends `sorry` to close the current scope.
        """
        blocks = self._get_ast_lines()
        enclosing = [b for b in blocks if b["start_line"] <= error_line <= b["end_line"]]
        lines = self.current_content.splitlines()

        def emergency_fallback():
            """
            Failsafe: If AST cannot parse the syntax error,
            perform a basic single-line replacement with `sorry`
            at the error line.
            """
            msg = f"AST parsing failed at L{error_line}. Applying basic single-line replacement."
            tqdm.write(msg)
            self._last_action_msg = msg
            indent = len(lines[error_line - 1]) - len(lines[error_line - 1].lstrip())
            lines[error_line - 1] = " " * indent + "sorry"
            self.current_content = "\n".join(lines) + "\n"
            return True

        if is_fatal:
            valid_nodes = [b for b in enclosing if "tactic" in b["kind"].lower() or "seq" in b["kind"].lower()]
            if not valid_nodes: return emergency_fallback()
            
            # Identify the narrowest scope (leaf node) to preserve surrounding logic
            target = min(valid_nodes, key=lambda x: x["end_line"] - x["start_line"])
            L_start, L_end = target["start_line"], target["end_line"]
            start_line_str = lines[L_start - 1]
            new_lines = lines[:L_start - 1]
            
            is_orphan_error = "no goals" in err_msg.lower() or "goals accomplished" in err_msg.lower()
            
            if is_orphan_error:
                # Remove tactic that is operating on an already closed goal
                self._last_action_msg = f"Removed orphaned tactic [{target['kind']}] L{L_start}..L{L_end}"
                indent = len(start_line_str) - len(start_line_str.lstrip())
                new_lines.append(" " * indent + "sorry")
                new_lines.extend(lines[L_end:])
            elif self._is_block_starter(start_line_str) and ":=" in start_line_str:
                # Truncate declaration body
                self._last_action_msg = f"Hollowed out block [{target['kind']}] starting at L{L_start}"
                clean_header = start_line_str.split(":=")[0] + ":= by sorry"
                new_lines.append(clean_header)
                new_lines.extend(lines[L_end:])
            else:
                # Replace standard leaf tactic
                self._last_action_msg = f"Replaced leaf tactic [{target['kind']}] L{L_start}..L{L_end}"
                indent = len(start_line_str) - len(start_line_str.lstrip())
                new_lines.append(" " * indent + "sorry")
                new_lines.extend(lines[L_end:])
                
            tqdm.write(self._last_action_msg)
                
        else: # Unsolved Goal Handling
            scopes = ["declaration", "tactichave", "tacticcases", "tacticmatch", "tacticlet"]
            valid_nodes = [b for b in enclosing if any(s in b["kind"].lower() for s in scopes)]
            if not valid_nodes:
                valid_nodes = [b for b in enclosing if "seq" in b["kind"].lower() or "bytactic" in b["kind"].lower()]
                if not valid_nodes: return emergency_fallback()
                # Use the largest block to ensure we close the outermost scope
                target = max(valid_nodes, key=lambda x: x["end_line"] - x["start_line"])
            else:
                target = min(valid_nodes, key=lambda x: x["end_line"] - x["start_line"])

            L_start, L_end = target["start_line"], target["end_line"]
            
            # Find the indentation of the first executable child tactic within the block
            indent = 0
            for i in range(L_start, L_end):
                line = lines[i]
                if line.strip() and not line.strip().startswith("--"):
                    indent = len(line) - len(line.lstrip())
                    break

            self._last_action_msg = f"Closed scope [{target['kind']}] at L{L_end} (Indent: {indent})"
            tqdm.write(self._last_action_msg)
            
            new_lines = lines[:L_end]
            new_lines.append(" " * indent + "sorry")
            new_lines.extend(lines[L_end:])

        self.current_content = self._clean_redundant_sorries(new_lines)
        return True

    def _call_lean_tool(self, tool_args: List[str], input_str: Optional[str] = None) -> str:
        """
        Động cơ lõi để gọi các Lean Binary (repl, dump_ast).
        Xử lý TempFile và thu hồi RAM ngay lập tức.
        """
        try:
            with tempfile.TemporaryFile(mode='w+', encoding='utf-8') as temp_in:
                if input_str:
                    temp_in.write(input_str + "\r\n\r\n")
                    temp_in.seek(0)
                
                res = subprocess.run(
                    ["lake", "exe"] + tool_args,
                    stdin=temp_in if input_str else None,
                    capture_output=True,
                    text=True,
                    cwd=REPL_DIR,
                    timeout=60
                )
                return res.stdout
        except Exception as e:
            print(f"  [!] Lean Call Error ({tool_args[0]}): {e}")
            return ""

    def _get_lean_errors(self) -> Tuple[List[Tuple[int, str]], List[Tuple[int, str]]]:
        """Dùng REPL để check lỗi logic"""
        req = json.dumps({"cmd": self.current_content})
        import time
        start_time = time.time()
        output = self._call_lean_tool(["repl"], input_str=req)
        elapsed_time = time.time() - start_time
        print(f"[REPL] lake exe repl executed in {elapsed_time:.4f} seconds")
        fatal_errors, unsolved_goals = [], []
        # Dùng raw_decode để bắt Multi-line JSON như DeepSeek
        decoder = json.JSONDecoder()
        idx = 0
        while idx < len(output):
            idx = output.find('{', idx)
            if idx == -1: break
            try:
                data, chunk_len = decoder.raw_decode(output[idx:])
                if "messages" in data:
                    for msg in data["messages"]:
                        ln, txt = msg.get("pos", {}).get("line", 1), msg.get("data", "")
                        if msg.get("severity") == "error":
                            if "unsolved goals" in txt: unsolved_goals.append((ln, txt))
                            else: fatal_errors.append((ln, txt))
                idx += chunk_len
            except: idx += 1
            
        return sorted(fatal_errors), sorted(unsolved_goals)

    def _get_ast_lines(self) -> List[Dict]:
        """Dùng dump_ast để soi cấu trúc cây"""
        # Lưu ý: dump_ast nhận file_path làm argument, không qua stdin
        import time
        start_time = time.time()
        output = self._call_lean_tool(["dump_ast", self.temp_file_path])
        elapsed_time = time.time() - start_time
        print(f"[AST] lake exe dump_ast executed in {elapsed_time:.4f} seconds")
        
        blocks = []
        raw_bytes = self.current_content.encode('utf-8')
        for line in output.splitlines():
            if line.strip().startswith("{"):
                try:
                    b = json.loads(line)
                    b["start_line"] = self._byte_to_line(raw_bytes, b["start_byte"])
                    b["end_line"] = self._byte_to_line(raw_bytes, b["end_byte"])
                    blocks.append(b)
                except: pass
        return blocks

    def _clean_redundant_sorries(self, lines: List[str]) -> str:
        """
        Removes duplicated `sorry` lines and empty lines generated during automated fixes.
        """
        cleaned = []
        for line in lines:
            if line == "":
                continue 
            if line.strip() == "sorry" and cleaned and cleaned[-1].strip() == "sorry":
                continue
            cleaned.append(line)
        return "\n".join(cleaned) + "\n"

    def _write_to_temp_file(self):
        """
        Writes the in-memory Lean code content to the temporary file for Lean to compile.
        """
        with open(self.temp_file_path, "w", encoding="utf-8") as tf:
            tf.write(self.current_content)

    def _log_state(self, step_name: str):
        """
        If log_path is set, append the current state of the code to the log file, 
        labeled with the step name.
        """
        if self.log_path:
            with open(self.log_path, "a", encoding="utf-8") as f:
                f.write(f"--- {step_name} ---\n\n")
                f.write(self.current_content)
                f.write("\n\n")

    @staticmethod
    def _byte_to_line(raw_bytes: bytes, byte_offset: int) -> int:
        """
        Converts zero-indexed byte offset to 1-indexed line number.
        """
        return raw_bytes[:byte_offset].count(b"\n") + 1

    @staticmethod
    def _is_block_starter(line: str) -> bool:
        """
        Heuristic to identify if a line starts a new logical block, such as
        'have', 'def', etc., possibly with assignment.
        """
        stripped = line.strip()
        if stripped.startswith("_") and ":=" in stripped: return True
        if not any(stripped.startswith(cmd) for cmd in BLOCK_STARTERS): return False
        if stripped.startswith("have") and ":=" not in stripped: return False
        return True


if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: python auto_sorrifier.py <path_to_lean_file>")
        sys.exit(1)
        
    target_path = sys.argv[1]
    with open(target_path, "r", encoding="utf-8") as f:
        source_code = f.read()
        
    patcher = AutoSorrifier(source_code)
    fixed_code = patcher.fix_code()
    
    if fixed_code:
        with open(target_path, "w", encoding="utf-8") as f:
            f.write(fixed_code)
        print("Done.")