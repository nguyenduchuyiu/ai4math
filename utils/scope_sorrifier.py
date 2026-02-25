import re
from typing import Tuple, List, Set, Dict, Any, Callable
from tqdm import tqdm

class Sorrifier:
    """
    Automated proof sorrifier that uses a scope-based error recovery strategy.
    
    It parses error messages from the Lean 4 compiler to dynamically locate 
    problematic tactics. Depending on the error type, it either truncates 
    the faulty tactic block and replaces it with `sorry` (for logical/syntax errors), 
    or appends `sorry` to properly close unfinished scopes (for 'unsolved goals').
    """
    
    def __init__(
        self, 
        verifier: Callable[[str], Dict[str, Any]], 
        max_cycles: int = 15, 
        pbar: bool = True
    ):
        self.verifier = verifier
        self.max_cycles = max_cycles
        self.pbar = pbar
        # Keywords that open a new logical scope/block in Lean 4
        self.block_starters = ("have", "·", ".", "cases ", "cases' ", "induction ", "induction' ", "rintro ", "intro ")

    def verify_and_fix(self, code: str) -> str:
        """
        Iteratively verifies and repairs the Lean 4 code until no fatal errors remain.
        """
        current_code = code
        modified_blocks: Set[int] = set()
        
        main_goal_line = 1
        for idx, line in enumerate(code.splitlines(), start=1):
            if ":= by" in line:
                main_goal_line = idx
                break

        progress_bar = tqdm(desc="Scope Sorrifier", unit="cycle", total=self.max_cycles) if self.pbar else None

        for _ in range(self.max_cycles):
            err_info = self.verifier(current_code)
            
            if err_info.get('pass', False):
                if progress_bar: progress_bar.close()
                return current_code

            # Categorize errors into structural/logic errors vs. incomplete proofs
            fatal_errors = []
            unsolved_errors = []
            for e in err_info.get('errors', []):
                if "unsolved goals" in e['data']:
                    unsolved_errors.append(e)
                else:
                    fatal_errors.append(e)

            # Safety: if verifier returned no classified errors, stop to avoid index errors
            if not fatal_errors and not unsolved_errors:
                print("No errors found in the code. Compile result:", err_info)
                if progress_bar: progress_bar.close()
                return current_code

            if fatal_errors:
                # Handle fatal errors by truncating the inner block
                fatal_errors.sort(key=lambda x: x['pos']['line'])
                err_line = fatal_errors[0]['pos']['line']
                
                new_code, owner_idx = self._replace_block_with_sorry(current_code, err_line)

                # Fallback to hard truncation if block replacement fails or loops
                if new_code == current_code or owner_idx in modified_blocks:
                    current_code = self._truncate_file(current_code, err_line)
                else:
                    current_code = new_code
                    modified_blocks.add(owner_idx)
            else:
                # Handle unfinished proofs by appending 'sorry' to the appropriate scope
                unsolved_errors.sort(key=lambda x: x['pos']['line'])
                err_line = unsolved_errors[0]['pos']['line']

                new_code = self._close_block_with_sorry(current_code, err_line, main_goal_line)
                
                if new_code == current_code:
                    current_code = self._truncate_file(current_code, err_line)
                else:
                    current_code = new_code

            if progress_bar: progress_bar.update(1)

        if progress_bar: progress_bar.close()
        return current_code

    # -------------------------------------------------------------------------
    # Core Scope Identification Helpers
    # -------------------------------------------------------------------------

    def _is_block_starter(self, line: str) -> bool:
        """Checks if a given line initializes a new tactic scope."""
        stripped = line.strip()
        if not any(stripped.startswith(cmd) for cmd in self.block_starters):
            return False
        # Special case: 'have' statements must contain ':= by' to be considered a tactic block
        if stripped.startswith("have") and ":= by" not in stripped:
            return False
        return True

    def _find_block_owner(self, lines: List[str], err_idx: int) -> int:
        """Scans upwards from the error line to find the parent block owner."""
        if err_idx >= len(lines):
            return -1
            
        err_indent = len(lines[err_idx]) - len(lines[err_idx].lstrip())
        
        # Check if the error is exactly on the block starter line
        if self._is_block_starter(lines[err_idx]):
            return err_idx
            
        # Scan upwards for a parent with strictly smaller indentation
        for i in range(err_idx - 1, -1, -1):
            line = lines[i]
            if not line.strip() or line.strip().startswith("--"):
                continue
            curr_indent = len(line) - len(line.lstrip())
            if curr_indent < err_indent and self._is_block_starter(line):
                return i
                
        return -1

    def _find_block_end(self, lines: List[str], owner_idx: int) -> int:
        """Scans downwards to find the boundary where the current block ends."""
        owner_indent = len(lines[owner_idx]) - len(lines[owner_idx].lstrip())
        for i in range(owner_idx + 1, len(lines)):
            line = lines[i]
            if not line.strip() or line.strip().startswith("--"):
                continue
            curr_indent = len(line) - len(line.lstrip())
            if curr_indent <= owner_indent:
                return i
        return len(lines)

    def _get_main_indent(self, lines: List[str], main_goal_idx: int) -> int:
        """Calculates the base indentation level for the main theorem proof."""
        for i in range(main_goal_idx + 1, len(lines)):
            line = lines[i]
            if line.strip() and not line.strip().startswith("--"):
                return len(line) - len(line.lstrip())
        return 2

    # -------------------------------------------------------------------------
    # Code Mutation Strategies
    # -------------------------------------------------------------------------

    def _replace_block_with_sorry(self, code: str, error_line_num: int) -> Tuple[str, int]:
        """
        Truncates the inner contents of a faulty block and replaces it with `sorry`.
        Returns the modified code and the line index of the modified block.
        """
        lines = code.splitlines()
        owner_idx = self._find_block_owner(lines, error_line_num - 1)
        
        if owner_idx == -1:
            return code, -1

        end_idx = self._find_block_end(lines, owner_idx)
        owner_line = lines[owner_idx]
        owner_indent = len(owner_line) - len(owner_line.lstrip())

        new_lines = lines[:owner_idx]
        stripped_owner = owner_line.strip()

        # Retain the block header but discard its faulty body
        if stripped_owner.startswith("have"):
            clean_owner = owner_line.split(":= by")[0] + ":= by"
            new_lines.append(clean_owner)
        elif stripped_owner.startswith("·") or stripped_owner.startswith("."):
            bullet_pos = owner_line.find(stripped_owner[0])
            clean_owner = owner_line[:bullet_pos + 1] 
            new_lines.append(clean_owner)
        else:
            new_lines.append(owner_line)

        # Inject sorry with appropriate indentation
        new_lines.append(" " * (owner_indent + 2) + "sorry")
        new_lines.extend(lines[end_idx:])
        
        return "\n".join(new_lines), owner_idx

    def _close_block_with_sorry(self, code: str, err_line_num: int, main_goal_line: int) -> str:
        """
        Appends `sorry` to properly close a block that lacks a concluding tactic.
        """
        lines = code.splitlines()
        
        # If the error points to the theorem declaration, close the main proof
        if err_line_num <= main_goal_line:
            base_indent = self._get_main_indent(lines, main_goal_line - 1)
            lines.append(" " * base_indent + "sorry")
            return "\n".join(lines)

        owner_idx = self._find_block_owner(lines, err_line_num - 1)
        if owner_idx == -1:
            base_indent = self._get_main_indent(lines, main_goal_line - 1)
            lines.append(" " * base_indent + "sorry")
            return "\n".join(lines)

        end_idx = self._find_block_end(lines, owner_idx)
        owner_indent = len(lines[owner_idx]) - len(lines[owner_idx].lstrip())

        insert_indent = owner_indent + 2
        lines.insert(end_idx, " " * insert_indent + "sorry")
        
        return "\n".join(lines)

    def _truncate_file(self, code: str, first_error_line: int) -> str:
        """
        Fallback hard truncation: removes all code from the error line downwards
        and safely closes the proof state.
        """
        lines = code.splitlines()
        err_idx = first_error_line - 1
        kept_lines = lines[:err_idx]

        if not kept_lines:
            indent = 2
        else:
            last_line = kept_lines[-1]
            indent_size = len(last_line) - len(last_line.lstrip())
            if last_line.strip().endswith(("by", "do", "with", ":")):
                indent_size += 2
            indent = indent_size

        kept_lines.append(" " * indent + "sorry")
        return "\n".join(kept_lines)