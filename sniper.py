import re
from tqdm import tqdm

class Sorrifier:
    """
    Sorrifier v5.0 - Scope Sniper (Phân tách Nuke và Append)
    """
    def __init__(self, verifier, max_cycles=15, pbar=True):
        self.verifier = verifier
        self.max_cycles = max_cycles
        self.pbar = pbar
        self.block_starters = ("have", "·", ".", "cases ", "cases' ", "induction ", "induction' ", "rintro ", "intro ")

    def verify_and_fix(self, code: str) -> str:
        current_code = code
        sniped_owners = set()
        
        main_goal_line = 1
        for idx, line in enumerate(code.splitlines(), start=1):
            if ":= by" in line:
                main_goal_line = idx
                break

        if self.pbar:
            pbar = tqdm(desc="Scope Sniper Fixing", unit="cycle", total=self.max_cycles)

        for attempt in range(self.max_cycles):
            err_info = self.verifier(current_code)
            
            if err_info['pass']:
                if self.pbar: pbar.close()
                return current_code

            # Phân loại lỗi
            real_errors = []
            unsolved_errors = []
            for e in err_info['errors']:
                if "unsolved goals" in e['data']:
                    unsolved_errors.append(e)
                else:
                    real_errors.append(e)

            if real_errors:
                # 🚨 CÓ LỖI LOGIC/CÚ PHÁP -> MOI RUỘT (Nuke)
                real_errors.sort(key=lambda x: x['pos']['line'])
                err_line = real_errors[0]['pos']['line']
                
                new_code, owner_idx = self._snipe_error_nuke(current_code, err_line)

                if new_code == current_code or owner_idx in sniped_owners:
                    current_code = self._guillotine(current_code, err_line)
                else:
                    current_code = new_code
                    sniped_owners.add(owner_idx)
            else:
                # 🚨 CHỈ CÒN UNSOLVED GOALS -> ĐẮP THÊM SORRY ĐÚNG SCOPE (Append)
                unsolved_errors.sort(key=lambda x: x['pos']['line'])
                err_line = unsolved_errors[0]['pos']['line']

                new_code = self._snipe_error_append_sorry(current_code, err_line, main_goal_line)
                
                if new_code == current_code:
                    current_code = self._guillotine(current_code, err_line)
                else:
                    current_code = new_code

            if self.pbar: pbar.update(1)

        if self.pbar: pbar.close()
        return current_code

    def _get_main_indent(self, lines, main_goal_idx):
        """ Tính toán thụt lề gốc của định lý chính """
        for i in range(main_goal_idx + 1, len(lines)):
            line = lines[i]
            if line.strip() and not line.strip().startswith("--"):
                return len(line) - len(line.lstrip())
        return 2 # Fallback mặc định

    def _snipe_error_append_sorry(self, code: str, err_line_num: int, main_goal_line: int):
        """
        Xử lý 'unsolved goals': Không xóa code cũ, chỉ tìm đúng ranh giới Block và CHÈN thêm sorry.
        """
        lines = code.splitlines()
        
        # 1. Báo lỗi ở định lý chính -> Cần đóng Main Goal bằng cách thêm sorry ở cuối file với lề chuẩn
        if err_line_num <= main_goal_line:
            base_indent = self._get_main_indent(lines, main_goal_line - 1)
            lines.append(" " * base_indent + "sorry")
            return "\n".join(lines)

        # 2. Báo lỗi ở block con -> Tìm chủ block
        err_idx = err_line_num - 1
        if err_idx >= len(lines):
            return code
            
        err_line = lines[err_idx]
        err_indent = len(err_line) - len(err_line.lstrip())
        owner_idx = -1
        
        stripped_err = err_line.strip()
        is_starter = any(stripped_err.startswith(cmd) for cmd in self.block_starters)
        if stripped_err.startswith("have") and ":= by" not in stripped_err:
            is_starter = False
            
        if is_starter:
            owner_idx = err_idx
        else:
            for i in range(err_idx - 1, -1, -1):
                line = lines[i]
                if not line.strip() or line.strip().startswith("--"):
                    continue
                curr_indent = len(line) - len(line.lstrip())
                if curr_indent < err_indent:
                    stripped = line.strip()
                    is_up = any(stripped.startswith(cmd) for cmd in self.block_starters)
                    if stripped.startswith("have") and ":= by" not in stripped:
                        is_up = False
                    if is_up:
                        owner_idx = i
                        break

        if owner_idx == -1:
            base_indent = self._get_main_indent(lines, main_goal_line - 1)
            lines.append(" " * base_indent + "sorry")
            return "\n".join(lines)

        owner_line = lines[owner_idx]
        owner_indent = len(owner_line) - len(owner_line.lstrip())

        # Tìm dòng kết thúc của block con này
        end_idx = len(lines)
        for i in range(owner_idx + 1, len(lines)):
            line = lines[i]
            if not line.strip() or line.strip().startswith("--"):
                continue
            curr_indent = len(line) - len(line.lstrip())
            if curr_indent <= owner_indent:
                end_idx = i
                break

        # Tinh hoa ở đây: CHÈN sorry vào ĐÚNG ranh giới kết thúc của block con, thụt lề = chủ block + 2
        insert_indent = owner_indent + 2
        lines.insert(end_idx, " " * insert_indent + "sorry")
        return "\n".join(lines)

    def _snipe_error_nuke(self, code: str, error_line_num: int):
        """
        Xử lý 'real_errors': Moi ruột thay bằng sorry (Logic cũ)
        """
        lines = code.splitlines()
        err_idx = error_line_num - 1
        if err_idx >= len(lines):
            return code, -1
        
        err_line = lines[err_idx]
        err_indent = len(err_line) - len(err_line.lstrip())
        owner_idx = -1
        
        stripped_err = err_line.strip()
        is_starter = any(stripped_err.startswith(cmd) for cmd in self.block_starters)
        if stripped_err.startswith("have") and ":= by" not in stripped_err:
            is_starter = False
            
        if is_starter:
            owner_idx = err_idx
        else:
            for i in range(err_idx - 1, -1, -1):
                line = lines[i]
                if not line.strip() or line.strip().startswith("--"):
                    continue
                curr_indent = len(line) - len(line.lstrip())
                if curr_indent < err_indent:
                    stripped = line.strip()
                    is_up = any(stripped.startswith(cmd) for cmd in self.block_starters)
                    if stripped.startswith("have") and ":= by" not in stripped:
                        is_up = False
                    if is_up:
                        owner_idx = i
                        break
                        
        if owner_idx == -1:
            return code, -1

        owner_line = lines[owner_idx]
        owner_indent = len(owner_line) - len(owner_line.lstrip())

        end_idx = len(lines)
        for i in range(owner_idx + 1, len(lines)):
            line = lines[i]
            if not line.strip() or line.strip().startswith("--"):
                continue
            curr_indent = len(line) - len(line.lstrip())
            if curr_indent <= owner_indent:
                end_idx = i
                break

        new_lines = lines[:owner_idx]
        stripped_owner = owner_line.strip()

        if stripped_owner.startswith("have"):
            clean_owner = owner_line.split(":= by")[0] + ":= by"
            new_lines.append(clean_owner)
            new_lines.append(" " * (owner_indent + 2) + "sorry")
        elif stripped_owner.startswith("·") or stripped_owner.startswith("."):
            bullet_pos = owner_line.find(stripped_owner[0])
            clean_owner = owner_line[:bullet_pos + 1] 
            new_lines.append(clean_owner)
            new_lines.append(" " * (owner_indent + 2) + "sorry")
        else:
            new_lines.append(owner_line)
            new_lines.append(" " * (owner_indent + 2) + "sorry")

        new_lines.extend(lines[end_idx:])
        return "\n".join(new_lines), owner_idx

    def _guillotine(self, code: str, first_error_line: int) -> str:
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