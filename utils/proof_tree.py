class ProofTree:
    def __init__(self, code: str):
        self.code = code
        self.tree = []
        self._parse()

    def _parse(self):
        """Xây dựng cây AST dựa trên thụt lề (Indentation)."""
        lines = self.code.splitlines()
        root = {"indent": -1, "text": "<ROOT>", "children": [], "line": 0}
        stack = [root]
        
        for idx, line in enumerate(lines, start=1):
            if not line.strip():
                continue
            
            indent = len(line) - len(line.lstrip(" "))
            node = {"indent": indent, "text": line, "children": [], "line": idx}
            
            # Xử lý các node anh em / cha con dựa trên thụt lề
            while stack and indent <= stack[-1]["indent"]:
                stack.pop()
                
            stack[-1]["children"].append(node)
            stack.append(node)
            
        self.tree = root["children"]
        self._fix_inline_have(self.tree)

    def _fix_inline_have(self, nodes):
        """Tách 'have h : X := by Y' thành node cha (have) và node con (Y)."""
        for node in nodes:
            txt = node["text"]
            if "have" in txt and " := by" in txt and node["children"]:
                prefix, sep, after = txt.partition(" := by")
                extra_text = after.strip()
                if extra_text:
                    node["text"] = prefix + sep
                    new_child = {
                        "indent": node["children"][0]["indent"],
                        "text": " " * node["children"][0]["indent"] + extra_text,
                        "children": [],
                        "line": node["line"] # Kế thừa line để dễ track
                    }
                    node["children"].insert(0, new_child)
            if node["children"]:
                self._fix_inline_have(node["children"])

    def get_node_by_line(self, line_num: int, nodes=None) -> dict:
        """Tìm node tương ứng với số dòng báo lỗi của Lean."""
        nodes = nodes if nodes is not None else self.tree
        for node in nodes:
            if node.get("line") == line_num:
                return node
            result = self.get_node_by_line(line_num, node["children"])
            if result:
                return result
        return None

    def replace_node(self, line_num: int, new_lines: list[str], nodes=None) -> bool:
        """Thay thế node `sorry` bằng danh sách các tactic LLM sinh ra."""
        nodes = nodes if nodes is not None else self.tree
        for i, node in enumerate(nodes):
            if node.get("line") == line_num:
                # Tính toán thụt lề chuẩn từ node cũ
                base_indent = node["indent"]
                new_nodes = []
                for j, text in enumerate(new_lines):
                    # Ép thụt lề chuẩn cho code của LLM
                    clean_text = text.lstrip()
                    new_nodes.append({
                        "indent": base_indent,
                        "text": (" " * base_indent) + clean_text,
                        "children": [],
                        "line": line_num + j * 0.1 # Trick nhỏ để giữ thứ tự
                    })
                # Thay thế 1 node bằng nhiều nodes mới
                nodes[i:i+1] = new_nodes
                return True
            if self.replace_node(line_num, new_lines, node["children"]):
                return True
        return False

    def to_string(self, nodes=None) -> str:
        """Xuất ngược cây AST thành file Lean 4."""
        nodes = nodes if nodes is not None else self.tree
        code_str = []
        for node in nodes:
            code_str.append(node["text"])
            if node["children"]:
                code_str.append(self.to_string(node["children"]))
        return "\n".join(code_str)