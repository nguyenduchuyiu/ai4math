import subprocess
import json
import os

REPL_DIR = "/home/huy/Project/formal_proof/repl"
FILE_PATH = "/home/huy/Project/formal_proof/broken_proof.lean"

def get_ast_nodes(file_path: str):
    res = subprocess.run(["lake", "env", "lean", "--run", "dump_ast.lean", file_path],
                         capture_output=True, text=True, cwd=REPL_DIR)
    nodes = []
    for line in res.stdout.splitlines():
        if line.strip().startswith("{"):
            try: nodes.append(json.loads(line))
            except: pass
    return nodes

def extract_leaf_tactics_from_ast(file_path: str):
    """
    Trả về DANH SÁCH NODE tactic lá (dict có start_byte, end_byte, kind, ...)
    thay vì trả về string. ast_sorrifier sẽ tự dùng các byte-range này để
    ghi đè 'sorry' chính xác.
    """
    nodes = get_ast_nodes(file_path)
    if not nodes:
        return []

    # 1. Tìm vỏ bọc ngoài cùng của bài giải
    seq_nodes = [n for n in nodes if "bytactic" in n["kind"].lower() or "tacticseq" in n["kind"].lower()]
    if not seq_nodes: return []
    outer_seq = max(seq_nodes, key=lambda x: x["end_byte"] - x["start_byte"])

    # 2. Lấy mọi node có chứa chữ 'tactic' để không bỏ sót lệnh từ thư viện ngoài (Mathlib, v.v.)
    ignored_kinds = {
        "lean.parser.tactic.tacticseq", 
        "lean.parser.tactic.tacticseq1indented",
        "lean.parser.term.bytactic" 
    }

    tactic_nodes = [
        n for n in nodes 
        if "tactic" in n["kind"].lower() 
        and n["kind"].lower() not in ignored_kinds
        # Chỉ lấy các node nằm trong phạm vi của bài giải
        and n["start_byte"] >= outer_seq["start_byte"]
        and n["end_byte"] <= outer_seq["end_byte"]
    ]

    from tqdm import tqdm

    # 3. THUẬT TOÁN TÌM NODE LÁ (LEAF NODES) - kèm tiến trình tqdm cho từng node
    leaf_tactics = []
    for i, node_a in enumerate(tqdm(tactic_nodes, desc="Tìm tactic leaf", unit="node")):
        is_leaf = True
        len_a = node_a["end_byte"] - node_a["start_byte"]
        
        for j, node_b in enumerate(tactic_nodes):
            if i == j: continue
            len_b = node_b["end_byte"] - node_b["start_byte"]
            
            # Nếu node_b nằm hoàn toàn lọt thỏm bên trong node_a => node_a KHÔNG PHẢI là lá
            if node_b["start_byte"] >= node_a["start_byte"] and node_b["end_byte"] <= node_a["end_byte"]:
                # Kích thước b nhỏ hơn a -> a chứa b
                if len_b < len_a:
                    is_leaf = False
                    break
                # Xử lý trường hợp trùng lặp chính xác (cùng start, cùng end): chỉ giữ lại 1 node
                elif len_b == len_a and j > i:
                    is_leaf = False
                    break
                    
        if is_leaf:
            leaf_tactics.append(node_a)

    # 4. Sắp xếp lại các lá từ trên xuống dưới theo thứ tự xuất hiện trong file
    leaf_tactics.sort(key=lambda x: x["start_byte"])
    return leaf_tactics


def get_leaf_tactic_texts(file_path: str):
    """
    Helper dùng riêng cho CLI: cắt chuỗi tactic từ các leaf node để in preview.
    """
    from tqdm import tqdm

    leaf_tactics = extract_leaf_tactics_from_ast(file_path)
    if not leaf_tactics:
        return []

    with open(file_path, "rb") as f:
        raw_bytes = f.read()

    results = []
    for node in tqdm(leaf_tactics, desc="Cắt chuỗi tactic", unit="leaf"):
        tac_bytes = raw_bytes[node["start_byte"]:node["end_byte"]]
        results.append(tac_bytes.decode("utf-8"))

    return results

if __name__ == "__main__":
    print("🔍 Đang quét Cây Cú Pháp (AST) để băm Tactic Leaf...")
    tactics = get_leaf_tactic_texts(FILE_PATH)
    
    print(f"✅ Đã băm thành công {len(tactics)} lệnh Tactic Leaf:")
    for i, tac in enumerate(tactics, 1):
        # In ra dòng đầu tiên của mỗi Tactic để review cho gọn
        tac_preview = tac.splitlines()[0] + (" [...]" if "\n" in tac else "")
        print(f"  {i}. {tac_preview}")