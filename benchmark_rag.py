import argparse
import json
from typing import List, Dict, Any

import faiss
import numpy as np
import torch
from sklearn.preprocessing import normalize
from transformers import AutoModelForTextEncoding, AutoTokenizer


class LeanDojoRetriever:
    def __init__(self, model_name: str):
        self.device = torch.device("cuda" if torch.cuda.is_available() else "cpu")
        self.tokenizer = AutoTokenizer.from_pretrained(model_name)
        self.model = AutoModelForTextEncoding.from_pretrained(model_name).to(self.device)
        self.model.eval()

    @torch.no_grad()
    def encode(self, texts, batch_size: int = 4, max_length: int = 512) -> np.ndarray:
        all_embeddings = []
        for i in range(0, len(texts), batch_size):
            batch = texts[i : i + batch_size]
            tokenized = self.tokenizer(
                batch,
                padding=True,
                truncation=True,
                max_length=max_length,
                return_tensors="pt",
            ).to(self.device)
            outputs = self.model(**tokenized)
            hidden_state = outputs.last_hidden_state
            lens = tokenized.attention_mask.sum(dim=1)
            mask = tokenized.attention_mask.unsqueeze(2)
            features = (hidden_state * mask).sum(dim=1) / lens.unsqueeze(1)
            all_embeddings.append(features.detach().cpu())
            if self.device.type == "cuda":
                torch.cuda.empty_cache()
        return torch.cat(all_embeddings, dim=0).numpy()

def extract_test_samples(raw_data: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    """Extract (query, targets) từ LeanDojo random/test.json."""
    test_samples = []

    for theorem in raw_data:
        file_path = theorem.get("file_path", "")

        for step in theorem.get("traced_tactics", []):
            query_state = step.get("state_before", "")
            if not query_state:
                continue

            annotated = step.get("annotated_tactic", [])
            if len(annotated) < 2:
                continue

            premise_list = annotated[1]

            ground_truths: List[str] = []
            for p in premise_list:
                full_name = p.get("full_name")
                if full_name:
                    ground_truths.append(full_name)

            if ground_truths:
                test_samples.append(
                    {
                        "query": query_state,
                        "targets": ground_truths,
                        "source": file_path,
                    }
                )

    return test_samples


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--vectors", default="premises_vectors.npy")
    p.add_argument("--metadata", default="leandojo_benchmark_4/filtered_premises.txt")
    p.add_argument("--model", default="kaiyuy/leandojo-lean4-retriever-byt5-small")
    p.add_argument("--k", type=int, default=5)
    p.add_argument(
        "--eval-samples",
        type=int,
        default=1000,
        help="Số sample dùng để eval LeanDojo test, mặc định 1000",
    )
    p.add_argument(
        "--leandojo-test-path",
        default="leandojo_benchmark_4/random/test.json",
        help="Đường dẫn tới LeanDojo random/test.json",
    )
    p.add_argument("--batch-size", type=int, default=4)
    p.add_argument("--max-length", type=int, default=4096)
    args = p.parse_args()

    # Load corpus vectors (saved from train script)
    vecs = np.load(args.vectors, mmap_mode="r")
    vecs = np.asarray(vecs, dtype=np.float32)  # faiss wants float32

    # Ensure cosine-sim compatible (L2 normalize)
    # (If already normalized, normalize() is effectively a no-op.)
    vecs = normalize(vecs, norm="l2")

    index = faiss.IndexFlatIP(vecs.shape[1])
    index.add(vecs)

    with open(args.metadata, "r", encoding="utf-8") as f:
        meta = []
        for line in f:
            laf = line.rstrip("\n")
            # Parse <a>Name</a> Statement as in leandojo_benchmark_4/filtered_premises.txt
            # E.g., "theorem <a>Algebra.Ring.Basic.mul_assoc</a> ∀ (a b c : α), (a * b) * c = a * (b * c)"
            try:
                # Split out name in <a>...</a>
                before_a, after_a = laf.split("<a>", 1)
                name_part, rest = after_a.split("</a>", 1)
                name = name_part.strip().split(".")  # list of name components
                statement = rest.strip()
                meta.append({"name": name, "type": statement, "raw": laf})
            except Exception as e:
                # Fallback: treat whole line as type
                meta.append({"name": None, "type": laf, "raw": laf})

    # Map full_name (Init.Prelude.id, ...) -> index trong corpus
    name_to_index: Dict[str, int] = {}
    for i, item in enumerate(meta):
        if item["name"]:
            key = ".".join(item["name"])
            if key not in name_to_index:
                name_to_index[key] = i

    encoder = LeanDojoRetriever(args.model)

    # === Eval LeanDojo random/test.json (goal -> ground-truth premises) ===
    with open(args.leandojo_test_path, "r", encoding="utf-8") as f:
        raw_data = json.load(f)

    all_samples = extract_test_samples(raw_data)
    if not all_samples:
        print("Không tìm được sample nào từ LeanDojo test.json.")
        return

    import random
    from tqdm import tqdm

    random.shuffle(all_samples)
    # samples = all_samples[: args.eval_samples]
    samples = all_samples
    queries: List[str] = []
    gt_index_sets: List[set] = []
    skipped_no_gt_in_corpus = 0

    for s in tqdm(samples, desc="Collecting samples"):
        target_names = s["targets"]  # list full_name string
        idxs = [name_to_index[n] for n in target_names if n in name_to_index]
        if not idxs:
            skipped_no_gt_in_corpus += 1
            continue
        queries.append(s["query"])
        gt_index_sets.append(set(idxs))

    if not queries:
        print("Không có sample nào mà ground-truth premise nằm trong corpus vectors.")
        return

    print(
        f"Dùng {len(queries)} sample (bỏ qua {skipped_no_gt_in_corpus} sample "
        "không mapping được premise vào corpus)."
    )

    q_vecs = encoder.encode(
        queries,
        batch_size=args.batch_size,
        max_length=args.max_length,
    ).astype(np.float32)
    q_vecs = normalize(q_vecs, norm="l2")

    sims, ids = index.search(q_vecs, args.k)

    hit1 = 0
    hitk = 0
    total = len(queries)

    for i, gt_indices in tqdm(enumerate(gt_index_sets), desc="Evaluating", total=len(gt_index_sets)):
        retrieved = ids[i]
        if retrieved[0] in gt_indices:
            hit1 += 1
        if any(idx in gt_indices for idx in retrieved):
            hitk += 1

    print(f"LeanDojo eval trên {total} sample:")
    print(f"Hit@1: {hit1 / total:.4f}")
    print(f"Hit@{args.k}: {hitk / total:.4f}")


if __name__ == "__main__":
    main()
