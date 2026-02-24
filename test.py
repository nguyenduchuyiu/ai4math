import os
import hashlib

ROOT = "logs/miniF2F-Test"

def file_hash(path, chunk_size=8192):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        while True:
            chunk = f.read(chunk_size)
            if not chunk:
                break
            h.update(chunk)
    return h.hexdigest()

different = []

for dirpath, dirnames, filenames in os.walk(ROOT):
    if "rec_1.jsonl" in filenames and "rec_2.jsonl" in filenames:
        f1 = os.path.join(dirpath, "rec_1.jsonl")
        f2 = os.path.join(dirpath, "rec_2.jsonl")

        if file_hash(f1) != file_hash(f2):
            # dirpath chính là thư mục của bài toán hiện tại
            different.append(dirpath)

print("Số bài có rec_1.jsonl khác rec_2.jsonl:", len(different))
for d in different:
    print(d)