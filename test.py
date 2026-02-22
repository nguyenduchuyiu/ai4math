from utils.extract_proof_state import extract_queries
from retriever import retrieve

code = open("tet.lean").read()
print(f"=== Input ===\n{code}")

queries = extract_queries(code)
print(f"Found {len(queries)} sorry(s)\n")

for i, q in enumerate(queries, 1):
    print(f"--- sorry #{i} (line {q['line']}) ---")
    print(f"RAG query:\n{q['raw']}\n")
    results = retrieve(q['raw'], k=10)
    print(f"\nRetrieved {len(results)} premises:")
    for i, (premise, score) in enumerate(results, 1):
        print(f"\n[{i}] Similarity: {score:.4f}")
        print(f"Name: {premise['full_name']}")
        print(premise["code"][:200] + ("..." if len(premise["code"]) > 200 else ""))