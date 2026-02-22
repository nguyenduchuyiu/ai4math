from prover.lean.verifier import verify_lean4_file
from utils.sorrify import Sorrifier, ProofTree
import os
from datetime import datetime


code = '''import Mathlib
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

lemma aime_1983_p3_1_1
    (f : ℝ → ℝ)
    (h₀ : ∀ x : ℝ,
        f x =
        x ^ 2 + (18 * x + 30) - 2 * √(x ^ 2 + 18 * x + 45))
    (h₁ : Fintype (↑(f ⁻¹' {0}) : Type)) :
    ∏ x ∈ (f ⁻¹' {0}).toFinset, x = 20 := by
  have h2 : ∀ x : ℝ, f x = 0 ↔ x = -9 + √61 ∨ x = -9 - √61 := by
    intro x
    constructor
    · -- Assume f(x) = 0, prove x = -9 ± √61
      intro hx
      have hfx : f x = x ^ 2 + (18 * x + 30) - 2 * √(x ^ 2 + 18 * x + 45) := h₀ x
      rw [hfx] at hx
      have h_eq : x ^ 2 + (18 * x + 30) - 2 * √(x ^ 2 + 18 * x + 45) = 0 := hx
      have h1 : 2 * √(x ^ 2 + 18 * x + 45) = x ^ 2 + 18 * x + 30 := by linarith
      have h2 : x ^ 2 + 18 * x + 45 ≥ 0 := by
        nlinarith [Real.sqrt_nonneg (x ^ 2 + 18 * x + 45)]
      have h3 : √(x ^ 2 + 18 * x + 45) ≥ 0 := Real.sqrt_nonneg (x ^ 2 + 18 * x + 45)
      have h4 : x ^ 2 + 18 * x + 30 ≥ 0 := by nlinarith
      have h5 : x ^ 2 + 18 * x + 30 = 2 * √(x ^ 2 + 18 * x + 45) := by linarith
      have h6 : (x ^ 2 + 18 * x + 30) ^ 2 = 4 * (x ^ 2 + 18 * x + 45) := by
        have hsq : (2 * √(x ^ 2 + 18 * x + 45)) ^ 2 = 4 * (x ^ 2 + 18 * x + 45) := by
          calc
            (2 * √(x ^ 2 + 18 * x + 45)) ^ 2 = 4 * (√(x ^ 2 + 18 * x + 45) ^ 2) := by ring
            _ = 4 * (x ^ 2 + 18 * x + 45) := by rw [Real.sq_sqrt h2]
        rw [← h5] at hsq
        nlinarith
      have h7 : (x - (-9 + √61)) * (x - (-9 - √61)) = 0 := by
        ring_nf
        nlinarith [h6, Real.sq_sqrt (show 0 ≤ 61 by norm_num : (61 : ℝ) ≥ 0)]
      cases' (mul_eq_zero.mp h7) with h8 h9
      · left
        linarith
      · right
        linarith
    · -- Assume x = -9 ± √61, prove f(x) = 0
      rintro (h | h)
      · -- x = -9 + √61
        rw [h]
        have h1 : (-9 + √61) ^ 2 + (18 * (-9 + √61) + 30) - 2 * √((-9 + √61) ^ 2 + 18 * (-9 + √61) + 45) = 0 := by
          have h2 : (-9 + √61) ^ 2 + 18 * (-9 + √61) + 30 = 10 := by
            ring_nf
            nlinarith [Real.sq_sqrt (show 0 ≤ 61 by norm_num : (61 : ℝ) ≥ 0)]
          have h3 : √((-9 + √61) ^ 2 + 18 * (-9 + √61) + 45) = 5 := by
            rw [show (-9 + √61) ^ 2 + 18 * (-9 + √61) + 45 = 25 by ring_nf; nlinarith [Real.sq_sqrt (show 0 ≤ 61 by norm_num : (61 : ℝ) ≥ 0)]]
            exact Real.sqrt_eq_cases.2 (by norm_num)
          linarith
        rw [h1]
      · -- x = -9 - √61
        rw [h]
        have h1 : (-9 - √61) ^ 2 + (18 * (-9 - √61) + 30) - 2 * √((-9 - √61) ^ 2 + 18 * (-9 - √61) + 45) = 0 := by
          have h2 : (-9 - √61) ^ 2 + 18 * (-9 - √61) + 30 = 10 := by
            ring_nf
            nlinarith [Real.sq_sqrt (show 0 ≤ 61 by norm_num : (61 : ℝ) ≥ 0)]
          have h3 : √((-9 - √61) ^ 2 + 18 * (-9 - √61) + 45) = 5 := by
            rw [show (-9 - √61) ^ 2 + 18 * (-9 - √61) + 45 = 25 by ring_nf; nlinarith [Real.sq_sqrt (show 0 ≤ 61 by norm_num : (61 : ℝ) ≥ 0)]]
            exact Real.sqrt_eq_cases.2 (by norm_num)
          linarith
        rw [h1]
  have h3 : (f ⁻¹' {0}).toFinset = {(-9 + √61), (-9 - √61)} := by
    ext x
    simp [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · -- Show that if f(x) = 0, then x ∈ { -9+√61, -9-√61 }
      intro hfx
      have h_eq : f x = 0 := hfx
      have h4 : x = -9 + √61 ∨ x = -9 - √61 := h2 x
      tauto
    · -- Show that if x ∈ { -9+√61, -9-√61 }, then f(x) = 0
      rintro (h | h)
      · -- x = -9 + √61
        rw [h]
        exact (h2 (-9 + √61)).left
      · -- x = -9 - √61
        rw [h]
        exact (h2 (-9 - √61)).right
  rw [h3]
  rw [Finset.prod_pair]
  have h4 : (-9 + √61) ≠ (-9 - √61) := by
    have h5 : √61 > 0 := Real.sqrt_pos.mpr (by norm_num : (61 : ℝ) > 0)
    linarith [h5]
  simp [h4]
  linarith [Real.sq_sqrt (show 0 ≤ 61 by norm_num : (61 : ℝ) ≥ 0)]
'''

# Create output directory if it doesn't exist
os.makedirs("output", exist_ok=True)
timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
output_file = f"output/proof_analysis_{timestamp}.md"

with open(output_file, "w", encoding="utf-8") as f:
    f.write(f"# Proof Analysis Report\n\n")
    f.write(f"**Generated:** {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n\n")
    
    f.write("## Raw Code\n\n")
    f.write("```lean\n")
    f.write(code)
    f.write("```\n\n")

    pt = ProofTree(code)
    pt.parse_lean_with_dot_subcases(clean_empty_lines=True, clean_comments=False)

    f.write("## Parsed Tree Structure\n\n")
    f.write("```\n")
    # Capture tree output
    import io
    import sys
    old_stdout = sys.stdout
    sys.stdout = buffer = io.StringIO()
    pt.print_lean_tree()
    tree_output = buffer.getvalue()
    sys.stdout = old_stdout
    f.write(tree_output)
    f.write("```\n\n")
    
    f.write("## Tree Code\n\n")
    f.write("```lean\n")
    f.write(pt.retrieve_lean_tree_code())
    f.write("\n```\n\n")
    
    f.write("## Initial Verification\n\n")
    r = verify_lean4_file(pt.retrieve_lean_tree_code(), timeout=120)
    f.write(f"**Status:** {'✅ PASS' if r['pass'] else '❌ FAIL'}\n\n")
    
    if not r['pass'] and r.get('errors'):
        f.write("### Errors\n\n```bash\n")
        for e in r.get('errors', []):
            f.write(f"- **Line {e['pos']['line']}:** {e['data']}\n")
        f.write("\n```\n\n")

    f.write("## Sorrification Process\n\n")
    checker = Sorrifier(pt, verify_lean4_file, clean_empty_lines=True, clean_comments=False)
    result = checker.verify_and_fix_tree()

    f.write("### Sorrified Result\n\n")
    f.write("```lean\n")
    f.write(result)
    f.write("\n```\n\n")

    f.write("## Auto Solver (ProofRepairer)\n\n")
    from utils.hint_repair import ProofRepairer
    repairer = ProofRepairer(result, verify_lean4_file)
    final_code = repairer.repair_proof()

    f.write("### Auto Solver Result\n\n")
    f.write("```lean\n")
    f.write(final_code)
    f.write("\n```\n\n")

    # Verify final result
    final_check = verify_lean4_file(final_code, timeout=120)
    f.write("## Final Verification\n\n")
    f.write(f"- **Pass:** {'Yes' if final_check['pass'] else 'No'}\n")
    f.write(f"- **Complete:** {'Yes' if final_check.get('complete', False) else 'No'}\n")

    from utils.extract_proof_state import extract_queries
    from retriever import retrieve

    f.write("## RAG Retrieval Analysis\n\n")

    queries = extract_queries(final_code)
    f.write(f"**Found {len(queries)} sorry(s)**\n\n")

    for i, q in enumerate(queries, 1):
        f.write(f"### Sorry #{i} (Line {q['line']})\n\n")
        f.write("#### Query\n\n```lean\n")
        f.write(q['raw'])
        f.write("\n```\n\n")
        
        # results = retrieve(q['raw'], k=10)
        # f.write(f"#### Retrieved {len(results)} Premises\n\n```lean\n")
        
        # for j, (premise, score) in enumerate(results, 1):
        #     f.write(f"**[{j}] {premise['full_name']}** (Similarity: {score:.4f})\n\n")
        #     premise_code = premise["code"]
        #     if len(premise_code) > 200:
        #         f.write(premise_code[:200] + "...")
        #     else:
        #         f.write(premise_code)
        #     f.write("\n")
        # f.write("\n```\n\n")

print(f"Analysis complete! Report saved to: {output_file}")
print(f"Open the file to view the formatted results.")