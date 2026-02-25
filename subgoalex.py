from prover.lean.verifier import verify_lean4_file
from utils.scope_sorrifier import Sorrifier
from utils.syntax_repair import SyntaxCorrector
import os
from datetime import datetime


code = '''
import Mathlib
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
lemma aime_1983_p3_1_1
  (f : ℝ → ℝ)
  (h₀ : ∀ (x : ℝ), f x = x ^ (2 : ℕ) + ((18 : ℝ) * x + (30 : ℝ)) - (2 : ℝ) * √(x ^ (2 : ℕ) + ((18 : ℝ) * x + (45 : ℝ))))
  (h₁ : Fintype (↑(f ⁻¹' {(0 : ℝ)}): Type)) :
  ∏ x ∈ (f ⁻¹' {(0 : ℝ)}).toFinset, x = (20 : ℝ) := by
  have h2 : ∀ x : ℝ, f x = x^2 + 18 * x + 30 - 2 * √(x^2 + 18 * x + 45) := by
    intro x
    rw [h₀ x]
    simp [pow_two]
  have h3 : ∀ x : ℝ, f x = 0 ↔ x = -9 + √61 ∨ x = -9 - √61 := by
    intro x
    rw [h2 x]
    constructor
    · -- Assume f(x) = 0
      intro h
      have h4 : √(x ^ 2 + 18 * x + 45) = (x^2 + 18 * x + 30) / 2 := by linarith
      have h5 : 0 ≤ √(x ^ 2 + 18 * x + 45) := Real.sqrt_nonneg (x ^ 2 + 18 * x + 45)
      have h6 : 0 ≤ (x^2 + 18 * x + 30) / 2 := by linarith [h5, h4]
      have h7 : x ^ 2 + 18 * x + 30 ≥ 0 := by linarith [h6]
      have h8 : x^2 + 18 * x + 45 = ((x^2 + 18 * x + 30) / 2) ^ 2 := by
        calc
          x^2 + 18 * x + 45 = (√(x ^ 2 + 18 * x + 45)) ^ 2 := by rw [Real.sq_sqrt]; nlinarith
          _ = ((x^2 + 18 * x + 30) / 2) ^ 2 := by rw [h4]
      have h9 : (x - (-9 + √61)) * (x - (-9 - √61)) = 0 := by
        ring_nf
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 61 by norm_num), h7, h8]
      cases' (mul_eq_zero.mp h9) with h10 h11
      · -- x - (-9 + √61) = 0
        left
        linarith
      · -- x - (-9 - √61) = 0
        right
        linarith
    · -- Show that if x ∈ {-9 + √61, -9 - √61}, then f(x) = 0
      rintro (h | h)
      · -- x = -9 + √61
        rw [h]
        have h12 : √61 ≥ 0 := Real.sqrt_nonneg 61
        have h13 : (-9 + √61) ^ 2 + 18 * (-9 + √61) + 30 - 2 * √((-9 + √61) ^ 2 + 18 * (-9 + √61) + 45) = 0 := by
          have h14 : (-9 + √61) ^ 2 + 18 * (-9 + √61) + 30 = 2 * √((-9 + √61) ^ 2 + 18 * (-9 + √61) + 45) := by
            have h15 : (-9 + √61) ^ 2 + 18 * (-9 + √61) + 45 = 25 := by
              ring_nf
              nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 61 by norm_num)]
            have h16 : √((-9 + √61) ^ 2 + 18 * (-9 + √61) + 45) = 5 := by
              rw [h15]
              exact Real.sqrt_eq_cases.2 (by norm_num)
            nlinarith [h16]
          linarith
        linarith
      · -- x = -9 - √61
        rw [h]
        have h12 : √61 ≥ 0 := Real.sqrt_nonneg 61
        have h13 : (-9 - √61) ^ 2 + 18 * (-9 - √61) + 30 - 2 * √((-9 - √61) ^ 2 + 18 * (-9 - √61) + 45) = 0 := by
          have h14 : (-9 - √61) ^ 2 + 18 * (-9 - √61) + 30 = 2 * √((-9 - √61) ^ 2 + 18 * (-9 - √61) + 45) := by
            have h15 : (-9 - √61) ^ 2 + 18 * (-9 - √61) + 45 = 25 := by
              ring_nf
              nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 61 by norm_num)]
            have h16 : √((-9 - √61) ^ 2 + 18 * (-9 - √61) + 45) = 5 := by
              rw [h15]
              exact Real.sqrt_eq_cases.2 (by norm_num)
            nlinarith [h16]
          linarith
        linarith
  have h17 : (f ⁻¹' {(0 : ℝ)} : Set ℝ) = {(-9 + √61), (-9 - √61)} := by
    ext x
    simp [h3 x]
  have h18 : (f ⁻¹' {(0 : ℝ)}).toFinset = {(-9 + √61), (-9 - √61)} := by
    simp [h17]
  rw [h18]
  rw [Finset.prod_insert]
  rw [Finset.prod_singleton]
  have h19 : (-9 + √61) * (-9 - √61) = (20 : ℝ) := by
    calc
      (-9 + √61) * (-9 - √61) = (-9) ^ 2 - (√61) ^ 2 := by ring
      _ = 81 - 61 := by norm_num [Real.sq_sqrt]
      _ = 20 := by norm_num
  linarith [h19]
'''

# Create output directory if it doesn't exist
os.makedirs("output", exist_ok=True)
timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
output_file = f"output/subgoalex.md"

with open(output_file, "w", encoding="utf-8") as f:
    f.write(f"# Proof Analysis Report\n\n")
    f.write(f"**Generated:** {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n\n")
    
    f.write("## Raw Code\n\n")
    f.write("```lean\n")
    f.write(code)
    f.write("```\n\n")

    # # Apply the same syntax correction pipeline as the main prover.
    # code_corrected = SyntaxCorrector(code).correct_text()

    # f.write("## Corrected Code\n\n")
    # f.write("```lean\n")
    # f.write(code_corrected)
    # f.write("\n```\n\n")
    code_corrected = code
    
    f.write("## Initial Verification\n\n")
    r = verify_lean4_file(code_corrected, timeout=120)
    f.write(f"**Status:** {'✅ PASS' if r['pass'] else '❌ FAIL'}\n\n")
    
    if not r['pass'] and r.get('errors'):
        f.write("### Errors\n\n```bash\n")
        for e in r.get('errors', []):
            f.write(f"- **Line {e['pos']['line']}:** {e['data']}\n")
        f.write("\n```\n\n")

    f.write("## Sorrification Process\n\n")
    checker = Sorrifier(verify_lean4_file, max_cycles=20)
    result = checker.verify_and_fix(code_corrected)

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