from prover.lean.verifier import verify_lean4_file
from utils.auto_sorrifier import AutoSorrifier
from utils.syntax_repair import SyntaxCorrector
import os
from datetime import datetime


code = '''
import Mathlib
open BigOperators Real Nat Topology Rat
lemma aime_1983_p3_1_1
  (f : ℝ → ℝ)
  (h₀ : ∀ (x : ℝ), f x = x ^ (2 : ℕ) + ((18 : ℝ) * x + (30 : ℝ)) - (2 : ℝ) * √(x ^ (2 : ℕ) + ((18 : ℝ) * x + (45 : ℝ))))
  (h₁ : Fintype (↑(f ⁻¹' {(0 : ℝ)}) : Type)) :
  ∏ x ∈ (f ⁻¹' {(0 : ℝ)}).toFinset, x = (20 : ℝ) := by
  have h2 : ∀ x : ℝ, f x = x^2 + 18*x + 30 - 2*√(x^2 + 18*x + 45) := by
    intro x
    rw [h₀ x]
    ring
  have h3 : (f ⁻¹' {(0 : ℝ)}).toFinset = {-5, -4} := by
    have h4 : ∀ x : ℝ, f x = 0 ↔ x = -5 ∨ x = -4 := by
      intro x
      rw [h2 x]
      simp
      constructor
      · intro h
        have h5 : x^2 + 18*x + 30 - 2*√(x^2 + 18*x + 45) = 0 := by
          linarith [h]
        have h6 : √(x^2 + 18*x + 45) = (x^2 + 18*x + 30) / 2 := by
          linarith [h5]
        have h7 : x^2 + 18*x + 30 ≥ 0 := by
          nlinarith [Real.sqrt_nonneg (x^2 + 18*x + 45), sq_nonneg (x + 9)]
        have h8 : x^2 + 18*x + 45 ≥ 0 := by
          nlinarith [Real.sqrt_nonneg (x^2 + 18*x + 45), sq_nonneg (x + 9)]
        have h9 : x^2 + 18*x + 30 = 2*√(x^2 + 18*x + 45) := by linarith [h6]
        have h10 : (x^2 + 18*x + 30)^2 = 4*(x^2 + 18*x + 45) := by
          calc
            (x^2 + 18*x + 30)^2 = (2*√(x^2 + 18*x + 45))^2 := by rw [h9]
            _ = 4 * (√(x^2 + 18*x + 45))^2 := by ring
            _ = 4 * (x^2 + 18*x + 45) := by rw [Real.sq_sqrt h8]
        have h11 : x^4 + 36*x^3 + 242*x^2 + 1008*x + 720 = 0 := by
          nlinarith [h10]
        have h12 : (x + 5)*(x + 4)*(x^2 + 32*x + 288) = 0 := by
          ring_nf at h11 ⊢
          linarith
        cases' (mul_eq_zero.mp h12) with h13 h14
        · cases' (mul_eq_zero.mp h13) with h15 h16
          · left
            linarith
          · right
            linarith
        · have h17 : x^2 + 32*x + 288 = 0 := by
            linarith
          have h18 : x^2 + 32*x + 288 > 0 := by
            nlinarith
          linarith
      · intro h
        cases' h with h19 h20
        · rw [h19]
          have h21 : √(25 + (-90) + 30) = √(-35) := by
            norm_num
          have h22 : √(-35) = 0 := by
            linarith [Real.sqrt_nonneg (-35), h21]
          linarith [h22]
        · rw [h20]
          have h23 : √(16 + (-72) + 30) = √(-26) := by
            norm_num
          have h24 : √(-26) = 0 := by
            linarith [Real.sqrt_nonneg (-26), h23]
          linarith [h24]
    ext x
    simp [h4]
  rw [h3]
  rw [Finset.prod_insert]
  rw [Finset.prod_singleton]
  norm_num
  all_goals
    linarith
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

    # Apply the same syntax correction pipeline as the main prover.
    code_corrected = SyntaxCorrector(code).correct_text()

    f.write("## Corrected Code\n\n")
    f.write("```lean\n")
    f.write(code_corrected)
    f.write("\n```\n\n")
    # code_corrected = code
    
    f.write("## Initial Verification\n\n")
    r = verify_lean4_file(code_corrected, timeout=120)
    f.write(f"**Status:** {'✅ PASS' if r['pass'] else '❌ FAIL'}\n\n")
    
    if not r['pass'] and r.get('errors'):
        f.write("### Errors\n\n```bash\n")
        for e in r.get('errors', []):
            f.write(f"- **Line {e['pos']['line']}:** {e['data']}\n")
        f.write("\n```\n\n")

    f.write("## Sorrification Process\n\n")
    checker = AutoSorrifier(code_corrected, max_cycles=20, log_path="output/sorrification.log")
    result = checker.fix_code()

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

    from utils.proof_state_extractor import extract_queries
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