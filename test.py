from utils.extract_lemmas_from_sorry import LemmaExtractor
import os

from prover.lean.verifier import verify_lean4_file

main_lean_path = "logs/aime_1984_p5/0_aime_1984_p5_1/main_theorem.lean"

with open(main_lean_path, "r") as f:
    final_code = f.read()

lemma_extractor = LemmaExtractor(final_code, verify_lean4_file)
lemmas = lemma_extractor.get_lemmas()
print(lemmas)