import os
import sys
import glob
import json
import time
import pickle
import shutil
import argparse
import re
from pathlib import Path
from tqdm import tqdm

# -- Local imports (adjust paths if needed) --
from utils.syntax_repair import SyntaxCorrector
from utils.auto_sorrifier import AutoSorrifier, PersistentASTDaemon
from utils.extract_lemmas_from_sorry import LemmaExtractor
from utils.convert_lean_to_json import get_deepseek_format_proofs
from utils.proof_assembler import LeanProofAssembler
from utils.hint_repair import ProofRepairer
from proof_selector import select_and_extract

from prover.lean.verifier import verify_lean4_file
from prover.launch_solver import (create_shared_schedulers, 
                                  launch_llm, 
                                  launch_llm_with_schedulers, 
                                  close_shared_schedulers)



class ApolloRepair:
    def __init__(self,
                 code: str,
                 lemma_name: str,
                 config: str = "configs/baseline_sampling.py",
                 rec_depth: int = 2,
                 log_dir = None,
                 shared_schedulers = None):
        self.code = code
        # If a file path is passed, load its contents so downstream steps see Lean code, not the path string.
        if os.path.isfile(self.code):
            with open(self.code, "r", encoding="utf-8") as f:
                self.code = f.read()


        self.lemma_name = lemma_name
        self.config = config
        self.rec_depth = rec_depth
        self.log_dir = log_dir
        os.makedirs(self.log_dir, exist_ok=True)
        self.shared_schedulers = shared_schedulers
        self._own_schedulers = False  # track if we created them ourselves
        self.repl_dir = "/workspace/npthai/APOLLO/repl"
        self._ast_daemon = None  # lazy init

        self.options = 'set_option pp.instanceTypes true\nset_option pp.numericTypes true\nset_option pp.coercions.types true\nset_option pp.letVarTypes true\nset_option pp.structureInstanceTypes true\nset_option pp.instanceTypes true\nset_option pp.mvars.withType true\nset_option pp.coercions true\nset_option pp.funBinderTypes true\nset_option pp.piBinderTypes true'

        self.default_header = f'import Mathlib\nimport Aesop\n\nopen BigOperators Real Nat Topology Rat\n\n'
    
    @property
    def repl_verifier(self):
        return self._ensure_schedulers()["verifier_scheduler"]

    def _verify(self, code, **kwargs):
        """Submit one verification request to the shared scheduler."""
        req_ids = self.repl_verifier.submit_all_request([dict(code=code, **kwargs)])
        return self.repl_verifier.get_all_request_outputs(req_ids)[0]

    def _ensure_schedulers(self):
        if self.shared_schedulers is None:
            print(f"[{self.lemma_name}] Initializing shared schedulers...")
            cfg, verifier_scheduler, generator_scheduler, llm_processes = create_shared_schedulers(
                self.config, log_dir=self.log_dir
            )
            self.shared_schedulers = {
                "cfg": cfg,
                "verifier_scheduler": verifier_scheduler,
                "generator_scheduler": generator_scheduler,
                "llm_processes": llm_processes,
            }
            self._own_schedulers = True
        return self.shared_schedulers

    @property
    def ast_daemon(self):
        if self._ast_daemon is None:
            print(f"[{self.lemma_name}] Initializing AST Daemon...")
            self._ast_daemon = PersistentASTDaemon(self.repl_dir)
        return self._ast_daemon

    def preprocess_code(self, code):
        code = code.splitlines()
        for i, line in enumerate(code):
            if line.strip().startswith('theorem') or line.strip().startswith('lemma'):
                line = f'\n{self.options}\n' + line
                code[i] = line
                break
        code = '\n'.join(code)

        return code

    def run(self) -> str:
        try:
            # prepend additional options for explicit type ontations for variables
            code = self.preprocess_code(self.code)
    
            start_time = time.time()
    
            # 1) Attempt to fix the code (will recurse as necessary)
            self.fix_code(
                code=code,
                attempt=1,
                log_dir=self.log_dir,
            )
    
            # 2) Once done, gather everything into a final proof
            proof_root = Path(self.log_dir)
            assembler = LeanProofAssembler(proof_root)
            final_proof_content = assembler.assemble_full_proof()
    
            # 3) Write out the final assembled proof
            output_file = proof_root / "assembled_main_theorem.lean"
            with open(output_file, "w", encoding="utf-8") as f:
                f.write(final_proof_content)
    
            print(f"Final assembled proof saved to: {output_file}")
            elapsed = time.time() - start_time
            print(f"ApolloRepair finished in {elapsed:.2f}s.")
            return str(output_file)
        finally:
            if self._ast_daemon is not None:
                self._ast_daemon.close()
                self._ast_daemon = None
            if self._own_schedulers and self.shared_schedulers is not None:
                from prover.launch_solver import close_shared_schedulers
                close_shared_schedulers(
                    self.shared_schedulers["verifier_scheduler"],
                    self.shared_schedulers["generator_scheduler"],
                    self.shared_schedulers["llm_processes"],
                )
                self.shared_schedulers = None
                self._own_schedulers = False

    def fix_code(self,
                 code: str,
                 attempt: int,
                 log_dir: str,
                 ):
        if attempt > self.rec_depth:
            print(f"[{self.lemma_name}] Max attempts ({self.rec_depth}) exceeded. Stopping recursion.")
            return

        main_lean_path = os.path.join(log_dir, "main_theorem.lean")
        data_path = os.path.join(log_dir, f"rec_{attempt}.jsonl")

        # If we haven't already created main_theorem.lean in this attempt
        if not os.path.isfile(main_lean_path): 
            # -- Syntax repair --
            code_corrected = SyntaxCorrector(code).correct_text()
            print(f"[{self.lemma_name}] Attempt {attempt}, after syntax fix:\n{code_corrected}\n")

            if not self._verify(code_corrected)['pass']:
                print(f"[{self.lemma_name}] Starting AST-based repair...")
                patcher = AutoSorrifier(
                    code=code_corrected, 
                    ast_daemon=self.ast_daemon, 
                    repl_verifier=self.repl_verifier,
                    max_cycles=30
                )
                code_corrected_sorry = patcher.fix_code()
                print(f"[{self.lemma_name}] After AST-based sorrification:\n{code_corrected_sorry}\n")
            else:
                code_corrected_sorry = code_corrected

            # -- Automatic proof repair --
            if 'sorry' in code_corrected_sorry:
                print(f"[{self.lemma_name}] Starting proof repair...")
                repairer = ProofRepairer(code_corrected_sorry, verify_lean4_file)
                final_code = repairer.repair_proof()
                print(f"[{self.lemma_name}] After repair: {final_code.count('sorry')} sorry(s) remaining.")
            else:
                final_code = code_corrected_sorry
            print(f"[{self.lemma_name}] Final repaired code:\n{final_code}\n")

            # Save the best known main theorem for this attempt
            with open(main_lean_path, "w") as f:
                f.write(final_code)
        else:
            # If main_theorem.lean already exists from a previous call
            with open(main_lean_path, "r") as f:
                final_code = f.read()

        # Extract sub-lemmas only if we haven't yet saved them this attempt
        if not os.path.isfile(data_path):
            lemma_extractor = LemmaExtractor(final_code, verify_lean4_file)
            lemmas = lemma_extractor.get_lemmas()

            # Fallback: if no lemmas extracted but code still fails,
            # force-sorrify the entire proof body and extract the main goal
            if not lemmas:
                verify_result = self._verify(final_code)
                if not verify_result.get('complete', False):
                    print(f"[{self.lemma_name}] No lemmas extracted, forcing full sorrification fallback.")
                    fallback_code = final_code.split(':= by')[0] + ':= by\n  sorry'
                    fallback_verify = verify_lean4_file(fallback_code)
                    if fallback_verify.get('pass', False):
                        # Update main_theorem.lean with the sorrified version
                        final_code = fallback_code
                        with open(main_lean_path, "w") as f:
                            f.write(final_code)
                        lemma_extractor = LemmaExtractor(final_code, verify_lean4_file)
                        lemmas = lemma_extractor.get_lemmas()

            formatted_lemmas = get_deepseek_format_proofs(lemmas)

            print(f"[{self.lemma_name}] Attempt {attempt} - extracted {len(lemmas)} lemmas.")
            print(f"[{self.lemma_name}] Attempt {attempt} - formatted into {len(formatted_lemmas)} JSON lines.")

            with open(data_path, "w") as f:
                for item in formatted_lemmas:
                    f.write(json.dumps(item, ensure_ascii=False) + "\n")

        # Now run the LLM solver on the sub-lemmas
        if self.shared_schedulers:
            launch_llm_with_schedulers(
                data_path,
                self.config,
                log_dir,
                verifier_scheduler=self.shared_schedulers["verifier_scheduler"],
                generator_scheduler=self.shared_schedulers["generator_scheduler"],
                cfg=self.shared_schedulers.get("cfg"),
                node_rank=self.shared_schedulers.get("node_rank", 0),
                world_size=self.shared_schedulers.get("world_size", 1),
            )
        else:
            launch_llm(data_path, self.config, log_dir)

        # Next, update or finalize the main theorem
        self.generate_main_theorem_files(log_dir, attempt)

    def generate_main_theorem_files(self, log_dir: str, attempt: int):
        for entry in os.listdir(log_dir):
            fullpath = os.path.join(log_dir, entry)

            # Skip direct files that are not pkl logs or subdirectories
            if os.path.isfile(fullpath):
                if not entry.endswith(".pkl"):
                    continue

            # If it's a directory that may contain .pkl logs
            if os.path.isdir(fullpath):
                if 'run' in fullpath:
                    continue
                print(fullpath)
                success_file = glob.glob(os.path.join(fullpath, "success-*.pkl"))
                if success_file:
                    with open(success_file[0], "rb") as f:
                        data = pickle.load(f)[0]
                    verified_code = data["result"]["verified_code"]
                    with open(os.path.join(fullpath, "main_theorem.lean"), "w") as f:
                        f.write(verified_code)
                else:
                    failure_files = glob.glob(os.path.join(fullpath, "failure-*.pkl"))
                    if not failure_files:
                        print(f"No success or failure pkl found in {fullpath}, skipping")
                        continue
                    
                    # Load failure candidates and use proof selector
                    print(f"[{self.lemma_name}] Loading failure candidates from {failure_files[0]}")
                    with open(failure_files[0], "rb") as f:
                        failure_data = pickle.load(f)
                    
                    # Extract proof bodies and formal statement - simplified
                    proof_bodies = []
                    formal_statement = ""
                    for entry in failure_data:
                        if isinstance(entry, dict) and 'proof_code' in entry and 'formal_statement' in entry:
                            # Get formal statement from first entry
                            if not formal_statement:
                                formal_statement = entry['formal_statement']
                            # Use proof_code directly - it's already the proof body
                            proof_bodies.append(entry['proof_code'])
                    
                    if not proof_bodies:
                        print(f"[{self.lemma_name}] No valid proof bodies found in failure file")
                        continue
                    
                    # Create header: imports + formal statement + ':= by'
                    header_imports = self.extract_header(self.code)
                    if not header_imports:
                        print(f"[{self.lemma_name}] No header imports found in main theorem")
                        header_imports = self.default_header
                    # formal_statement already ends with ':= by', so don't add it again
                    if formal_statement.endswith(' := by'):
                        header = header_imports + "\n\n" + formal_statement
                    else:
                        header = header_imports + "\n\n" + formal_statement + " := by"
                    # Use proof selector to find best candidate
                    print(f"[{self.lemma_name}] Running proof selector on {len(proof_bodies)} candidates")
                    try:
                        result = select_and_extract(
                            header, proof_bodies, top_k=1,
                            verifier=self.repl_verifier,
                            ast_server=self.ast_daemon,
                            max_workers=4,
                        )
                        if result["selected"]:
                            best_candidate = result["selected"][0]
                            print(f"[{self.lemma_name}] Selected best candidate with {best_candidate.num_preserved_steps} preserved steps")
                            
                            # Save the sorrified (verified-passing) candidate and continue recursion
                            if not best_candidate.sorrified_code:
                                print(f"[{self.lemma_name}] sorrified_code is empty for best candidate #{best_candidate.idx}, skipping")
                                continue
                            saved_code = best_candidate.sorrified_code
                            with open(os.path.join(fullpath, "main_theorem.lean"), "w") as f:
                                f.write(saved_code)
                                print(f"[{self.lemma_name}] Saved selected candidate to {os.path.join(fullpath, 'main_theorem.lean')}")
                            
                            # Continue with the selected candidate
                            self.fix_code(saved_code, attempt + 1, fullpath)
                        else:
                            print(f"[{self.lemma_name}] No valid candidates found by proof selector")
                    except Exception as e:
                        print(f"[{self.lemma_name}] Error in proof selector: {e}")
                        continue

    def extract_header(self, code):
        header = []
        for line in code.splitlines():
            if any(k in line for k in ("import", "open")):
                header.append(line)
        return '\n'.join(header)
    
if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--config", type=str, default="configs/baseline_sampling_kimina_prover.py")
    parser.add_argument("--problem", type=str, default="problems/problem1.lean")
    args = parser.parse_args()
    # Create log_dir from problem file name (without extension)
    base_problem = os.path.splitext(os.path.basename(args.problem))[0]
    print("Base problem: ", base_problem)
    log_dir = os.path.join('logs', base_problem)
    code = open(args.problem, 'r').read()
    cfg, verifier_scheduler, generator_scheduler, llm_processes = create_shared_schedulers(args.config, log_dir=log_dir)
    shared = {
        "cfg": cfg,
        "verifier_scheduler": verifier_scheduler,
        "generator_scheduler": generator_scheduler,
        "llm_processes": llm_processes,
    }
    apollo = ApolloRepair(
        code=code, 
        lemma_name=base_problem, 
        config=args.config, 
        rec_depth=3, 
        log_dir=log_dir,
        shared_schedulers=shared
    )
    try:
        apollo.run()
    finally:
        close_shared_schedulers(verifier_scheduler, generator_scheduler, llm_processes)