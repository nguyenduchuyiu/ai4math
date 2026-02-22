"""
Run Apollo on the sample set in problems/miniF2F-sample with shared vLLM.
"""
import os
import argparse
from pathlib import Path

from apollo import ApolloRepair
from prover.launch_solver import create_shared_schedulers, close_shared_schedulers


def main():
    import shutil

    p = argparse.ArgumentParser()
    p.add_argument("--config", type=str, default="configs/baseline_sampling_kimina_prover.py")
    p.add_argument("--problem-dir", type=str, default="problems/miniF2F-Test")
    p.add_argument("--log-root", type=str, default="logs/miniF2F-Test")
    p.add_argument("--rec-depth", type=int, default=2)
    p.add_argument("--limit", type=int, default=None, help="Max number of problems (debug)")
    args = p.parse_args()

    test_dir = Path(args.problem_dir)
    names = sorted(p.stem for p in test_dir.glob("*.lean"))
    if args.limit:
        names = names[: args.limit]

    # Write the config file into the log root dir for reproducibility
    os.makedirs(args.log_root, exist_ok=True)
    config_filename = os.path.basename(args.config)
    config_out_path = os.path.join(args.log_root, config_filename)
    shutil.copy(args.config, config_out_path)
    # Also save CLI arguments and other info, to help record full config
    with open(os.path.join(args.log_root, "run_config.txt"), "w", encoding="utf-8") as f:
        import sys
        import datetime
        f.write(f"Command line: {' '.join(sys.argv)}\n")
        f.write(f"Run time: {datetime.datetime.now()}\n")
        f.write(f"Config file copied to: {config_out_path}\n")
        f.write(f"Arguments:\n")
        for k, v in vars(args).items():
            f.write(f"  {k}: {v}\n")

    cfg, verifier_scheduler, generator_scheduler, llm_processes = create_shared_schedulers(args.config, log_dir=args.log_root)
    shared = {
        "cfg": cfg,
        "verifier_scheduler": verifier_scheduler,
        "generator_scheduler": generator_scheduler,
        "llm_processes": llm_processes,
    }

    try:
        for name in names:
            lean_path = test_dir / f"{name}.lean"
            if not lean_path.is_file():
                print(f"Skip (file not found): {lean_path}")
                continue
            log_dir = os.path.join(args.log_root, name)
            print(f"Running: {name} -> {log_dir}")
            apollo = ApolloRepair(
                code=str(lean_path),
                lemma_name=name,
                config=args.config,
                rec_depth=args.rec_depth,
                lean_version="v4.17.0",
                log_dir=log_dir,
                shared_schedulers=shared,
            )
            apollo.run()
    finally:
        close_shared_schedulers(
            shared["verifier_scheduler"],
            shared["generator_scheduler"],
            shared["llm_processes"],
        )


if __name__ == "__main__":
    main()

# Expect base model: 63.1% pass rate, Apollo (Rec depth 2): 68.9% pass rate