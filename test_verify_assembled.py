"""
Test script to verify assembled Lean proofs and report pass/fail statistics.

Usage:
    python test_verify_assembled.py logs/miniF2F-sample
    python test_verify_assembled.py logs/miniF2F-sample --timeout 120
    python test_verify_assembled.py logs/miniF2F-sample --skip-verify  # only check sorry + recursion stats
"""

import os
import sys
import argparse
import re
from collections import defaultdict
from concurrent.futures import ThreadPoolExecutor, as_completed

from prover.lean.verifier import verify_lean4_file


def count_recursion_depth(problem_dir):
    """Count max recursion depth by traversing subdirectories.
    
    Subfolder pattern: 0_<problem_name>_1 -> 0_<problem_name>_1_1 -> 0_<problem_name>_1_1_1
    Each level = 1 recursion.
    """
    max_depth = 0

    def _walk(d, depth):
        nonlocal max_depth
        for entry in os.listdir(d):
            full = os.path.join(d, entry)
            if os.path.isdir(full) and entry.startswith("0_"):
                new_depth = depth + 1
                if new_depth > max_depth:
                    max_depth = new_depth
                _walk(full, new_depth)

    _walk(problem_dir, 0)
    return max_depth


def check_problem(problem_dir, problem_name, timeout=300, skip_verify=False):
    """Check a single problem. Returns dict with status info."""
    lean_file = os.path.join(problem_dir, "assembled_main_theorem.lean")
    result = {
        "name": problem_name,
        "has_assembled": False,
        "has_sorry": None,
        "verify_pass": None,
        "verify_complete": None,
        "verify_errors": [],
        "recursion_depth": count_recursion_depth(problem_dir),
        "status": "NO_FILE",
    }

    if not os.path.exists(lean_file):
        return result

    result["has_assembled"] = True

    with open(lean_file, "r") as f:
        code = f.read()

    if "sorry" in code:
        result["has_sorry"] = True
        result["status"] = "SORRY"
        return result

    result["has_sorry"] = False

    if skip_verify:
        result["status"] = "SKIP_VERIFY"
        return result

    # Verify with lean4
    print(f"  Verifying {problem_name} ...", end=" ", flush=True)
    vresult = verify_lean4_file(code, timeout=timeout)
    result["verify_pass"] = vresult.get("pass", False)
    result["verify_complete"] = vresult.get("complete", False)
    result["verify_errors"] = vresult.get("errors", [])
    verify_time = vresult.get("verify_time", 0)

    if result["verify_complete"]:
        result["status"] = "PASS"
        print(f"PASS ({verify_time:.1f}s)")
    elif result["verify_pass"]:
        result["status"] = "PASS_INCOMPLETE"
        print(f"PASS_INCOMPLETE ({verify_time:.1f}s)")
    else:
        result["status"] = "FAIL"
        errors = result["verify_errors"]
        err_msg = errors[0]["data"][:80] if errors else "unknown"
        print(f"FAIL ({verify_time:.1f}s) - {err_msg}")

    return result


def main():
    parser = argparse.ArgumentParser(description="Verify assembled Lean proofs")
    parser.add_argument("folder", help="Root folder containing problem subdirectories")
    parser.add_argument("--timeout", type=int, default=300, help="Lean verification timeout (seconds)")
    parser.add_argument("--skip-verify", action="store_true", help="Skip Lean verification, only check sorry and recursion")
    args = parser.parse_args()

    root = args.folder
    if not os.path.isdir(root):
        print(f"Error: {root} is not a directory")
        sys.exit(1)

    problems = sorted([
        d for d in os.listdir(root)
        if os.path.isdir(os.path.join(root, d))
    ])

    print(f"Found {len(problems)} problems in {root}\n")

    results = []

    # ---- Use 16 workers in a ThreadPoolExecutor ----
    def _single_problem_task(pname):
        pdir = os.path.join(root, pname)
        return check_problem(pdir, pname, timeout=args.timeout, skip_verify=args.skip_verify)

    with ThreadPoolExecutor(max_workers=16) as executor:
        # submit jobs
        future_to_name = {executor.submit(_single_problem_task, pname): pname for pname in problems}
        for future in as_completed(future_to_name):
            r = future.result()
            results.append(r)

    # sort results by problem name for consistent output
    results.sort(key=lambda r: r["name"])

    # --- Summary ---
    print("\n" + "=" * 90)
    print("SUMMARY")
    print("=" * 90)

    status_counts = defaultdict(int)
    for r in results:
        status_counts[r["status"]] += 1

    total = len(results)
    pass_count = status_counts.get("PASS", 0)
    pass_incomplete = status_counts.get("PASS_INCOMPLETE", 0)
    sorry_count = status_counts.get("SORRY", 0)
    fail_count = status_counts.get("FAIL", 0)
    no_file = status_counts.get("NO_FILE", 0)
    skip_count = status_counts.get("SKIP_VERIFY", 0)

    print(f"Total problems:     {total}")
    print(f"PASS (complete):    {pass_count}")
    print(f"PASS (incomplete):  {pass_incomplete}")
    print(f"SORRY:              {sorry_count}")
    print(f"FAIL:               {fail_count}")
    print(f"NO_FILE:            {no_file}")
    if skip_count:
        print(f"SKIP_VERIFY:        {skip_count}")

    verified = pass_count + pass_incomplete + fail_count
    if verified > 0:
        print(f"\nPass rate (verified): {pass_count + pass_incomplete}/{verified} = {(pass_count + pass_incomplete) / verified * 100:.1f}%")
    if total > 0:
        print(f"Pass rate (total):    {pass_count + pass_incomplete}/{total} = {(pass_count + pass_incomplete) / total * 100:.1f}%")

    # --- Recursion depth stats ---
    print("\n" + "=" * 90)
    print("RECURSION DEPTH STATISTICS")
    print("=" * 90)

    depth_stats = defaultdict(lambda: {"total": 0, "pass": 0, "sorry": 0, "fail": 0, "other": 0})
    for r in results:
        d = r["recursion_depth"]
        depth_stats[d]["total"] += 1
        if r["status"] in ("PASS", "PASS_INCOMPLETE"):
            depth_stats[d]["pass"] += 1
        elif r["status"] == "SORRY":
            depth_stats[d]["sorry"] += 1
        elif r["status"] == "FAIL":
            depth_stats[d]["fail"] += 1
        else:
            depth_stats[d]["other"] += 1

    print(f"{'Depth':<8} {'Total':<8} {'Pass':<8} {'Sorry':<8} {'Fail':<8} {'Other':<8}")
    print("-" * 48)
    for d in sorted(depth_stats.keys()):
        s = depth_stats[d]
        print(f"{d:<8} {s['total']:<8} {s['pass']:<8} {s['sorry']:<8} {s['fail']:<8} {s['other']:<8}")

    # --- Per-problem detail ---
    print("\n" + "=" * 90)
    print("PER-PROBLEM DETAIL")
    print("=" * 90)
    print(f"{'Problem':<60} {'Status':<18} {'Rec.Depth':<10}")
    print("-" * 88)
    for r in results:
        print(f"{r['name']:<60} {r['status']:<18} {r['recursion_depth']:<10}")


if __name__ == "__main__":
    main()

# python test_verify_assembled.py logs/miniF2F-sample --timeout 300