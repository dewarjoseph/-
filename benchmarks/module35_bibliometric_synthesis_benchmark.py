"""
benchmarks/module35_bibliometric_synthesis_benchmark.py
================================================================================
Pillar 7 (Module 35): Multi-Database Scholarly Bibliometric Synthesis Benchmark.
Evaluates:
  1. Systematic cross-disciplinary citation database (9 key DOI/arXiv references).
  2. Quantitative comparative literature matrix benchmarking our discoveries across all 7 pillars.
================================================================================
"""

import json
import os
import sys

sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))

from src.cross_disciplinary.pillar7_bibliometrics import execute_pillar7_bibliometrics


def run_benchmark():
    print("=" * 80)
    print("MODULE 35 BENCHMARK: MULTI-DATABASE SCHOLARLY BIBLIOMETRICS")
    print("=" * 80)

    results = execute_pillar7_bibliometrics()

    print(f"\n[1] Verified Cross-Disciplinary Bibliography ({results['citation_count']} citations):")
    for cit in results["bibliography"]:
        ref = cit.get("doi") or cit.get("eprint")
        print(f"  [{cit['key']}] Pillar {cit['pillar']}: {cit['title']} ({cit['year']}) -> {ref}")

    print("\n[2] Quantitative Comparative Literature Matrix (7 Pillars):")
    for row in results["comparative_matrix"]:
        print(f"  Pillar {row['pillar']} ({row['domain']:30s}): {row['metric']:28s} | Prior Art: {row['prior_art']:25s} | Our Work: {row['our_work']:28s} | Gain: {row['gain']}")

    print(f"\n  Pillar 7 Synthesis Verified: {results['pillar7_passed']}")

    os.makedirs("data", exist_ok=True)
    out_path = "data/module35_benchmark_results.json"
    with open(out_path, "w") as f:
        json.dump(results, f, indent=2)
    print(f"\n[OK] Deterministic ledger written to {out_path}")
    return results


if __name__ == "__main__":
    run_benchmark()
