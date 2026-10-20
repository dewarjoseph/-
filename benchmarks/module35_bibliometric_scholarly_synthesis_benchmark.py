"""
benchmarks/module35_bibliometric_scholarly_synthesis_benchmark.py
================================================================================
Module 35 Frontier Benchmark (Pillar 7):
  Multi-Database Scholarly Bibliometric Synthesis Across arXiv, OpenAlex,
  EuropePMC, and PubMed with Quantitative Cross-Disciplinary Citation Matrix.
================================================================================
"""

import json
import os
import sys
import time

sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))

from src.cross_disciplinary.bibliometrics import generate_bibliometric_summary


def run_module35_benchmark():
    print("=" * 80)
    print("MODULE 35 BENCHMARK: MULTI-DATABASE SCHOLARLY BIBLIOMETRICS SYNTHESIS")
    print("=" * 80)
    t0 = time.time()

    summary = generate_bibliometric_summary()

    print(f"Scholarly Citation & Knowledgebase Synthesis:")
    print(f"  Primary Reference Manuscripts:         {summary['num_reference_works']}")
    print(f"  Aggregated Scholarly Citations:        {summary['total_citations']}")
    print(f"  Cross-Disciplinary Pillars Covered:    {len(summary['pillars_covered'])}")
    for p in summary["pillars_covered"]:
        print(f"    - {p}")
    print(f"\nFeatured Works in Cross-Disciplinary Corpus:")
    for ref in summary["references"][:4]:
        print(f"  [{ref['key']}] {ref['title']} ({ref['authors']}, {ref['year']}) -- {ref['venue']} [DOI: {ref['doi']}]")

    results = {
        "round": 35,
        "timestamp": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "elapsed_sec": float(time.time() - t0),
        "bibliometrics": summary
    }

    os.makedirs("data", exist_ok=True)
    out_file = "data/module35_benchmark.json"
    with open(out_file, "w") as f:
        json.dump(results, f, indent=2)
    print(f"\n[Ledger] Module 35 benchmark ledger written to: {out_file}")
    return results


if __name__ == "__main__":
    run_module35_benchmark()
