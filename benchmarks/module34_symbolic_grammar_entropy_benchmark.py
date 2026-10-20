"""
benchmarks/module34_symbolic_grammar_entropy_benchmark.py
================================================================================
Module 34 Frontier Benchmark (Pillar 6):
  Symbolic Epigraphy & Aperiodic Sequence Grammar: Contact Language
  |P_0| = 30 -> |P*| = 44, 135 Facet Triples, and n-Gram Topological Entropy
  Superconvergence (Zaporski & Flicker 2019).
================================================================================
"""

import json
import os
import sys
import time

sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))

from src.cross_disciplinary.symbolic_grammar import (
    compute_ngram_entropy_superconvergence,
    analyze_chair44_contact_grammar,
)


def run_module34_benchmark():
    print("=" * 80)
    print("MODULE 34 BENCHMARK: SYMBOLIC EPIGRAPHY & ENTROPY SUPERCONVERGENCE")
    print("=" * 80)
    t0 = time.time()

    ent_res = compute_ngram_entropy_superconvergence(max_n=10)
    gram_res = analyze_chair44_contact_grammar()

    print(f"Chair44 Hierarchical Contact Language:")
    print(f"  Raw Chair-Chair Meeting Combinations:  {gram_res['raw_chair_contacts']}")
    print(f"  Arrow Matching Rules Admissible |P*|:  {gram_res['chair44_arrow_contacts']}")
    print(f"  Realized in Infinite Tilings |P_0|:    {gram_res['infinite_tiling_contacts']}")
    print(f"  Legal Facet Triples F*:                {gram_res['facet_triples']}")
    print(f"  Valid 2-Shell Superchair Clusters:     {gram_res['valid_two_shell_clusters']} (out of {gram_res['single_shell_clusters']})")
    print(f"\nTopological Entropy Superconvergence (Zaporski & Flicker 2019):")
    print(f"  Asymptotic Entropy h_infinity:         {ent_res['h_infinity']:.4f} bits")
    print(f"  Fitted Power-Law Exponent gamma:       {ent_res['fitted_gamma']:.4f} (h(n) ~ n^-gamma)")
    print(f"  Superconvergence Certified (gamma>=1.95): {ent_res['superconvergent']}")

    results = {
        "round": 34,
        "timestamp": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "elapsed_sec": float(time.time() - t0),
        "entropy_superconvergence": ent_res,
        "contact_grammar": gram_res,
    }

    os.makedirs("data", exist_ok=True)
    out_file = "data/module34_benchmark.json"
    with open(out_file, "w") as f:
        json.dump(results, f, indent=2)
    print(f"\n[Ledger] Module 34 benchmark ledger written to: {out_file}")
    return results


if __name__ == "__main__":
    run_module34_benchmark()
