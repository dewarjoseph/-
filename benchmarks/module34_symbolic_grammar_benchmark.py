"""
benchmarks/module34_symbolic_grammar_benchmark.py
================================================================================
Pillar 6 (Module 34): Symbolic Epigraphy & Aperiodic Grammar Benchmark.
Evaluates:
  1. Chair44 hierarchical contact grammar: |P_0| = 30 -> |P^*| = 44 and 135 facet triples.
  2. Block entropy superconvergence H_n / n -> 0 for aperiodic substitution words.
  3. Epigraphic restoration comparison (Ithaca/Aeneas deep epigraphy models).
================================================================================
"""

import json
import os
import sys
import numpy as np

sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))

from src.cross_disciplinary.pillar6_epigraphy import execute_pillar6_epigraphy


def run_benchmark():
    print("=" * 80)
    print("MODULE 34 BENCHMARK: APERIODIC GRAMMAR & SYMBOLIC EPIGRAPHY")
    print("=" * 80)

    results = execute_pillar6_epigraphy()

    cg = results["contact_grammar"]
    print("\n[1] Hierarchical Contact Language & Entropy Rates:")
    print(f"  Contact Counts by Level : {cg['contact_language_sizes']}")
    print(f"  Coarsening Closure Size : {cg['coarsening_closure_size']} (Complete |P^*| = 44)")
    print(f"  Facet Triples Count     : {cg['facet_triples_count']}")
    print(f"  Entropy Rates per Token : {[round(r, 4) for r in cg['entropy_rates_per_token']]}")
    print(f"  Superconvergence Ratio  : {cg['superconvergence_rate']:.4f}")
    print(f"  Entropy Decay Verified  : {cg['entropy_decay_verified']}")

    ep = results["epigraphy_comparison"]
    print("\n[2] Neural Epigraphy Model Comparison (Ithaca/Aeneas):")
    print(f"  Grammar Type             : {ep['grammar_type']}")
    print(f"  Epigraphic Comparator    : {ep['epigraphic_comparator']}")
    print(f"  Topological Perplexity   : {ep['topological_perplexity']:.3f}")
    print(f"  Sequence Accuracy        : {ep['sequence_restoration_accuracy']*100:.1f}%")
    print(f"  Grammar Concordance      : {ep['grammar_concordance']}")

    os.makedirs("data", exist_ok=True)
    out_path = "data/module34_benchmark_results.json"
    with open(out_path, "w") as f:
        json.dump(results, f, indent=2, default=lambda o: bool(o) if isinstance(o, (np.bool_, bool)) else (float(o) if isinstance(o, (np.floating, float)) else int(o)))
    print(f"\n[OK] Deterministic ledger written to {out_path}")
    return results


if __name__ == "__main__":
    run_benchmark()
