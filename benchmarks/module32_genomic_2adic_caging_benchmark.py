"""
benchmarks/module32_genomic_2adic_caging_benchmark.py
================================================================================
Module 32 Frontier Benchmark (Pillar 4):
  2-Adic DNA Brick Self-Assembly, Chromatin Polymer Caging, and Hodge-Laplacian
  Spectral Gap Analysis with JASPAR CTCF Motifs and ENCODE cCRE Architecture.
================================================================================
"""

import json
import os
import sys
import time

sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))

from src.cross_disciplinary.genomic_topology import (
    compute_2adic_dna_brick_caging,
    analyze_chromatin_ctcf_caging,
)


def run_module32_benchmark():
    print("=" * 80)
    print("MODULE 32 BENCHMARK: 2-ADIC GENOMIC TOPOLOGY & DNA BRICK CAGING")
    print("=" * 80)
    t0 = time.time()

    dna_res = compute_2adic_dna_brick_caging(hierarchy_levels=4)
    ctcf_res = analyze_chromatin_ctcf_caging()

    print(f"2-Adic DNA Brick Polyhedral Hodge Caging:")
    print(f"  Levels Analyzed:                       {dna_res['levels']}")
    print(f"  Hodge-Laplacian Caging Gaps Delta_2:   {[round(g, 4) for g in dna_res['hodge_caging_gaps']]}")
    print(f"  Topological Caging Ratios Delta_2/Delta_0: {[round(r, 1) for r in dna_res['topological_caging_ratios']]}")
    print(f"\nJASPAR Architectural Motif Integration:")
    print(f"  Factor Name:                           {ctcf_res['factor_name']} (JASPAR ID: {ctcf_res['jaspar_id']})")
    print(f"  Motif Length:                          {ctcf_res['motif_length']} bp")
    print(f"  Positional Information Content:        {ctcf_res['information_content_bits']:.1f} bits")
    print(f"  Boundary Insulation Efficiency:        {ctcf_res['caging_efficiency'] * 100:.1f}%")

    results = {
        "round": 32,
        "timestamp": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "elapsed_sec": float(time.time() - t0),
        "dna_brick_caging": dna_res,
        "ctcf_chromatin_caging": ctcf_res,
    }

    os.makedirs("data", exist_ok=True)
    out_file = "data/module32_benchmark.json"
    with open(out_file, "w") as f:
        json.dump(results, f, indent=2)
    print(f"\n[Ledger] Module 32 benchmark ledger written to: {out_file}")
    return results


if __name__ == "__main__":
    run_module32_benchmark()
