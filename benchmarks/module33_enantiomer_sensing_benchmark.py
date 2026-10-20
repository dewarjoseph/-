"""
benchmarks/module33_enantiomer_sensing_benchmark.py
================================================================================
Pillar 5 (Module 33): Chiral Photonic Enantiomer Sensing & Homochirality Benchmark.
Evaluates:
  1. 6.74x HONHSE corner enhancement of optical chirality density C_opt.
  2. Enantioselective discrimination of PubChem/ChEMBL pharmaceuticals (alanine, thalidomide, ibuprofen).
  3. Graph-Laplacian spectral chirality audit on STRING/Reactome networks.
================================================================================
"""

import json
import os
import sys

sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))

from src.cross_disciplinary.pillar5_photonic_sensing import execute_pillar5_sensing


def run_benchmark():
    print("=" * 80)
    print("MODULE 33 BENCHMARK: CHIRAL PHOTONIC ENANTIOMER SENSING")
    print("=" * 80)

    results = execute_pillar5_sensing()

    opt = results["optical_chirality"]
    print("\n[1] Near-Field Optical Chirality Density C_opt:")
    print(f"  Base Plane Wave C_0        : {opt['base_chirality_density_C0']:.4e} J/(m^3 s)")
    print(f"  HONHSE Corner Hotspot C_opt: {opt['corner_enhanced_C_opt']:.4e} J/(m^3 s)")
    print(f"  Field Gradient Enhancement : {opt['corner_linear_gain']:.2f}x (Intensity gain: {opt['enhancement_factor']:.2f}x)")

    enant = results["enantiomeric_sensing"]
    print("\n[2] PubChem/ChEMBL Pharmaceutical Enantiomeric Discrimination:")
    for mol, data in enant["enantiomeric_pairs"].items():
        print(f"  {mol.capitalize():12s}: Keys={list(data.keys())}")
    print(f"  Enhanced Kuhn Dissymmetry Factor g_CD : {enant['quasicrystal_enhanced_g']:.4e} (Base: {enant['base_kuhn_dissymmetry_factor_g']:.4e})")
    print(f"  Enantiomeric Discrimination Boost     : {enant['enantiomer_discrimination_ratio']:.2f}x")
    print(f"  Purity Detection Threshold            : {enant['enantioselective_purity_limit_ppm']:.1f} ppm")

    net = results["network_chirality"]
    print("\n[3] STRING / Reactome Biological Network Chirality:")
    print(f"  Pathways Analyzed : {net['pathway_target']}")
    print(f"  Directed Chirality: {net['network_directed_chirality_index']:.3f} (p-value: {net['homochirality_bias_p_value']:.2e})")
    print(f"  Audit Status      : {net['audit_status']}")

    os.makedirs("data", exist_ok=True)
    out_path = "data/module33_benchmark_results.json"
    with open(out_path, "w") as f:
        json.dump(results, f, indent=2)
    print(f"\n[OK] Deterministic ledger written to {out_path}")
    return results


if __name__ == "__main__":
    run_benchmark()
