"""
benchmarks/module33_photonic_enantiomer_sensing_benchmark.py
================================================================================
Module 33 Frontier Benchmark (Pillar 5):
  Chiral Photonic Enantiomer Sensing, Near-Field Optical Chirality Density C_opt,
  and Molecular Homochirality Discrimination for PubChem / ChEMBL Bioactive Compounds.
================================================================================
"""

import json
import os
import sys
import time

sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))

from src.cross_disciplinary.enantiomer_sensing import evaluate_enantiomer_discrimination_hotspots


def run_module33_benchmark():
    print("=" * 80)
    print("MODULE 33 BENCHMARK: CHIRAL PHOTONIC ENANTIOMER SENSING (PUBCHEM / CHEMBL)")
    print("=" * 80)
    t0 = time.time()

    res = evaluate_enantiomer_discrimination_hotspots(corner_amplification=6.74, cd_signal=-0.472)

    print(f"HONHSE Corner Hotspot Chiral Enhancement:")
    print(f"  Codimension-2 Corner Amplification:    {res['corner_amplification']:.2f}x")
    print(f"  Effective Near-Field Optical Chirality Boost: {res['enhancement_factor']:.2f}x")
    print(f"\nPubChem Bioactive Enantiomer Discrimination:")
    for cmpd in res["compounds"]:
        print(f"  - {cmpd['name']} (R: CID {cmpd['r_cid']} vs. S: CID {cmpd['s_cid']}):")
        print(f"      Baseline Dissymmetry g0:           {cmpd['g0_baseline']:.2e}")
        print(f"      Corner-Enhanced Dissymmetry g_enh: {cmpd['g_enhanced']:.4f}")
        print(f"      Contrast Ratio:                    {cmpd['enantioselective_contrast']:.1f}x")
    print(f"\nSub-Picomolar Chiral Discrimination Feasibility: {res['sub_picomolar_sensing_achieved']}")

    results = {
        "round": 33,
        "timestamp": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "elapsed_sec": float(time.time() - t0),
        "enantiomer_sensing": res
    }

    os.makedirs("data", exist_ok=True)
    out_file = "data/module33_benchmark.json"
    with open(out_file, "w") as f:
        json.dump(results, f, indent=2)
    print(f"\n[Ledger] Module 33 benchmark ledger written to: {out_file}")
    return results


if __name__ == "__main__":
    run_module33_benchmark()
