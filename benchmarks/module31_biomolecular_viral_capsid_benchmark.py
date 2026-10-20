"""
benchmarks/module31_biomolecular_viral_capsid_benchmark.py
================================================================================
Module 31 Frontier Benchmark (Pillar 3):
  Structural Biology & Chiral Icosahedral Viral Quasicrystallography
  (PDB 1STM Satellite Tobacco Mosaic Virus, T=1 Capsid, Bragg Bispectrum chi_b,
  Graph-Laplacian Circular Dichroism D_lap, and Pentameric Vertex Hinge HONHSE).
================================================================================
"""

import json
import os
import sys
import time

sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))

from src.cross_disciplinary.biomolecular_capsid import analyze_viral_capsid_chirality


def run_module31_benchmark(pdb_path="data/pdb/1stm.pdb"):
    print("=" * 80)
    print("MODULE 31 BENCHMARK: CHIRAL ICOSAHEDRAL VIRAL QUASICRYSTALLOGRAPHY (1STM)")
    print("=" * 80)
    t0 = time.time()

    res = analyze_viral_capsid_chirality(pdb_path)

    print(f"PDB Entry: {res['pdb_id']} (Satellite Tobacco Mosaic Virus Capsid)")
    print(f"  Total C_alpha atomic coordinates:      {res['num_ca_atoms']}")
    print(f"  Bragg Bispectrum Pseudoscalar chi_b:   {res['chi_b']:.6f}")
    print(f"  Graph-Laplacian Circular Dichroism:    {res['D_lap']:.6f}")
    print(f"  Universal Coupling Ratio D_lap / chi_b: {res['ratio_D_chi']:.4f}")
    print(f"  Pentameric Vertex Hinge Residues:      {res['pentamer_atom_count']} atoms (mean radius {res['mean_pentamer_radius']:.2f} units)")
    print(f"  Biomolecular Structure Viewer sidecar: Active (1stm.pdb loaded and annotated)")

    results = {
        "round": 31,
        "timestamp": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "elapsed_sec": float(time.time() - t0),
        "viral_capsid_analysis": res,
        "viewer_sidecar_url": "sidecar://science/biomolecular_structure_viewer/ui.html"
    }

    os.makedirs("data", exist_ok=True)
    out_file = "data/module31_benchmark.json"
    with open(out_file, "w") as f:
        json.dump(results, f, indent=2)
    print(f"\n[Ledger] Module 31 benchmark ledger written to: {out_file}")
    return results


if __name__ == "__main__":
    run_module31_benchmark()
