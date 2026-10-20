"""
benchmarks/module30_4d_tesseract_spin4_benchmark.py
================================================================================
Module 30 Frontier Benchmark (Pillar 2):
  4D Tesseract Chair C_4 = [0,2]^4 \ (1,2]^4 Symmetry, Boundary 3-Face Restriction
  Pruning, Coarsening Closure, and Spin(4) ~= SU(2)_L x SU(2)_R Holonomy Analysis
  (Resolving Kamenetsky's Open Problem 9.1).
================================================================================
"""

import json
import os
import sys
import time

sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))

from src.chair44.tesseract_4d import search_4d_coarsening_obstruction, analyze_4d_boundary_faces


def run_module30_benchmark():
    print("=" * 80)
    print("MODULE 30 BENCHMARK: 4D TESSERACT CHAIR & SPIN(4) HOLONOMY ANALYSIS")
    print("=" * 80)
    t0 = time.time()

    faces = analyze_4d_boundary_faces()
    obs_res = search_4d_coarsening_obstruction()

    print(f"4D Tesseract Chair Decomposition:")
    print(f"  Total child tesseracts in C_4:         {obs_res['num_children']} (out of 16 in 2^4)")
    print(f"  Boundary 3-face topological pruning:   {obs_res['chair_face_count']} Chair3 faces, {obs_res['cube_face_count']} Cube3 faces")
    print(f"  Spin(4) ~= SU(2)_L x SU(2)_R Decoupling: max ||[J_L, J_R]|| = {obs_res['spin4_decoupling_norm']:.2e}")
    print(f"  Kamenetsky Open Problem 9.1 Closure:   {obs_res['obstruction_resolved']}")

    results = {
        "round": 30,
        "timestamp": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "elapsed_sec": float(time.time() - t0),
        "boundary_faces": {f"{k[0]}_{k[1]}": v for k, v in faces.items()},
        "obstruction_analysis": obs_res
    }

    os.makedirs("data", exist_ok=True)
    out_file = "data/module30_benchmark.json"
    with open(out_file, "w") as f:
        json.dump(results, f, indent=2)
    print(f"\n[Ledger] Module 30 benchmark ledger written to: {out_file}")
    return results


if __name__ == "__main__":
    run_module30_benchmark()
