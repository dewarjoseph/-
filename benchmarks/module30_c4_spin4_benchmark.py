r"""
benchmarks/module30_c4_spin4_benchmark.py
================================================================================
Pillar 2 (Module 30): 4D Tesseract Chair (C_4) & Spin(4) Holonomy Benchmark.
Evaluates:
  1. Geometric structure of C_4 = [0,2]^4 \ (1,2]^4 (15 sub-tesseracts).
  2. Boundary 3-cube restriction and Spin(4) ~= SU(2)_L x SU(2)_R holonomy.
  3. Kamenetsky Open Problem 9.1 proof: algebraic obstruction to homochiral frame closure.
================================================================================
"""

import json
import os
import sys

sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))

from src.cross_disciplinary.pillar2_spin4_tesseract import execute_pillar2_open_problem_proof


def run_benchmark():
    print("=" * 80)
    print("MODULE 30 BENCHMARK: 4D TESSERACT CHAIR & SPIN(4) HOLONOMY")
    print("=" * 80)

    results = execute_pillar2_open_problem_proof()

    obs = results["obstruction_details"]
    print("\n[1] 4D Tesseract Chair (C_4) Geometry:")
    print(f"  Sub-tesseracts count: {obs['num_subcubes']} (15 unit 4-cubes)")
    print(f"  Odd-weight octants  : {obs['odd_weight_octants']}, Even-weight: {obs['even_weight_octants']}")
    print(f"  Boundary 3-cube faces: {obs['boundary_3cubes']}")

    spin4 = results["spin4_holonomy"]
    print("\n[2] Spin(4) ~= SU(2)_L x SU(2)_R Decomposition:")
    print(f"  so(4) Lie algebra dimension : {obs['so4_dim']}")
    print(f"  SU(2)_L (self-dual) dim    : {obs['su2_plus_dim']}")
    print(f"  SU(2)_R (anti-self-dual) dim: {obs['su2_minus_dim']}")
    print(f"  Sample Tr_L holonomies      : {spin4['sample_tr_L']}")
    print(f"  Sample Tr_R holonomies      : {spin4['sample_tr_R']}")

    print("\n[3] Kamenetsky Open Problem 9.1 Resolution:")
    print(f"  Resolution Status: {results['open_problem_9_1_resolution']}")
    print(f"  Conclusion       : {obs['conclusion']}")
    print(f"  Pillar 2 Passed  : {results['pillar2_passed']}")

    os.makedirs("data", exist_ok=True)
    out_path = "data/module30_benchmark_results.json"
    with open(out_path, "w") as f:
        json.dump(results, f, indent=2)
    print(f"\n[OK] Deterministic ledger written to {out_path}")
    return results


if __name__ == "__main__":
    run_benchmark()
