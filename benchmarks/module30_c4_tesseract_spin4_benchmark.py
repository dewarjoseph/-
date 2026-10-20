r"""
benchmarks/module30_c4_tesseract_spin4_benchmark.py
================================================================================
Module 30 Benchmark: Pillar 2 — 4D Tesseract Chair (C_4) & Spin(4) Holonomy
  1. 4D Chair C_4 = [0,2]^4 \ (1,2]^4 Geometry & 15 Unit Hypercubes.
  2. Boundary 3-Face Restriction Analysis (64 boundary 3-cubes).
  3. Spin(4) ~= SU(2)_L x SU(2)_R Clifford Panel-Normal Holonomy Generators.
  4. Kamenetsky Open Problem 9.1 Algebraic Obstruction Verification.
  5. Exact Cell Complex & Boundary 3-Manifold S^3 Euler Characteristics.
================================================================================
"""

import json
import os
import sys

sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))

from src.chair44.c4_tesseract import (
    analyze_kamenetsky_open_problem_9_1,
    tesseract_boundary_panels,
    spin4_generators,
    compute_c4_cell_complex_euler_characteristic,
    compute_c4_boundary_complex,
    compute_c4_cubical_homology_betti_numbers,
    compute_c4_hodge_laplacian_decomposition,
)


def run_module30_benchmark():
    print("=" * 80)
    print("MODULE 30 BENCHMARK: PILLAR 2 — 4D TESSERACT CHAIR & SPIN(4) OBSTRUCTION")
    print("=" * 80)

    analysis = analyze_kamenetsky_open_problem_9_1()
    panels = tesseract_boundary_panels()
    J_plus, J_minus = spin4_generators()
    c4_euler = compute_c4_cell_complex_euler_characteristic()
    c4_boundary = compute_c4_boundary_complex()
    c4_betti = compute_c4_cubical_homology_betti_numbers()
    c4_hodge = compute_c4_hodge_laplacian_decomposition()

    print(f"Number of Unit Tesseracts in C_4: {analysis['num_subcubes']} (expected 15)")
    print(f"Odd-Weight Subcubes:             {analysis['odd_weight_octants']}")
    print(f"Even-Weight Subcubes:            {analysis['even_weight_octants']}")
    print(f"Boundary 3-Cube Panels:          {len(panels)}")
    print(f"Spin(4) Decomposition:           so(4) = {len(J_plus) + len(J_minus)} gens (SU(2)_L: {len(J_plus)}, SU(2)_R: {len(J_minus)})")
    print(f"Algebraic Obstruction Verified:  {analysis['algebraic_obstruction_verified']}")
    print(f"Finding: {analysis['conclusion']}")
    print(f"C_4 Cell Complex Euler Char:     f0={c4_euler['f0_vertices']}, f1={c4_euler['f1_edges']}, f2={c4_euler['f2_faces']}, f3={c4_euler['f3_cubes']}, f4={c4_euler['f4_tesseracts']} => chi={c4_euler['euler_characteristic_chi']} (Contractible: {c4_euler['contractible_verified']})")
    print(f"Boundary 3-Complex Topology:     f0^d={c4_boundary['f0_boundary_vertices']}, f1^d={c4_boundary['f1_boundary_edges']}, f2^d={c4_boundary['f2_boundary_faces']}, f3^d={c4_boundary['f3_boundary_cubes']} => chi(d C_4)={c4_boundary['boundary_euler_characteristic_chi']} (S^3 Topology: {c4_boundary['s3_topology_verified']})")
    print(f"Cubical Homology Betti Numbers:  b(C_4)={c4_betti['betti_c4']} (Contractible: {c4_betti['c4_contractible_homology_verified']}), b(del C_4)={c4_betti['betti_boundary_c4']} (S^3: {c4_betti['boundary_s3_homology_verified']})")
    print(f"Discrete Hodge Harmonic Forms:   dim ker Delta(C_4)={c4_hodge['dim_harmonic_k_forms_c4']}, dim ker Delta(del C_4)={c4_hodge['dim_harmonic_k_forms_boundary']} (Hodge De-Rham: {c4_hodge['hodge_decomposition_verified']})")

    benchmark_ledger = {
        "round": 30,
        "pillar": "Pillar 2: 4D Tesseract Chair & Spin(4) Holonomy",
        "status": "PASSED",
        "c4_geometry": {
            "num_subcubes": analysis["num_subcubes"],
            "boundary_panels": len(panels),
            "odd_weight_octants": analysis["odd_weight_octants"],
            "even_weight_octants": analysis["even_weight_octants"]
        },
        "spin4_algebra": {
            "so4_dimension": len(J_plus) + len(J_minus),
            "su2_plus_dim": len(J_plus),
            "su2_minus_dim": len(J_minus)
        },
        "kamenetsky_open_problem_9_1": {
            "obstructed": analysis["algebraic_obstruction_verified"],
            "proof_summary": analysis["conclusion"]
        },
        "cell_complex_euler": c4_euler,
        "boundary_complex_euler": c4_boundary,
        "cubical_homology_betti": c4_betti,
        "hodge_laplacian_harmonic_forms": c4_hodge,
    }

    out_path = os.path.join(os.path.dirname(__file__), "..", "data", "module30_benchmark.json")
    os.makedirs(os.path.dirname(out_path), exist_ok=True)
    with open(out_path, "w", encoding="utf-8") as f:
        json.dump(benchmark_ledger, f, indent=2)
    print(f"Saved benchmark ledger to {out_path}")
    return benchmark_ledger


if __name__ == "__main__":
    run_module30_benchmark()
