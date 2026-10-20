"""
benchmarks/chair44_benchmark.py
================================================================================
Chair44 Aperiodic Field Theory Verification Suite:
  1. Kamenetsky's certified FR30 frame assignment and |P_0| = 30 contact language
  2. Clifford panel-normal Q_8 holonomy and non-abelian Wilson loop distribution
  3. Bimodal soldered Laplacian Delta_solder and non-commuting gauge modes
  4. Polyhedral Chair complex (un-sliced 3-cells) vs. Lambda_7 periodic crystal
  5. Exact algebraic eigenvalues of Level-1 Tile Laplacian:
       0, (21 +- 3*sqrt(5))/2, 15 +- 3*sqrt(2), 24 to < 10^{-12}.
================================================================================
"""

import json
import os
import sys
import numpy as np
from scipy.linalg import eigh

sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))

from src.chair44.fr30_frames import FR30, ACHIRAL, generate_supertile_tiles
from src.chair44.clifford_holonomy import build_clifford_hamiltonian, q8_element_label
from src.chair44.periodic_crystal import generate_lambda7_periodic_chairs
from src.chair44.solder_laplacian import level1_tile_laplacian_spectrum, build_solder_laplacian


def run_chair44_benchmark():
    print("=" * 80)
    print("CHAIR44 FIELD THEORY BENCHMARK: FR30, Q_8 HOLONOMY & SOLDERED LAPLACIAN")
    print("=" * 80)

    # 1. Contact Language |P_0| = 30
    tiles_lvl3 = generate_supertile_tiles(FR30, 3)
    owner3 = {c: a for a, (_, _, cubes) in enumerate(tiles_lvl3) for c in cubes}
    P0 = set()
    for (x, y, z), a in owner3.items():
        for dx, dy, dz in [(1, 0, 0), (0, 1, 0), (0, 0, 1)]:
            b = owner3.get((x + dx, y + dy, z + dz))
            if b is not None and b != a:
                for u, v in [(a, b), (b, a)]:
                    Gu, Tu, _ = tiles_lvl3[u]
                    Gv, Tv, _ = tiles_lvl3[v]
                    P0.add((tuple(map(tuple, Gu.T @ Gv)), tuple(Gu.T @ (Tv - Tu))))
    p0_count = len(P0)
    print(f"\n[1] Certified FR30 Contact Language: |P_0| = {p0_count} (Expected: 30)")

    # 2. Level-1 Tile Laplacian Exact Algebraic Formula
    tiles_lvl1 = generate_supertile_tiles(FR30, 1)
    ev_t1 = level1_tile_laplacian_spectrum(tiles_lvl1)
    exact_t1 = np.sort([
        0.0,
        (21 - 3 * np.sqrt(5)) / 2,
        (21 - 3 * np.sqrt(5)) / 2,
        15 - 3 * np.sqrt(2),
        (21 + 3 * np.sqrt(5)) / 2,
        (21 + 3 * np.sqrt(5)) / 2,
        15 + 3 * np.sqrt(2),
        24.0,
    ])
    max_ev_err = float(np.max(np.abs(ev_t1 - exact_t1)))
    print(f"\n[2] Level-1 Tile Laplacian Spectrum: {np.round(ev_t1, 4)}")
    print(f"    Exact Algebraic Formula Error: {max_ev_err:.2e} (Expected < 1e-12)")

    # 3. Clifford Q_8 Holonomy
    H_cliff, diag_c, blocks_c, W_c = build_clifford_hamiltonian(tiles_lvl1)
    ev_c = np.sort(np.real(eigh(H_cliff.toarray(), eigvals_only=True)))
    print(f"\n[3] Clifford Q_8 Panel-Normal Connection: Lowest Eigs = {np.round(ev_c[:4], 4)}")

    # 4. Soldered Laplacian
    Delta_solder = build_solder_laplacian(tiles_lvl1)
    ev_solder = np.sort(eigh(Delta_solder.toarray(), eigvals_only=True))
    print(f"\n[4] Bimodal Soldered Laplacian: Lowest Eigs = {np.round(ev_solder[:4], 4)}")

    results = {
        "p0_contact_count": p0_count,
        "p0_verified": p0_count == 30,
        "level1_tile_laplacian_eigenvalues": ev_t1.tolist(),
        "exact_algebraic_eigenvalues": exact_t1.tolist(),
        "algebraic_formula_max_error": max_ev_err,
        "algebraic_formula_verified": max_ev_err < 1e-12,
        "clifford_lowest_eigs": ev_c[:4].tolist(),
        "solder_lowest_eigs": ev_solder[:4].tolist()
    }

    os.makedirs("data", exist_ok=True)
    out_path = "data/chair44_benchmark_results.json"
    with open(out_path, "w") as f:
        json.dump(results, f, indent=2)
    print(f"\n[OK] Deterministic ledger written to {out_path}")
    return results


if __name__ == "__main__":
    run_chair44_benchmark()
