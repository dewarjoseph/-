"""
benchmarks/module29_transient_scaling_benchmark.py
================================================================================
Pillar 1 (Module 29): Large-Scale Thermodynamic & Wigner-Smith Transient Scaling.
Evaluates:
  1. Patch scaling for R = 18, 20.
  2. Wigner-Smith group delay splitting Delta_tau_g for FRBs and pulsars.
  3. Scale-invariant birefringence power spectrum C_ell^{alpha alpha} propto ell^{-2}.
================================================================================
"""

import json
import os
import sys

sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))

from src.cross_disciplinary.pillar1_transients import execute_pillar1_scaling


def run_benchmark():
    print("=" * 80)
    print("MODULE 29 BENCHMARK: THERMODYNAMIC SCALING & WIGNER-SMITH TRANSIENTS")
    print("=" * 80)

    results = execute_pillar1_scaling()

    print("\n[1] Thermodynamic Cut-and-Project Scaling:")
    for k, v in results["thermodynamic_scaling"].items():
        print(f"  {k} : Sites={v['estimated_sites']} | chi_b={v['chi_b_converged']} | D_lap={v['D_lap_converged']} | Ratio={v['ratio']:.4f}")

    print("\n[2] Wigner-Smith Group Delay Splitting:")
    ws = results["wigner_smith"]
    print(f"  tau_g^+ Mean={ws['tau_plus_mean']:.4f}, tau_g^- Mean={ws['tau_minus_mean']:.4f}")
    print(f"  Group Delay Splitting Max={ws['max_group_delay_splitting']:.4e} (FRB dispersion metric)")

    print("\n[3] Scale-Invariant Birefringence Power Spectrum:")
    cl = results["birefringence_spectrum"]
    print(f"  Fitted Power-Law Slope: {cl['spectral_index']:.4f} (Expected: -2.0000)")
    print(f"  Scale-Invariance Verified: {cl['scale_invariant_verified']}")

    os.makedirs("data", exist_ok=True)
    out_path = "data/module29_benchmark_results.json"
    with open(out_path, "w") as f:
        json.dump(results, f, indent=2)
    print(f"\n[OK] Deterministic ledger written to {out_path}")
    return results


if __name__ == "__main__":
    run_benchmark()
