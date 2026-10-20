"""
benchmarks/module29_wigner_smith_transient_benchmark.py
================================================================================
Module 29 Frontier Benchmark (Pillar 1):
  Wigner-Smith Time-Delay Matrix Q_WS(omega), Broadband Astrophysical Transient
  Group-Delay Splitting Delta tau_g, and Cosmic Birefringence Spectrum C_ell.
================================================================================
"""

import json
import os
import sys
import time
import numpy as np

sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))

from src.icosahedral_qc.floquet_cosmology import (
    compute_wigner_smith_time_delay,
    compute_cosmological_birefringence_spectrum,
    compute_floquet_phasonic_pumping,
)


def run_module29_benchmark():
    print("=" * 80)
    print("MODULE 29 BENCHMARK: WIGNER-SMITH TRANSIENT SCALING & COSMIC BIREFRINGENCE")
    print("=" * 80)
    t0 = time.time()

    # Universal continuous chiral bispectrum limit chi_b(infinity) = 0.001767
    chi_b_inf = 0.001767
    omega_vals = np.linspace(0.1, 5.0, 50)

    ws_res = compute_wigner_smith_time_delay(omega_vals, chi_b_inf)
    biref_res = compute_cosmological_birefringence_spectrum(ell_max=100)
    floquet_res = compute_floquet_phasonic_pumping()

    print(f"Wigner-Smith Time Delay Analysis (N={len(omega_vals)} frequencies):")
    print(f"  Mean Group-Delay Splitting Delta tau_g: {ws_res['mean_delta_tau']:.6e} s")
    print(f"  Scaling Factor Delta tau_g / chi_b:    {ws_res['scaling_factor']:.4f}")
    print(f"\nCosmological Birefringence Power Spectrum C_ell ~ ell^-2:")
    print(f"  Total Variance (ell = 2..100):         {biref_res['total_variance']:.4f}")
    print(f"\nFloquet-Phasonic Synthetic Magnetogenesis:")
    print(f"  Floquet Sideband Dichroism CD_pm2:     {floquet_res['CD_pm2'] * 100:.1f}%")
    print(f"  Synthetic Peierls Flux Phi_B:          {floquet_res['phi_b']:.4f}")
    print(f"  Axial Orbital Dipole m_z:              {floquet_res['m_z']:.4f}")

    results = {
        "round": 29,
        "timestamp": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "elapsed_sec": float(time.time() - t0),
        "wigner_smith": ws_res,
        "cosmic_birefringence": biref_res,
        "floquet_pumping": floquet_res,
    }

    os.makedirs("data", exist_ok=True)
    out_file = "data/module29_benchmark.json"
    with open(out_file, "w") as f:
        json.dump(results, f, indent=2)
    print(f"\n[Ledger] Module 29 benchmark ledger written to: {out_file}")
    return results


if __name__ == "__main__":
    run_module29_benchmark()
