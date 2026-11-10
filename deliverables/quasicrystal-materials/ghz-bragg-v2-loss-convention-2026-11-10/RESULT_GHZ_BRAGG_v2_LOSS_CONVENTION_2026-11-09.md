# RESULT — GHz Bragg v2 loss-convention addendum (C1: M → M(1 + i eta))

Quasicrystal Materials, 2026-11-09 PT (America/Los_Angeles), original run 10:37 PM PT.
This file is a header-redacted, path-stripped public copy of that result note, revised
on 2026-11-10 PT (revision 3: provenance wording, and one descriptive sentence).
The runner in this folder was re-executed on 2026-11-10 PT with python3 -I, numpy only, CPU only; scientific numbers reproduced exactly against the original results JSON sha256 1e65984a68dffbf015c16e68daf9e87da831d55b50f5b14f8c1f4ce566ecdda2 (see MANIFEST.sha256).
Labels [P]/[C]/[E]/[X]/[A]/[F]. Runtime < 1 s.

## Pins (rehashed by the runner, which refuses on mismatch; all MATCH before and after)

- Addendum in this folder (a 2026-11-10 redaction and paraphrase of the text frozen before any addendum number): PREREG_GHZ_BRAGG_v2_ADDENDUM_LOSS_CONVENTION_2026-11-09.md
  sha256 d4e473db20d57eeb33c98bcb54d89fc84713687905dfd0246793b7d4ce54f96f
  Original unedited addendum (not in this folder) sha256 f4467b54c82a17255958e143d3d327ff33914e2025bc9439926635e49a1fea24
- Parent v2 prereg (cited, not reproduced in this folder): PREREG_GHZ_BRAGG_v2_2026-11-09.md sha256 33338a45bea89082d89601d02ed87814273a7833d5a908eb664b25702f991e36
- eta = 0 baselines (derived file, two T(f0) values only; not a v2 verdict): eta0_baselines.json
  sha256 5e8bc5fb11246573ee897faaaa634d95e6b5461921d93fd5aac4fee462e1edd3
  Taken from the original v2 results JSON sha256 6475ff5ab93536678ec80d8408aa105c17e3c66a5972c2868f5cdbb2702da892, which is not reproduced in this folder.
- Not edited: v2 runner 8e562b7167f7fa729d9e2aa79859ee73456f1592b8b50a60e4d801c956b21436;
  v2 result note a36c34605df555f0b3aa72dae19ddb3a1bc6c8fd31051c929d69dcd408532a92.

## Artifacts (this folder)

- Runner: ghz_bragg_v2_loss_convention_run.py sha256 8f31454b2fddb1eefd42dbdc85b3fb968e54349b498454761937fbf7e1ea5a09
- Results: results_ghz_bragg_v2_loss_convention.json sha256 39b8a8345d0b8e4156ea14158a0ffe2047d7dfd2d50a73dd16dad3736150038b
  Original unedited results JSON (not in this folder) sha256 1e65984a68dffbf015c16e68daf9e87da831d55b50f5b14f8c1f4ce566ecdda2
  The two JSON files differ only in the pins block (relative paths, the redacted addendum hash, the derived baseline pin, and a cited parent-prereg record) and in the eta=0 baseline field names inside hypotheses. Every scientific field matches exactly.

Runner = v2 TR copied verbatim with one change: v_c = v·sqrt(1 + i eta) (principal root) in W and SiO2.
Transfer-matrix +i off-diagonals, r/t algebra, R = |r|², T = |t|², lossless Si half-spaces unchanged.
Those +i off-diagonals are the e^{+i ω t} time-harmonic convention (fields ~ e^{i ω t − i k x}), as stated in the addendum.
Not re-run: eta = 0, V2, V3. Cases: eta ∈ {1e-4, 1e-3, 1e-2} [A] × {PER21_tau, FIB21_tau, PER13_tau, FIB13_tau},
main grid 0.05–6.5 GHz N = 20001, plus f0 = 2 GHz and 2 f0. Same words and tau thicknesses as v2
(d_A = 848.24 nm W, d_B = 524.24 nm SiO2, ratio tau). Materials and eta [A].

## Validations [E]

V_L0 (single W layer d_A = 8.4824e-7 m in lossless Si, eta = 1e-3): min A_abs = +9.97e-6 (≥ −1e-10),
A_abs(f0) = +1.094e-3 (> 0), max T 0.99167, max R 0.85888. **PASS.** The sign is now dissipative.

V_L (main grid, floor 1e-10): **PASS for all 12 eta/stack cases**; no voiding failure, no untrusted case.

| eta | stack | min A_abs | A_abs(f0) | max A_abs | max T | max R |
|---|---|---|---|---|---|---|
| 1e-4 | PER21_tau | 5.912e-5 | 1.208e-4 | 0.3383 | 0.99957 | 0.99994 |
| 1e-4 | FIB21_tau | 5.585e-5 | 1.241e-4 | 0.7741 | 0.99834 | 0.99994 |
| 1e-4 | PER13_tau | 3.953e-5 | 1.208e-4 | 0.1304 | 0.99956 | 0.99994 |
| 1e-4 | FIB13_tau | 3.495e-5 | 1.241e-4 | 0.1106 | 0.99858 | 0.99994 |
| 1e-3 | PER21_tau | 5.910e-4 | 1.207e-3 | 0.5303 | 0.99572 | 0.99941 |
| 1e-3 | FIB21_tau | 5.583e-4 | 1.240e-3 | 0.9815 | 0.99400 | 0.99944 |
| 1e-3 | PER13_tau | 3.952e-4 | 1.207e-3 | 0.4998 | 0.99572 | 0.99941 |
| 1e-3 | FIB13_tau | 3.494e-4 | 1.240e-3 | 0.6334 | 0.98725 | 0.99944 |
| 1e-2 | PER21_tau | 5.894e-3 | 1.201e-2 | 0.9134 | 0.95831 | 0.99411 |
| 1e-2 | FIB21_tau | 5.569e-3 | 1.233e-2 | 0.9563 | 0.95192 | 0.99443 |
| 1e-2 | PER13_tau | 3.940e-3 | 1.201e-2 | 0.7790 | 0.95831 | 0.99411 |
| 1e-2 | FIB13_tau | 3.486e-3 | 1.233e-2 | 0.8906 | 0.94157 | 0.99443 |

All min R, min T ≥ 0 (min T ~1e-17 for PER21_tau). Full values in the JSON.

**The v2 unphysical behaviour is gone [E].** v2 (gain sign, untrusted) had A_abs < 0 everywhere
(e.g. FIB21_tau A_abs(f0) −1.241e-3, max A_abs on grid −5.59e-4 at eta 1e-3) and T > 1
(FIB21_tau T_peak(B0) 16.939 at eta 1e-3; FIB13_tau 1.608). Under C1: A_abs(f0) = +1.240e-3,
min A_abs > 0 everywhere, max T ≤ 0.9996 in every case.

## Hypotheses (eta = 0 baselines from eta0_baselines.json: FIB21_tau T(f0) = 1.4983e-13, PER21_tau T(f0) = 1.0877e-17 → FIB>PER)

- **H7 (eta = 1e-3): PASS [E].** FIB21_tau T(f0) = 1.4964e-13, PER21_tau T(f0) = 1.0863e-17; FIB>PER, same direction as eta = 0 (ratio ≈ 1.38e4).
- **H8 (eta = 1e-2): PASS [E].** FIB21_tau T(f0) = 1.4744e-13, PER21_tau T(f0) = 1.0719e-17; FIB>PER, same direction (ratio ≈ 1.38e4).

Meaning: the eta = 0 ordering (tau-Fibonacci transmits MORE than tau-periodic at f0) does not
reverse at the sampled [A] values eta = 1e-3 (H7) and eta = 1e-2 (H8); eta = 1e-4 is reported
descriptively only. H7/H8 PASS is stability of a ranking that disfavours Fibonacci;
it is not isolator-advantage evidence. FIB13_tau / PER13_tau are size checks, not scored.
The v2 runner's H7/H8 PASS marks remain withdrawn; these addendum scores replace them.

**Isolator advantage: FAIL [F]** (from the eta = 0 score already recorded in the v2 result note, sha256 a36c3460…; unchanged). This addendum adds no new overall mark.
H1–H6 not reopened.

## Descriptive (not scored, not advantage evidence) [E]

| eta | stack | T(f0) | T(2f0) | T_peak(B0) | S(B0) dB | f0 band (GHz, T<1e-2, ≥5 MHz) | A_abs(f0) | max A_abs |
|---|---|---|---|---|---|---|---|---|
| 1e-4 | PER21_tau | 1.0875e-17 | 2.574e-16 | 3.021e-15 | 145.20 | 0.911075–2.8315625 | 1.208e-4 | 0.3383 |
| 1e-4 | FIB21_tau | 1.4981e-13 | 2.477e-13 | 0.18964 | 7.22 | 1.64444–2.9031575 | 1.241e-4 | 0.7741 |
| 1e-3 | PER21_tau | 1.0863e-17 | 2.569e-16 | 3.013e-15 | 145.21 | 0.911075–2.831885 | 1.207e-3 | 0.5303 |
| 1e-3 | FIB21_tau | 1.4964e-13 | 2.471e-13 | 0.04853 | 13.14 | 1.6441175–2.90348 | 1.240e-3 | 0.9815 |
| 1e-2 | PER21_tau | 1.0719e-17 | 2.495e-16 | 2.915e-15 | 145.35 | 0.90914–2.84543 | 1.201e-2 | 0.9134 |
| 1e-2 | FIB21_tau | 1.4744e-13 | 2.381e-13 | 2.145e-4 | 36.68 | 0.7649825–2.914445 | 1.233e-2 | 0.9563 |

In words: PER21_tau's f0 band and T(f0) barely move with eta. FIB21_tau's f0 band is close to
v2 eta = 0 (1.7112–2.9028 GHz) and widens downward as eta grows; its B0 peak (a transmission resonance
below the band edge, 0.2368 at eta = 0 in v2) is damped by absorption (0.190 → 0.049 → 2.1e-4), not by
a new gap.
Compared with the untrusted v2 lossy spectra: T(f0) values are near-identical (they are dominated by the
evanescent stop band), while v2's B0 peaks and A_abs signs were gain artefacts.

## Issues / notes

- The very small T(f0) values (~1e-13, ~1e-17) are computed directly as |t|² and are not limited by the
  1 − R cancellation; the ranking has ~4 orders of margin. [E]

## Scope (scientific limits, unchanged; wording redacted from the frozen addendum)

1D transfer-matrix model of tau-thickness W/SiO2 stacks on Si, normal incidence, longitudinal only.
Not a measured specimen and not a 3D model.
TLS stays [X] and is not modelled. Infima stay [X]. Not evidence about measured films.
