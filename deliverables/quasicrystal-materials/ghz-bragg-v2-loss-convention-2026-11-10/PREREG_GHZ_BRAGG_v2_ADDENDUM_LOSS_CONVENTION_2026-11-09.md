# PREREG_GHZ_BRAGG_v2 ADDENDUM: loss-convention and passivity check

Quasicrystal Materials, 2026-11-09 PT (America/Los_Angeles). The original
addendum was written and frozen BEFORE any addendum numerics
(sha256 f4467b54c82a17255958e143d3d327ff33914e2025bc9439926635e49a1fea24;
that file is not edited). These public-copy bytes are a 2026-11-10
redaction and paraphrase of that frozen text. The runner in this folder
pins the sha256 of these redacted-and-paraphrased bytes.
Labels [P]/[C]/[E]/[X]/[A]/[F]. python3 -I, numpy only. CPU only.

This is an addendum to the parent preregistration
PREREG_GHZ_BRAGG_v2_2026-11-09.md, cited only by
sha256 33338a45bea89082d89601d02ed87814273a7833d5a908eb664b25702f991e36
and not reproduced here. That file is not edited. The eta = 0
isolator-advantage FAIL [F], and H1–H6 as scored in
RESULT_GHZ_BRAGG_v2_2026-11-09.md
sha256 a36c34605df555f0b3aa72dae19ddb3a1bc6c8fd31051c929d69dcd408532a92,
stand. This addendum rescues only the lossy ranking claims H7 and H8.

## Why this addendum exists

The frozen v2 runner
ghz_bragg_v2_run.py
sha256 8e562b7167f7fa729d9e2aa79859ee73456f1592b8b50a60e4d801c956b21436
implemented the layer modulus replacement
M → M(1 − i eta), with v_c = v * sqrt(1 − i eta) (principal square root),
z = rho v_c, and k = 2 π f / v_c, inside the same 2x2 pressure/velocity
transfer matrix already used at eta = 0, whose off-diagonal factors are +i
(a12 = i z sin(kd), a21 = i sin(kd)/z). That matrix is the e^{+i ω t}
time-harmonic convention (fields ~ e^{i ω t − i k x}).

Under that convention, a passive (dissipative) layer must have Im(k) < 0
in the forward direction, which requires Im(v_c) > 0, i.e.
M → M(1 + i eta) and v_c = v * sqrt(1 + i eta). The v2 sign
M(1 − i eta) is therefore a gain convention, not a loss convention, when
paired with that matrix.

This diagnosis uses only numbers already recorded in the frozen v2 result
note and in the original v2 results JSON
sha256 6475ff5ab93536678ec80d8408aa105c17e3c66a5972c2868f5cdbb2702da892
(that JSON is not reproduced in this folder):
A_abs = 1 − R − T was systematically negative and tracked eta
(A_abs(f0) ≈ −1.2e-4, −1.2e-3, −1.2e-2 at eta = 1e-4, 1e-3, 1e-2), and
FIB21_tau had T_peak(B0) = 16.939 at eta = 1e-3 (T > 1). Those lossy
spectra are not trusted. The v2 runner's H7/H8 PASS marks are withdrawn
as evidence; they are not [E] and are not used below. They will be
replaced only by the scores from this addendum, after freeze and run.
No new lossy number is computed in this file.

TLS stays [X] and is not modelled. No measured W or SiO2 loss source is
opened. Eta values remain assumed [A]. This addendum uses the discrete
set {1e-4, 1e-3, 1e-2}.

## What is frozen (everything in v2 stays, with exactly these changes)

Geometry, materials [A], f0 = 2.0 GHz, tau thicknesses, words, frequency
grid, B0, and the metrics already used to score the v2 result note
(sha256 a36c3460…) stay unchanged. Do not re-run eta = 0. Do not
re-score H1–H6. Do not edit the v2 prereg, the v2 runner, the original
v2 JSON, or the v2 result note.

C1. Loss sign only. In the W and SiO2 layers, not in the Si half-spaces,
replace M by M(1 + i eta). Equivalently, v_c = v * sqrt(1 + i eta) with
the principal square root, z = rho v_c, k = 2 π f / v_c. The same eta is
applied to W and to SiO2. The transfer-matrix entries, the r and t
algebra, and the definitions R = |r|^2, T = |t|^2 stay identical to the
frozen v2 runner (identical lossless Si half-spaces). The new runner
lives in the output folder named below and may copy TR from the v2
runner with that one sign change only. The v2 runner file itself is not
edited.

C2. Cases. Re-run only the lossy etas {1e-4, 1e-3, 1e-2},
each [A], on the four tau stacks PER21_tau, FIB21_tau, PER13_tau,
FIB13_tau, on the main N = 20001 grid (0.05–6.5 GHz inclusive linspace)
and at the single frequencies f0 and 2 f0. FIB13_tau and PER13_tau remain
size checks, not scored. Do not re-run V2 (quarter-wave v1 reproduction)
or V3. Do not re-run eta = 0.

C3. Absorption and the R+T+A=1, A>=0 check. R and T remain |r|^2 and
|t|^2. A_abs is defined by A_abs = 1 − R − T, so R + T + A_abs = 1 holds
by definition at every frequency. The substantive passivity gate is
A_abs >= 0 together with 0 <= R,T <= 1, to a numerical floor stated in
V_L below. This is a check on the corrected convention, not a new
physical absorption integral.

## Validations (must all pass, else H7 and H8 are VOID)

V_L0, single-layer sign check. One W layer of thickness d_A (the frozen
tau long thickness), between the same lossless Si half-spaces, at
eta = 1e-3, on the main grid: min A_abs >= −1e-10 and A_abs(f0) > 0.
If this fails, the sign is still wrong and the run is VOID.

V_L, passivity on the declared stacks. For each eta in {1e-4, 1e-3, 1e-2}
and each of the four tau stacks, on the main grid:
- min A_abs >= −1e-10
- min R >= −1e-10 and min T >= −1e-10
- max R <= 1 + 1e-10 and max T <= 1 + 1e-10
Report, for each stack and eta, min A_abs, A_abs(f0), max A_abs, max T,
and max R. If V_L fails for any scored stack (PER21_tau or FIB21_tau) at
eta = 1e-3 or eta = 1e-2, H7 and H8 are VOID. A V_L failure only at
eta = 1e-4, or only on a size-check stack, is reported and does not void
H7/H8, but that eta or stack's spectra are not trusted.

If V_L0 or a voiding V_L check fails, report the validations and do not
treat H7 or H8 as scored results.

## Hypotheses (declared in this addendum, before the addendum run)

The eta = 0 comparison baselines are the two T(f0) values stored in this
folder for the 21-layer Fibonacci and periodic tau stacks, in the derived
file eta0_baselines.json, which the runner must rehash and refuse to use
on mismatch. Do not recompute eta = 0. The parent preregistration is
cited only by sha256 33338a45… and is not reproduced here.

- H7, at the sampled value eta = 1e-3 under the corrected convention C1:
  compare T(f0) of FIB21_tau with T(f0) of PER21_tau. H7 PASSes only if
  that inequality has the same strict direction as the stored eta = 0
  pair. If those two stored eta = 0 values are equal, no direction
  exists to preserve, and H7 is a FAIL.
- H8 repeats that direction-stability comparison at the sampled value
  eta = 1e-2.

Report PASS/FAIL with the measured T(f0) values. Do not change
thresholds after seeing the numbers. H7 and H8 are loss-ranking
stability claims against assumed [A] eta, not against measured loss,
and only at those two sampled values (eta = 1e-4 is reported
descriptively and is not a scored ranking test).
Computed model numbers are [E]. Failed gates are [F]. If VOID, H7 and
H8 stay untrusted and are not labelled [E] or [F].

Also report, descriptively and not as isolator-advantage evidence:
T(f0), T(2 f0), T_peak(B0), S(B0), f0-containing −20 dB (or
transmission-suppression) bands, A_abs(f0), and max A_abs, for
PER21_tau and FIB21_tau at each lossy eta. These may be compared in
words to the untrusted v2 lossy spectra; they do not reopen H1–H6 and
do not change the eta = 0 isolator-advantage FAIL [F].

## Verdict criteria (stated in advance)

- Isolator advantage remains FAIL [F], as already scored at eta = 0
  in the v2 result note (sha256 a36c3460…). This addendum cannot
  change that mark.
- H7 and H8 are scored only if V_L0 and the voiding V_L checks PASS.
- This addendum adds no new overall mark. The only new scored claims
  are H7 and H8, each PASS [E] or FAIL [F], or VOID.
- This model remains 1D, normal incidence, longitudinal only. It is not
  evidence about measured films. TLS stays [X] and is not modelled.
  Infima stay [X].

## Scope

1D transfer-matrix model of tau-thickness W/SiO2 stacks on Si, normal
incidence, longitudinal only. Not a measured specimen and not a 3D model.

## Outputs

This folder (the public copy places the runner, results JSON, and dated
result note next to this addendum): a runner, results JSON, and a dated
result note. The runner must rehash this addendum and the derived
eta = 0 baseline file eta0_baselines.json and refuse to run on mismatch.
The parent v2 prereg hash 33338a45… is recorded as a cited pin; that
file is not reproduced here. No edit to any file named in "What is
frozen" above.
