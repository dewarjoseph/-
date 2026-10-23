# Phase V-E protocol: compressions of the exact boundary response (frozen)

The protocol was frozen and committed **before any basis was evaluated on an evaluation-set system** (the 264 rule classes or the 18 controls). Development used only the four development rules listed below, plus FR30 at levels 2–3, whose bottoms were already public in V-A to V-D. The machine-readable copy is `audit/results/phase5e_protocol.json`. The level-7 scaling predictions were frozen separately and earlier, in commit a781ad8 (`audit/results/phase5e_level7_prediction.json`), while the level-7 solver was still at pass 1.

## 1. Objects (unchanged from V-D)

- **Operator.** H = 24 I − A on ℓ²(tiles) ⊗ ℂ², with Q8 Clifford links. Uses the pinned convention of `audit/phase5a_controls.py`.
- **Partition and target.** Depth-1 child partition, surface S, interior I, child responses R_c(E), glued operator K(E). These are V-D's definitions (`audit/phase5d_schur.py`).
- **Target.** The level-4 pinned bottom Y4, as stored by V-B/V-C. It is re-derived here by shift-invert at 0 (H ≥ 0), and agreement with the stored value is checked.
- **Compressed prediction.** For a subspace W of the S-space with orthonormal basis P, the prediction E_W is the root of g_W(E) = λ_min(P†K(E)P) on E < λ_II. It is parameter-free and satisfies E_W ≥ Y4 (Rayleigh–Ritz). The root is computed with the bracketed Newton/chord iteration of `audit/phase5e_rg.py` to 10⁻¹² (it relies on the concavity of g_W). E_REF = 7.0, the V-D energy, is admissible for every system: λ_II ≥ 7.735 at level 4.

## 2. Candidate bases (frozen; `audit/phase5e_rg.py`)

All bases are Kramers-complete (multiplets never split) and gauge-covariant. D is the retained complex dimension. dim S = 4592 at level 4.

| family | definition | grid |
|---|---|---|
| `child(k)` | k lowest Kramers pairs of R_c(E_REF) per child (complete child-eigenmode basis, V-D) | k = 1, 2, 4, 8, 16, 32, 64 |
| `face(k)` | k lowest pairs of R_c(E_REF)[F,F] on each face F (face tiles of c facing exactly one other child) | k = 1, 2, 4, 8, 16 |
| `iface2(k)` | k lowest pairs of K(E_REF) restricted to the two facing faces of each adjacent child pair (two-sided seam modes) | k = 1, 2, 4, 8, 16, 32 |
| `fec(k)` | face(k), plus k lowest pairs on each hinge (tiles facing two other children), plus all corner tiles (≥ 3) | k = 1, 2, 4, 8, 16 |
| `patch2(k)`, `patch3(k)` | k lowest pairs of R_c(E_REF) on each patch = interface tiles of c inside one depth-2 (depth-3) subtree; hierarchy/wavelet-like | k = 1, 2, 4, 8 and k = 1, 2 |
| `adaptive(m)` | coordinate subspace of the m surface tiles with the largest **training-rule** mean ground-state density (geometric tile keys; V-D CV repetition-0 folds; controls trained on all 264) | m = 64, 128, 229, 512 (D = 2m) |
| `interface` | all interface tiles (coordinate subspace): the physically motivated tile selection, **not** a compression by the criterion below | — |
| `oracle(m)` | as `adaptive`, but ranked by the system's own ground state. **Not admissible** (uses the target); reported only as the ceiling of tile selection | m as above |
| `exact` | all of S: the V-D reference ceiling, explicitly **non-compressed** | validation subset only |

The face/hinge/corner geometry and the depth-2 and depth-3 patch counts do not depend on the level, so at fixed k each family has the same D at every level. That makes "fixed D across levels" the renormalization-group test.

**Development record (rules 950 and 1583, level 4; not evaluation systems).** Every low-mode family had an edge error between 0.48 and 1.6 for D ≤ 1372. `interface` (D = 2554) had 0.006 and 0.015. As a result, `face(32)` (D = 2016, 140 s per system) was dropped from the grid, and `iface2` was added before freezing.

## 3. Evaluation sets (unchanged)

- **Rules.** The 264 V-D rule classes (`audit/results/phase5d_protocol.json`), one representative per symmetry class, FR30 representing its own class. They were re-verified from the V-D feature shards.
- **Controls.** The 18 V-D level-4 intervention controls, never used for training.
- **Development rules.** 950, 1583, 1787 and 3133. Each is one representative of a class outside the 264, drawn with seed 20261026. They are used only for development and for the level sweep.
- **Level sweep.** FR30, 3697 (= 4757), 1387 and 2238, plus the four development rules, at levels 2, 3, 4 and 5. Level 5 omits `interface`.
- **Level 3.** All 264 classes.

## 4. Primary configuration per family

The primary configuration is the largest member with **D ≤ 459 = 10 % of dim S**: child(16), face(4), iface2(8), fec(2), patch2(4), adaptive(229). patch3 has no member under the cap (patch3(1) has D = 538), so it is reported but cannot pass. Since the members are nested, no data are used for this choice.

## 5. Success criteria (all required, for the primary configuration of a family)

| # | criterion | threshold and reason |
|---|---|---|
| C1 | compression | D ≤ 0.10 · dim S |
| C2 | spectral accuracy | calibrated out-of-fold RMSE of E_W ≤ **0.05**, and max calibrated error ≤ 0.15. Calibration subtracts the mean (E_W − Y4) of the training folds (V-D repetition-0 10-fold split), allowing for the one-sided Ritz bias. *Reason:* the effects to be explained are ≥ 0.1 (15 of 18 control residuals; FR30 +0.77; M6's regression error 0.103), so resolving them at 2σ needs RMSE ≤ 0.05. Solver error (≤ 10⁻¹⁰) is negligible. |
| C3 | gauge invariance | max \|ΔE_W\| ≤ **10⁻⁸** under a random SU(2) gauge per tile (gauge set: 12 systems at level 3, 4 at level 4). *Reason:* this is 10⁴ times the root tolerance and well above the eigensolver's 10⁻¹¹. |
| C4 | held out beyond baselines | M7 = flux + E_W, in V-D's exact CV (20 × 10-fold, seeds 20261024 + r, ridge α by inner 5-fold CV). Its CV-R² must exceed both M4 (0.9174 ± 0.0018) and M2 (0.8900 ± 0.0008) by more than 2 sd, using the larger of the two sds. The calibrated parameter-free RMSE must also be below M4's CV-RMSE (0.1747). |
| C5 | interventions | (a) sign of E_W(control) − E_W(FR30) correct for all 17 controls (actual \|ΔY4\| ≥ 0.31 for each, so there are no ties); (b) sign of the M7-predicted flux residual correct for every control with \|actual residual\| ≥ 0.05 (16 of 18); (c) corr(predicted, actual residual) ≥ 0.8. |
| C6 | FR30 | the M7 leave-FR30-out fraction of FR30's flux residual explained ≥ 0.5, and FR30's calibrated E_W error ≤ 0.10 |
| C7 | stability | (a) at fixed k, the mean relative edge error over the 8 level-sweep systems must not grow by more than 1.5× from level 3 to 4, nor from 4 to 5; (b) the 95th percentile of the level-4 calibrated error across the 264 classes ≤ 0.10 |
| C8 | interpretation | the basis is defined geometrically, spectrally on local blocks, or from training data, with D ≤ 10 %. It is not K(E) itself. |

**Decision.** A family is a *meaningful success* only if C1–C8 all hold. If none passes, the result is negative and is reported as such, with the failure quantified per criterion. No further families, grids, energies or thresholds are added after this freeze. Anything added later is labelled **exploratory** and needs a fresh holdout before it can influence a conclusion.

## 6. Pre-registered diagnostics (no pass/fail role)

- **Captured weight.** c = ‖P†ψ_S‖²/‖ψ_S‖² of the exact ground pair, and the Ritz defect g_W(E_0). These are checked against the two-sided bound of Theorem E4: μ₂(1−c) ≤ g_W(E_0) ≤ μ_max(1−c)/c, with μ₂ ≥ min(λ₃, λ_II) − E_0.
- **Tile support.** The number of surface tiles holding 50, 90, 99 and 99.9 % of ψ_S, and its growth with level.
- **H2 closure test.** This is the universal child subspace. The restrictions of the FR30 ground pair at levels 4, 5 and 6 (and 7 if it converges) to every copy of the level-3 supertile give snapshots in the 574-dimensional T₃ surface space. The optimal (SVD) subspace trained on levels 4–5 is tested on level 6. *Pass mark for "closure plausible":* d ≤ 57 (10 %) captures ≥ 99 % of the held-out-level weight. Eckart–Young then gives a lower bound on the uncaptured weight of every fixed d-dimensional subspace.
- **Child-response clustering.** The number of eigenvalues of R_m(E_REF) within w = 0.25, 0.5, 1, 2 and 4 of its bottom, for m = 1–4.
- **Exploratory, flagged.** A gauge-invariant energy budget: child-internal energy, seam bond energy, and bond efficiency η = −(bond energy)/(2 Σ|ψ_a||ψ_b|).

## 7. Compute plan

- **Hardware.** 24 logical CPUs, 32 GB, Windows 11, Python 3.12.10, numpy 2.5.2, scipy 1.18.1.
- **Lanes.** Single-threaded BLAS per lane. The level-4 stage uses 18 lanes (about 250 s per system). Level 3 uses 6 lanes. The level sweep runs one system per lane. The adaptive stage runs after level 4.
- **Level 7.** The level-7 solver runs separately with 4 threads (`audit/phase5e_level7_runner.py`). Its scaling verdict uses only the rules frozen in a781ad8.
- **Logs.** Logs are kept in the session scratchpad. Every result line records seconds and iterations.
