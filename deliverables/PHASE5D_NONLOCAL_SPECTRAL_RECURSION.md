# Phase V-D — Nonlocal spectral recursion and the FR30 excess

Branch `claude/phase5d-nonlocal-recursion` (from the Phase V-C head 5be8e28). Everything below was computed in this phase by `audit/phase5d_schur.py` and `audit/phase5d_analyze.py`. The held-out protocol (`audit/results/phase5d_protocol.json`) and the analysis code were committed (7ba5e8f) **before any descriptor value was computed**. Status tags: **[P]** proved, **[E]** numerical with stated errors, **[U]** unresolved.

## Result

**The hypothesis is partly supported and the mechanism is not established.** The frozen decision criterion required three things of a descriptor that contains no target-derived quantity (model M3 or M4):

1. beat the flux-only, bounded-radius and previous-level-edge baselines out of sample by more than 2 sd;
2. explain a majority of FR30's leave-out residual;
3. track the intervention residuals with correlation above 0.5.

The best such model (M4: child surface response plus gluing penalties) **passes (1)**, with CV-R² 0.917 ± 0.002 against 0.799, 0.881 and 0.890. It **fails (2)**: it explains 0.42 of FR30's residual. It **passes (3) only nominally**: correlation 0.55, but with a mean error of 0.27, sign errors on several hierarchy-destroying controls, and a predicted +0.51 for a control whose actual residual is 0.00.

The failure is located precisely. The exact glued boundary operator K(E) carries essentially all the information: at fixed energies it predicts 86 % of the flux-residual variance, 94 % of FR30's residual, and the interventions with correlation 0.99. But that operator does not compress. The parent's lowest mode needs about 150 of the 574 child surface modes for 90 % of its weight, so no low-dimensional recursive representation exists in the child-mode basis. The partition is exact and the three energies suffice. **The obstruction is the lack of a low-dimensional representation, not the choice of partition or the energy resolution.**

## 1. Evidence reproduced and discrepancies resolved

- **Census.** Complete, 6561 decorations at level 3, forming **1098 symmetry classes** (1089 of size 6, 9 of size 3; class key = level-3 bottom to 7 decimals plus the level-4 class-count multiset). FR30's class is {1386, 3690, 4752}.
- **Discrepancy resolved.** Decoration 4757 (cited in Phase V-B as beating FR30 at level 4) and decoration 3697 (one of the five rules in Phase V-C) are **the same symmetry class**. "4757 and the five rules above FR30" is therefore five independent rules, not six: classes of 1387, 3693, 3697 = 4757, 1144, 3718.
- **Level-4 data.** Level-4 bottoms are *sampled*, not complete. They cover the 256 classes of the preregistered Phase V-B sample plus 8 classes from Phase V-C, **264 classes** in all, each represented once and used as one data unit. No symmetry copy is counted twice.
- **Controls.** The 18 level-4 intervention systems are taken from `audit/results/phase5b_controls.jsonl`, and their bottoms were re-derived here through the Schur root (maximum error 4.7×10⁻¹¹).

## 2. Effective boundary operator

**Partition.** Children are the eight depth-1 subtrees (tile index // 8^(L−1)). The surface S_c of child c is its set of tiles with a panel neighbour outside the child, whether in another child or missing. I = ∪(child \ S_c).

**Theorem D0 [P] (additivity).** The pinned operator has diagonal 24 on every tile, so H(T_L) = ⊕_c H_pin(child c) − V. Here V is the set of inter-child panel hoppings. Each child block is exactly the pinned operator of T_{L−1}: links depend only on M_aᵀn and are therefore invariant under the child's rotation. Every inter-child hop joins two surface tiles, so H_II is block diagonal over children (checked in a test).

**Definitions.**

- Child response: R_c(E) = H_{S_cS_c} − E − H_{S_cI_c}(H_{I_cI_c} − E)⁻¹H_{I_cS_c}.
- Glued operator: K(E) = ⊕_c R_c(E) − V_SS, the Schur complement of H − E onto S. It is computed with dense child-local solves; nothing larger than a child interior is ever inverted.

**Theorem D1 [P] (Schur criterion).** Write λ_II = λ_min(H_II). On the admissible interval E < λ_II:

- det(H − E) = det(H_II − E) · det K(E);
- K(E) is Hermitian, and dK/dE = −I − XX† ≤ −I with X = H_SI(H_II − E)⁻¹, so λ_min K(E) is strictly decreasing with slope ≤ −1;
- by Haynsworth inertia additivity, the number of eigenvalues of H below E equals the number of negative eigenvalues of K(E);
- hence λ_min(H) is the unique root of λ_min K(E) = 0 whenever λ_min(H) < λ_II.

The spectrum of K(E) at a fixed E is *not* the spectrum of H. Only its sign changes, and its negative-eigenvalue count, carry spectral information about H.

**Validation [E]** (`audit/results/phase5d_validate.json`; tests in `tests/test_phase5d.py`):

| check | result |
|---|---|
| root of λ_min K vs direct bottom, levels 2–3, four systems (FR30, rule 2238, iid1, shuffle1) | errors 2×10⁻¹⁵ … 3×10⁻¹¹ |
| inertia count at 7 energies per system | agrees everywhere |
| Schur complement vs explicit dense complement (level 3) | 10⁻¹¹ |
| root vs stored LOBPCG bottoms, level 4, 13 rules and 18 controls | ≤ 2×10⁻¹³ and ≤ 5×10⁻¹¹ |
| random SU(2) gauge per tile: every descriptor | invariant to 2×10⁻¹⁴ |
| admissible windows | λ_II ≥ 7.735 over all 264 rules at level 4 (17.4 at level 3); 4 of 792 feature evaluations fall at inadmissible energies (E = 8 for rules with λ_II < 8) and are flagged |
| lowest eigenvalue of the 4592-dimensional K | Lanczos and dense LAPACK agree to 2×10⁻¹⁴ |

**Gauge subtlety found and fixed.** Every eigenvalue of R_c is a Kramers doublet (quaternionic symmetry). A reduced model that keeps a single vector of a doublet depends on the gauge (deviation 0.09). The reduced models therefore keep whole Kramers multiplets, after which every descriptor is gauge-invariant.

## 3. Recursive descriptor

**Theorem D2 [P] (exact recursion).** Write R_m(E) for the response of the whole supertile T_m on its outer surface. R_{m+1}(E) is the Schur complement, onto the parent surface, of the glued operator built from eight copies of R_m(E) and the inter-child hoppings. The proof uses quotient-formula transitivity of Schur complements together with Theorem D0. **Validated** for m = 1…4 and four rules: deviation from the direct Schur complement ≤ 7×10⁻¹⁵ (`audit/results/phase5d_recursion.json`).

**Spectral flow across levels** (lowest eigenvalue of R_m(7.0), Kramers-degenerate):

| m | surface tiles | FR30 | rule 3697 (= 4757) | rule 1387 | rule 2238 |
|---|---|---|---|---|---|
| 1 | 8 | 7.810 | 8.724 | 8.724 | 8.913 |
| 2 | 53 | 4.942 | 5.183 | 5.283 | 4.867 |
| 3 | 287 | 4.220 | 4.357 | 4.827 | 4.501 |
| 4 | 1331 | 3.954 | 4.225 | 4.556 | 4.326 |

The surface dimension grows like 4^m, and the low spectrum of R_m clusters (gaps of a few 10⁻³ at m = 4). FR30's surface response is the *softest* of the four at every level from m = 3.

**Reduced-order benchmark [E]** (`audit/results/phase5d_reduced_order.json`). Rayleigh–Ritz interface models keep the k lowest Kramers pairs of each child's R_c(7); they are upper bounds on λ_min K.

| pairs per child k | 1 | 4 | 16 | 64 | 128 | 287 (all) |
|---|---|---|---|---|---|---|
| FR30 error | +1.763 | +1.660 | +1.487 | +0.718 | +0.451 | 0 |
| rule 1387 error | +1.815 | +1.753 | +1.612 | +0.845 | +0.540 | 0 |

The exact lowest vector of K(7) needs child-mode ranks 27 / 153 / 538 (FR30) and 17 / 140 / 532 (rule 1387), out of 574, to hold 50 / 90 / 99 % of its weight. The inter-child coupling (unit hopping on every interface panel) is as strong as the child response itself and mixes almost the entire child surface spectrum. **No low-dimensional recursive representation exists in this basis.** The exact recursion's effective boundary dimension is the whole surface. **[E]**

## 4. Held-out comparison (frozen protocol)

The unit is one symmetry class (264 classes). Rule-level 10-fold CV is repeated 20 times; ridge regularization is chosen by inner CV; the flux columns are always included. Descriptors are evaluated at the fixed energies E ∈ {6, 7, 8}, which are not tied to any rule's own edge.

| model | CV-R² (Y4) | CV-RMSE | share of flux-residual variance explained | FR30 leave-out: share of its residual explained |
|---|---|---|---|---|
| M0 flux only | 0.7986 ± 0.0011 | 0.2727 | 0 | 0 (residual +0.773) |
| M1 + 30 bounded-radius predictors | 0.8813 ± 0.0032 | 0.2093 | 0.411 ± 0.015 | 0.152 |
| M2 + Y3 (previous-level edge) | 0.8900 ± 0.0008 | 0.2015 | 0.454 ± 0.004 | 0.548 |
| M3 + child response c1(E) | 0.8345 ± 0.0021 | 0.2472 | 0.178 ± 0.011 | 0.084 |
| **M4 + c1 + gluing penalties gp_k(E)** | **0.9174 ± 0.0018** | **0.1747** | **0.590 ± 0.010** | **0.416** |
| M5 + Y3 + c1 + gp | 0.9497 ± 0.0010 | 0.1363 | 0.750 ± 0.005 | 0.711 |
| M6 + λ_min K(E) (exact-reformulation control) | 0.9714 ± 0.0013 | 0.1027 | 0.858 ± 0.007 | 0.942 |

Solver error (≤ 10⁻⁷ in Y4, ≤ 2×10⁻¹⁴ in the descriptors) is negligible next to the repetition spread shown.

**Interventions** (18 controls, never in training; models trained on all 264 classes): correlation between predicted and actual flux residual, and mean absolute error.

| model | correlation | mean error |
|---|---|---|
| M1 | 0.64 | 0.20 |
| M3 | 0.75 | 0.19 |
| M4 | 0.55 | 0.27 |
| M6 (control) | 0.99 | 0.05 |

M3 orders the controls correctly but compresses them toward zero: it predicts +0.07 for FR30, whose actual residual is +0.77. M4 predicts positive residuals for iid1, iid2 and flip 20 %, whose actual residuals are −0.24, −0.20 and 0.00. Per-control values are in `audit/results/phase5d_heldout.txt`.

**Where FR30 sits.** On the child response c1(7) it is at the 92nd percentile, on the gluing penalty gp₁(7) at the 46th, on gp₈(7) at the 79th, and on λ_min K(7) at the 98th. The rules with the highest raw edges (1387, 3693, 1144, 3718) are at the 95th–100th percentile of the gluing penalties. The compressed descriptors therefore account for the high-edge rules better than for FR30's excess. Collinearity: c1 correlates +0.48 with f_{−1}, gp₈ −0.10. The gluing penalties are not flux proxies.

## 5. The four required distinctions

- **Descriptor that merely correlates with flux.** c1 partly (r = 0.48 with f_{−1}); the gluing penalties are not.
- **Descriptor that predicts spectral edges across unseen rules.** Yes, for M4. It beats flux-only, all 30 bounded-radius predictors, and the previous-level edge, out of sample and with non-overlapping uncertainty. **[E]**
- **Causal mechanism supported by controlled interventions.** No. The compressed descriptors do not reproduce the intervention residuals quantitatively, and they explain only 42 % of FR30's residual. Only the uncompressed operator does (M6), and M6 is the eigenproblem restated at a fixed energy, so it cannot count as an explanation.
- **Hypothesis that remains untested.** Whether a *different* low-dimensional basis compresses K(E). Candidates: modes localized on individual child-child interface faces, a symmetry-adapted basis of the eight-child configuration, or the energy-dependent interface Green's function on each face. This is now the precise open problem.

## 6. Why the hypothesis fails, as the protocol required

| possible cause | finding |
|---|---|
| boundary partition | **ruled out**: the partition is exact (Theorems D0–D2, validated to 10⁻¹⁵) |
| energy resolution | **ruled out**: the same three energies carry 86 % of the residual variance through λ_min K (M6) |
| lack of a low-dimensional recursive representation | **identified as the obstruction**: 90 % of the parent mode needs about 150 of 574 child modes, and reduced models at k ≤ 128 pairs carry errors of 0.45 to 1.8 |
| excess unpredictable from the descriptor class | **not the case for the full operator**; true for the compressed descriptors tested |

**Narrowed hypothesis.** The excess is a property of the whole energy-dependent interface problem: how strongly the inter-child coupling frustrates nearly the entire child surface spectrum. It is not a property of a few soft child modes and their coupling. Any mechanism must therefore be a statement about a high-dimensional interface operator, or a compression in a basis other than the child eigenbasis. This sharpens Phase V-B's negative result, "no bounded-radius statistic explains it": the information is nonlocal *and* high-dimensional.

## 7. Problem B (thermodynamic limit), kept separate

The mechanism result says nothing about whether the interface-state structure and D₂ ≈ 1.9 persist at larger sizes, and none is inferred from it.

**Level 7 was not resumed in this phase.**

- **Cost estimate (Phase V-B, measured).** Dimension 4 194 304, H about 0.8 GB, 0.38–0.9 s per matvec. Checkpointed Chebyshev-filtered subspace iteration needs 6–15 h and 4–6 GB.
- **Convergence criterion (validated at levels 4 and 5 against stored values and the certified level-4 bound).** Residual ≤ 1e-7 on the lowest two Kramers pairs, which bounds the eigenvector angle to ≈ 0.02 rad at the extrapolated gap 5×10⁻⁶.
- **Frozen scaling prediction the run would test.** If the critical-state reading of Phase V-A is right, D₂ in the 6→7 window lies in [1.80, 2.00], the depth-1 interface weight lies below 0.57 with enrichment above 10, and the overlap of the level-7 ground state with the level-6 state replicated in the centre child falls below 0.14. A D₂ above 2.3 would indicate a crossover toward extended states; a D₂ below 1.5, toward localization.

Resume command (checkpoints from Phase V-B exist at pass 1):

```
OMP_NUM_THREADS=2 setsid nohup timeout 50400 python3 -u -I audit/phase5b_d_level7.py run 7 --resume > <log> 2>&1 < /dev/null &
```

## 8. Reproduction, logs, resources, inventory

```
python3 -u -I audit/phase5d_schur.py validate          # Schur root, inertia, gauge, levels 2-3 (about 1 min)
python3 -u -I audit/phase5d_schur.py recursion 4        # exact recursion m=1..4, spectral flow (about 5 min)
python3 -u -I audit/phase5d_schur.py features <s> 3     # 3 shards, 264 rule classes at level 4
python3 -u -I audit/phase5d_schur.py controls           # 18 intervention controls at level 4
python3 -u -I audit/phase5d_analyze.py                  # frozen held-out evaluation
python3 -m unittest tests/test_phase5d.py               # 7 tests
```

**Resources.** The feature sweep took about 1.6 h on three single-thread lanes plus one lane for the controls; peak RSS under 1 GB per lane. About 9 s per energy per rule.

**Logs.** Scratchpad `phase5d/feat{0,1,2}.log` and `controls.log`.

**Files.**

- *New code:* `audit/phase5d_schur.py`, `audit/phase5d_analyze.py`.
- *Results:* `audit/results/phase5d_{protocol,validate,recursion,reduced_order,heldout}.json`, `phase5d_heldout.txt`, `phase5d_features_shard{0,1,2}.jsonl` (every rule: features at three energies, admissibility, λ_II, root checks), `phase5d_controls.jsonl`.
- *Tests:* `tests/test_phase5d.py` (7, pass).
- *Previous reports:* not modified.

**Commits.** 7ba5e8f (frozen protocol), f22389c (solver change, validated, no definition changed), then this report's commit.
