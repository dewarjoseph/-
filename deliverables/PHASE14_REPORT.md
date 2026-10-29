# Phase XIV — The Chair44 matter floor in a dynamical Q₈ gauge field (first "new physics" experiment)

**Status labels.**
- [P] proved;
- [C] computed exactly or to rounding level;
- [E] floating-point evidence;
- [X] conjecture or extrapolation;
- [F] falsified.

**Everything in this phase is [E], from a simulated (Monte Carlo) ensemble** on one finite patch of 512 tiles. No continuum, infinite-volume or physical claim follows from it (§5).

**Artifacts.**

| role | file |
|---|---|
| protocol (frozen before any value) | `audit/results/phase14_preregistration_dynamical.json`, commit 429d370, sha256 `da1e379d…b958` |
| driver | `audit/phase14_dynamical.py` |
| data | `audit/results/phase14_dynamical.json` |
| scoring | `audit/phase14_score.py` → `phase14_score.json`, `phase14_ledger.json` |
| tests | `tests/test_phase14.py` |

---

## 1. Question and why it is the first step

Phases X–XIII studied the frustration floor λ_min(H_U) of the Chair44 operator for **frozen** frame-rule backgrounds U. The handoff brief lists "frozen background" among the no-go facts: a fixed connection is not a dynamical gauge field. It names a dynamical gauge field on the hull as candidate (a).

The question, frozen before any value was computed:

> When the Q₈ gauge field on the chair hull is dynamical (Wilson action), does the Chair44 matter floor survive as an order parameter, and are the frame-rule backgrounds typical or atypical configurations of the ensemble?

## 2. Model (dynamics, regime, observable)

- **Complex.** The dual cubical complex of the pinned level-3 chair supertile (`phase5c_q8_gauge.fr30_complex(3)`):
  - 512 tiles and 3 584 unit cubes;
  - 9 984 dual links, of which 5 376 join different tiles and are dynamical; links inside a tile are frozen to 1 ("rigid tiles");
  - 9 264 plaquettes, of which 7 728 are inter-tile.
- **Action.** S[U] = β Σ_p (1 − ½ Re Tr U_p), with U_l ∈ Q₈. This is the Wilson action of the finite group Q₈ ⊂ SU(2).
- **Sampler.** The exact heat bath over the 8 group elements: the Phase V-C engine G, unchanged.
- **Matter (quenched).**
  - H_U = 24 − Σ_l [L(U_l) at (a, b) + L(U_l)ᵀ at (b, a)], where L(q) is the 4×4 real left multiplication by the quaternion q. This is the realified spinor form of Phases X–XIII, with each eigenvalue doubled.
  - The floor λ_min(H_U) is computed by dense diagonalisation (dimension 2 048) on every measured configuration.
- **Regime.** One finite patch, 15 couplings β ∈ [0, 6], hot and cold starts, 300 thermalisation sweeps, then 40 measurements 10 sweeps apart.

## 3. Checks (all pass)

| check | requirement | result |
|---|---|---|
| C1 | at β = ∞ (cold, no sweeps) λ_min(H_1) = trivial floor of T₃, 1.66951 | 1.6695123 ✓ |
| C2 | λ_min invariant under 3 random tile-wise gauge transformations (to 1e-9) | max deviation 2.3·10⁻¹⁴ ✓ |
| C3 | at β = 0, each of the 8 elements within 5 % of 1/8 | frequencies 0.1239–0.1259 ✓ |
| C4 (not preregistered) | the 1387 frame-rule background in this H_U gives Y₃(1387) of Phases XII–XIII | 9.955918832 = 9.955918832 ✓ |

C4 confirms that the dynamical-matter operator and the frozen-background operator of the earlier phases are the same operator, so the comparisons in H2 are like with like.

## 4. Results and scores

**Results by coupling.** Columns:
- ⟨P⟩ is the mean real part of the inter-tile plaquettes;
- floors are the mean ± standard error (SE) over 40 configurations;
- the last column gives the range of sampled floors over both starts.

| β | ⟨P⟩ hot | floor hot | floor cold | sampled range (both starts) |
|---|---|---|---|---|
| 0 | 0.000 | 15.050 ± 0.032 | 15.029 ± 0.026 | 14.28 – 15.46 |
| 0.25 | 0.061 | 14.565 ± 0.024 | 14.497 ± 0.028 | 13.87 – 14.96 |
| 0.5 | 0.128 | 13.880 ± 0.036 | 13.930 ± 0.029 | 13.28 – 14.31 |
| 0.75 | 0.201 | 13.153 ± 0.034 | 13.184 ± 0.037 | 12.39 – 13.53 |
| 1.0 | 0.283 | 12.194 ± 0.031 | 12.284 ± 0.038 | 11.61 – 12.64 |
| 1.25 | 0.376 | 11.049 ± 0.042 | 11.057 ± 0.036 | 10.36 – 11.61 |
| 1.5 | 0.495 | 9.296 ± 0.042 | 9.236 ± 0.048 | 8.56 – 9.95 |
| 1.75 | 0.734 | 4.647 ± 0.063 | 4.769 ± 0.056 | 3.82 – 5.59 |
| 2.0 | 0.966 | 1.848 ± 0.006 | 1.819 ± 0.008 | 1.74 – 1.99 |
| 2.25 | 0.986 | 1.843 ± 0.005 | 1.712 ± 0.003 | 1.69 – 1.92 |
| 2.5 | 0.993 | 1.788 ± 0.010 | 1.685 ± 0.001 | 1.67 – 1.99 |
| 3.0 | 0.993 | 1.834 ± 0.006 | 1.672 ± 0.000 | 1.67 – 1.91 |
| 3.5 | 0.994 | 1.877 ± 0.007 | 1.670 ± 0.000 | 1.67 – 1.96 |
| 4.0 | 0.994 | 1.824 ± 0.007 | 1.670 ± 0.000 | 1.67 – 1.94 |
| 6.0 | 0.963 | 2.610 ± 0.004 | 1.6695 | 1.67 – 2.66 |

**Scores.** These are computed by `phase14_score.py` from the stored samples, with the preregistered rules; nothing is refitted.

| prediction | verdict | data |
|---|---|---|
| **H1** hot-series ⟨λ_min⟩ non-increasing (no rise > 3 SE) | **[F] fails** | rises 2.5→3.0 (+0.046 > 0.035), 3.0→3.5 (+0.043 > 0.028), 4.0→6.0 (+0.786 > 0.025) |
| **H2** Y₃(1387) = 9.95592 exceeds every sampled floor at every β | **[F] fails** | violated at β = 0, 0.25, 0.5, 0.75, 1.0, 1.25 (every sample there lies above 10.35) |
| **H3** largest floor drop within one grid step of largest ⟨P⟩ rise | **holds** | both at β = 1.5 → 1.75 (drop 4.65; rise 0.239) |

### Reading the scores (descriptive, not preregistered)

- **H1 fails because the hot starts do not equilibrate.**
  - For β ≥ 2 the hot and cold series disagree by more than 3 SE.
  - At β = 6 the hot start freezes at ⟨P⟩ = 0.963 with the floor at 2.61, while the cold start sits at ⟨P⟩ = 1 and the trivial floor.
  - This is the metastable-defect behaviour already seen with engine G in Phase V-C, and it is expected at a first-order transition of a finite-group Wilson theory (Petcher–Weingarten 1980).
  - The cold series has no rise beyond 3 SE.
  - The prediction named the hot series, so H1 stays **[F]**. A rescored cold series would be a post-hoc choice and is not offered as a result.
- **H2 fails in the direction opposite to the one predicted.**
  - Disordered gauge fields on this patch are **more** frustrated than the frame-rule backgrounds: about 15 at β = 0, against 9.96 for 1387.
  - The 1387 value lies in the gap between the β = 1.25 samples (≥ 10.36) and the β = 1.5 samples (≤ 9.954). No sampled configuration at any grid coupling reaches it.
  - FR30 (Y₃ = 9.378) lies inside the β = 1.5 range.
  - So on T₃ the frame-rule floors are not extreme within this ensemble. They correspond to an intermediate-coupling level of disorder.
- **H3 holds, but it is a weak test.** The floor is a function of the field, and the field changes most at the crossover. Coincident largest changes are the natural outcome, not a discriminating one.

## 5. What this does not show (and why)

- **No infinite-volume statement.**
  - On the infinite hull, a field with independent random links contains arbitrarily large nearly-trivial regions with probability 1. The bottom of its spectrum is then that of the trivial connection (this is the no-go "random links have floor 0 a.s." in the brief).
  - The β = 0 value of about 15 is therefore a property of the pinned 512-tile patch, which is too small to contain such regions. It is not a property of the ensemble.
  - The same caveat applies to every β below the crossover.
- **No continuum limit.**
  - Q₈ is a finite group, and its Wilson theory has a bulk transition, not a scaling region.
  - The crossover near β ≈ 1.5–1.75 on this patch is a lattice-scale phenomenon.
  - This is the no-go "no continuum limit" of the brief; nothing here changes it.
- **Quenched.** The matter does not act back on the gauge field. H_U is a probe, not a dynamical fermion: there is no determinant and no chirality.
- **One patch, one seed per start.** There is no volume scaling and no autocorrelation analysis beyond the 10-sweep spacing.

## 6. Novelty check (primary sources, read at abstract level)

- **Wilson theories of finite subgroups of SU(2).**
  - D. Petcher and D. H. Weingarten, *Phys. Rev. D* **22**, 2465 (1980), simulated the tetrahedral, octahedral and icosahedral subgroups. They found a first-order transition whose critical coupling moves toward zero as the order of the group grows.
  - G. Bhanot and M. Creutz, *Phys. Rev. D* **24**, 3212 (1981), mapped the phase structure of variant SU(2)/SO(3)/ℤ₂ actions.
  - Q₈ as a gauge group for quantum simulation appears, for example, in arXiv:2203.15541.
  - The gauge dynamics of this phase is therefore standard. Only the complex (the chair hull with rigid tiles) is specific to this programme.
- **Low modes of covariant Laplacians in gauge ensembles.**
  - F. Bruckmann and E.-M. Ilgenfritz, "Laplacian modes probing gauge fields", *Phys. Rev. D* **72**, 114502 (2005), arXiv:hep-lat/0509020.
  - J. Greensite, Š. Olejník, M. I. Polikarpov, S. N. Syritsyn and V. I. Zakharov, "Localized eigenmodes of covariant Laplacians in the Yang–Mills vacuum", arXiv:hep-lat/0504008 (2005).
  - Both use the bottom of a covariant Laplacian as a probe of SU(2) configurations.
  - The observable λ_min(H_U) is of this kind, but for the Q₈ spinor representation on an aperiodic hull with pinned boundary.
- **Conclusion.** No new method is claimed. The new element is the comparison of a dynamical ensemble against the frame-rule backgrounds of Phases X–XIII. Its first answer is the [F] of H2.

## 7. Next steps (proposals; none is run)

1. **Volume scaling at β = 0 (a derived, falsifiable prediction).**
   - The almost-sure argument of §5 predicts that ⟨λ_min⟩ at β = 0 decreases with the level L of the patch, towards the trivial floor of the same patch.
   - Freeze it, with a stated rate (none is claimed now), on T₂, T₃ and T₄. The size of T₄ (4 096 tiles, dimension 16 384) needs a sparse solver.
2. **Equilibration.** Use a parallel-tempering or two-start convergence criterion before any score that depends on the β ≥ 2 hot series.
3. **Candidate (b), the SU(2) scaling limit.**
   - Replace Q₈ by the binary icosahedral group and then by SU(2), where a scaling region exists.
   - First ask whether the floor measured in lattice units scales with the string tension. This is the first point at which a statement about a limit could be made, and it would be [X] until done.
4. **Candidate (c), a time direction.** Make the hull the spatial slice of a transfer-matrix (Hamiltonian) theory, so that "dynamics" means time evolution and not only a statistical ensemble.
5. **Candidate (d), the Geometric Unity bridge.** This stays an analogy only, [A], and is not pursued until 1–3 give a model with a limit.
