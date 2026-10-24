# Phase X — Spectral frustration across the Chair44 rule space: an extremal search, a bracketing classification, and the limits of curvature summaries

**Repository state.**
- Branch `claude/phase10-spectral-frustration`, cut from `main` at 37c27ff (PR #9 merged; it contains Phases V–IX).
- Prior commits and artifacts are untouched. Everything new is under `audit/phase10_*`, `audit/results/phase10_*`, `tests/test_phase10.py` and this report.

**Conventions** (fixed once, used everywhere):

| object | definition |
|---|---|
| decoration r | a frame choice for each of the 8 children of the chair substitution (`PHASE7_DEFINITIONS.md` §1). *Proper*: det = +1, 3⁸ = 6561 decorations (the census). *Extended*: any of the 6 permutations per child, 6⁸ = 1 679 616 |
| links | U_f(a→b) = (σ·M_aᵀn_f)(σ·M_bᵀn_f) ∈ Q₈ ⊂ SU(2). Reverse crossing gives U⁻¹. The sign of n_f is irrelevant |
| hull operator | H_Y = 24 − A_U = D_U†D_U on ℓ²(Y) ⊗ ℂ², Y in the hull Ω_r of the rule. On every infinite chair tiling Deg ≡ 24 |
| **E_\*(r)** | inf σ(H_Y). Constant on Ω_r when the hull is minimal |
| pinned bottom **Y_L(r)** | λ_min(24 − A_U) on the level-L supertile T_L(r): a compression of H_Y, so an *upper* bound on E_\* |
| free bottom **F_k(r)** | λ_min(Deg − A_U) on T_k(r), the Neumann operator: a *lower* bound on E_\* (Theorem X.2) |
| volume | tiles. The spinor dimension is 2 per tile |
| gauge class | S₃-orbit (rigid axis permutations) merged with verified gauge equivalences (Phase IX): **1098 classes**, each represented by its smallest decoration index. FR30 = decoration 4752 lies in class **1386** = {1386, 3690, 4752} |

These three quantities are always kept apart:
- λ_min of a finite matrix (Y_L, F_k, U_m), which is numerical or certified;
- E_\*(r);
- certified bounds on E_\*(r).

**Labels.**
- [P] proved;
- [C] computer-certified (exact rational arithmetic, or rounding-error-bounded Cholesky);
- [E] floating-point evidence;
- [X] conjecture;
- [F] falsified.

---

## 0. Answer

**The question.** Can FR30 be understood as one member of a mathematically defined family of spectrally frustrated geometric connections? Can we discover a better member, or prove a general principle that explains why certain local non-Abelian configurations produce unusually high spectral floors?

**1. The family exists. FR30 is one member of it, near the top but not at it.**
- The proper Chair44 frame rules form the family: 6561 decorations of the chair substitution with Pauli-frame Q₈ links, in 1098 gauge classes.
- Every member has a primitive frame substitution, hence a minimal hull.
- **Every member has a strictly positive infinite-volume floor, E_\* ≥ 3.788** [C].
- The certified intervals of all 1098 classes are computed (`phase10_dataset.json`).
- **806 classes are rigorously below FR30.**

**2. FR30 is not optimal.**
- **Certified: E_\*(1387) ≥ 8.7644994 > 8.7642270 ≥ E_\*(FR30).**
  - Class 1387 = {1387, 1388, 3691, 3692, 4753, 4754} is FR30 with only the frame of the central child changed.
  - The lower bound is Theorem X.7 at R = 14. All 7527 legal balls are certified, on the GPU, with Higham's rounding bound.
  - The upper bound is Phase VIII's exact rational Rayleigh quotient.
- **1387 leads the census.** It is first at every computed level and in the matched-radius localization bounds.
  - Its certified enclosure is [8.7644994, 9.3928286] (a stronger R = 15 certificate at μ ≈ 8.80 was still running when this report was written: pending).
  - Its lower bound exceeds the certified upper bound of 1094 of the other 1097 classes. The other three are 1389, 1391 and 901. 901 (Y₅ ≤ 8.7946) falls below if the pending R = 15 certificate passes.
- **Outside the census (Stage C), 1387's mirror twin is higher still at every computed level.**
  - The twin composes every child frame with the reflection x ↔ y, so each generation alternates handedness.
  - Y₅ = 9.4159 against 9.3928, and its level-4 lead is certified.
  - Its R = 14 certificate against FR30 was still running on the GPU when this report was written (no ball had failed after 2500 of 7527): pending.
  - Handedness is not a uniform improvement: FR30's own twin is lower.
- **All three of the brief's discovery targets are met** (§3.4).


**3. The general principle is standard mathematics, and it is support-type, not frequency-type.**
- Positivity is classified exactly. E_\*(r) > 0 iff some finite supertile carries a non-flat connection (Theorem X.3). Every proper rule qualifies.
- Quantitatively, the floor of every rule with a primitive frame substitution is the minimum, over its finitely many legal local environments, of their local ground energies, up to an explicit O(R⁻²) error (Theorem X.7, IMS localization applied to the whole family).
- A rule therefore has a high floor exactly when **every** legal local environment is strongly frustrated. One weakly frustrated legal environment sets the floor, however rare it is.
- Curvature *summaries* provably cannot carry this information:
  - plaquette class frequencies cannot lower-bound the floor (X.4: flat islands at frustration density ≥ 0.78);
  - identical Q₈ holonomy classes on every plaquette, and hence gauge-equivalent Abelian shadows, can carry certified different infinite-volume floors (X.5, on ℤ³);
  - identical class counts can carry certified different finite-volume bottoms (9.1).
- Non-Abelian holonomy raises the floors of FR30 and 1387 above their Abelian shadows, by certified margins ≥ 0.32 and ≥ 0.99. It lowers a ℤ³ connection's floor below two of its shadows, also certified (§7). It is not a principle in either direction.

**4. The hierarchy.** Not established.
- In the pre-registered held-out test, hierarchy descriptors improve the prediction in 3 of the 4 registered comparisons: Y₄ with both learners and Y₅ with gradient boosting.
- They do not improve the fourth (Y₅ with OLS), so the registered criterion fails.
- A post-hoc control against the union of all non-hierarchy descriptors shows the same pattern.
- Every registered hierarchy descriptor also fails the 937/938 test.
- By contrast, the local radius-1 environment minimum U₁ alone ranks the held-out level-5 bottoms with Spearman ρ = 0.955 (§3.1, §5).

**5. Novelty.**
- FR30 itself is Kamenetsky's certified assignment "frames30" (arXiv:2610.00916). The Phase VII radius-1 matching rule is not new; Phase IX's novelty entry is corrected.
- What is new here is computational and explicit (category 2):
  - the spectral extremal search over the rule family;
  - the census-wide certified positivity;
  - the certified ℤ³ class-field-matched pair;
  - the better candidate and its certificate.
- The general statements are established mathematics (category 1) applied to a new class of examples.
- No physical claim is made.

---

## 1. The starting point, verified (Part I)

**State recovered before any change.**
- PR #9 (Phases VIII–IX) is merged into `main` at 37c27ff, and the working tree was clean.
- This phase branches from that commit.
- All 22 Phase VIII–IX tests pass on it.

| Phase IX conclusion | how it was re-verified here | status |
|---|---|---|
| census of 6561 rules, **1098 gauge classes** | `phase10_census.gauge_classes()` rebuilds them (S₃-orbits plus the verified gauge merges). Test: the classes partition 0…6560, and members are isospectral at level 3 | **confirmed** [C] |
| link definition and orientation | Pauli formula; reverse crossing gives U⁻¹; normal sign irrelevant. Test: the spectrum is invariant under a random SU(2) gauge field | **confirmed** |
| operator construction | the phase9 builder (independent of the census code) and the census builder agree to 10⁻⁹ on the level-3 spectra of three rules, including the top Phase X class | **confirmed** |
| FR30's finite levels Y₃…Y₇ versus E_\* | Y_L are compressions (upper bounds), and E_\* is the hull infimum. Kept separate everywhere (conventions table) | **confirmed** |
| rigorous E_\* ∈ [7.954292, 8.7642270381] | the generalized localization code (`phase10_ims.py`, a separate implementation) reproduces Phase VII's FR30 values: 325 / 747 balls and certified Λ₆ = 3.655558585, Λ₈ = 6.562783238 to 10⁻¹². The upper endpoint is an exact rational Rayleigh quotient | **confirmed** [C] |
| 937/938 certified separation | `tests/test_phase9.py` recomputes it: ≥ 0.2776 (L3) and ≥ 0.2502 (L4) | **confirmed** [C] |
| radius-1 ladder and step-resolved results | stored artifacts with tests. The ladder code reproduces FR30's U₁…U₃ exactly | **confirmed** [E] |
| novelty of the radius-1 matching rule (Phase VII Thm 6.2) | primary-source check (§8) | **corrected**: FR30 is Kamenetsky's certified "frames30" (arXiv:2610.00916). The result is not new |
| completeness of "legal 1-stars from T₅" | Φ-closure check on every class (§3.1) | **corrected**: T₅ misses rare 1-star types in 1086 of 1098 classes (not FR30's). The radius-1 data are recomputed on the Φ-closure, which is complete when the frame substitution is primitive |

**Label discipline used below.**
- *Numerical*: a floating eigenvalue with its residual.
- *Rigorous finite-dimensional certificate*: an exact rational Rayleigh quotient, or a Higham-bounded Cholesky, about a finite matrix.
- *Infinite-volume theorem*: a proof plus certificates that bound E_\*.
- *Conjecture*: anything resting on a ratio hypothesis or an observed pattern.

---

## 2. The extremal problem and the dataset (Part II)

**The problem.**
- The configuration space is the 1098 gauge classes of proper Chair44 decorations.
- The target is E_\*(r) = inf σ(H_Y) for Y in the hull Ω_r.
- **The primary objective is the best certified lower bound on E_\*(r)**, not the largest finite-level eigenvalue. For every class it is
  - the larger of the certified free-supertile bound F₃ (Theorem X.2), certified by Higham's Cholesky test;
  - and, for Stage B candidates, the localization bound Λ_R (Phase VII Thm 7.1, generalized to every decoration in `phase10_ims.py`).
- The upper side uses exact rational Rayleigh quotients:
  - of the level-4 ground vector, for every class;
  - of the level-5 ground vector, for every Stage B class;
  - of the level-6 vector and the minimizing localization ball, for the leading classes.

**Three quantities, never mixed.**
- Y_L(r) = λ_min(H_r^{(L)}) of the pinned level-L supertile. It is a finite-matrix eigenvalue, numerical or certified.
- E_\*(r) = inf σ(H_r).
- The certified interval [best lower, best upper] ∋ E_\*(r).

The leaderboard ranks by the third, and reports the first only as evidence.

**Operator normalization, boundary conditions and volume.** These are fixed in the conventions table above.
- The pinned (Dirichlet-type) operator is the compression 24 − A_U on a finite patch.
- The free (Neumann) operator is Deg − A_U.
- Periodic approximants use Bloch boundary conditions on the period lattice 2ᵏΛ₇.
- Volume is counted in tiles.

**The evaluation record.** It has one row per gauge class (`phase10_dataset.json`/`.csv`, 1098 rows). The seven items the brief requires map to these fields:

| required item | fields | computed for |
|---|---|---|
| legal local configurations, admissibility | `n_types1` (Φ-closed legal 1-star types), `n_types1_in_T5`, `phi_complete`, `phi_self_loops`, `phi_perron`, `phi_second`. All decorations are proper (det = +1), with the same chair geometry | all |
| gauge-invariant curvature and Wilson loops | plaquette and two-cycle Q₈-class counts at L3. 2 × 2 Wilson-loop class fractions (V-B) | all |
| local frustration, spatial correlations | U₀ (pinned 1-star minimum), U₁ (pinned σ(τ) minimum), μ₀ (free 1-star minimum), frequency of the U₁-minimising type. V-B correlation statistics (`Ct_*`, `Cp_*`, `pair_m1`, `cv_*`) | all |
| spectral data at several levels | Y₁…Y₄, F₁…F₄, closed-walk moments m₂…m₈ (L3) | all |
| | Y₅ with residual | 222 classes (Stage B, benchmarks, registered random sample of 200) |
| | F₅ | the first classes of the level-5 run only. It was dropped because the free level-5 eigensolve converges slowly, and level 4 already gives the matched-volume comparison |
| | Y₆, U₂, U₃ | the deep stage: 1387, 1389, 1391, FR30, 901 |
| certified bounds | certified F₃ lower bound, exact rational Y₄ upper bound | all |
| | exact Y₅ upper bound | Stage B |
| | Λ_R, D_R | candidates |
| finite-size drift, boundary sensitivity | Y₃ − Y₄ drift. Y₄ − F₄ (pinned versus free at matched volume). Perturbation sensitivity: max \|ΔY₄\| over the 16 single-child frame changes. Periodic approximants | all; periodic for benchmarks |
| cost and certificate strength | wall time per record. Each bound carries its certificate type in the leaderboard | all |

**Ranking.**
- The leaderboard (`phase10_leaderboard.json`/`.csv`) is sorted by the best certified lower bound.
- A Pareto frontier is computed over seven objectives:
  - certified lower bound (max);
  - certified bracket width (min);
  - level drift (min);
  - free-pinned gap (min);
  - perturbation sensitivity (min);
  - non-trivial plaquette fraction (max);
  - number of legal 1-star types, as a proxy for rule and certificate complexity (min).
- **The mandatory benchmarks:**
  - FR30's class;
  - its Abelian shadows χ₁, χ₂;
  - the trivial and Z₂ controls;
  - five scrambled controls (Phase VIII);
  - FR30's periodic approximants;
  - the 937/938 pair;
  - the ℤ³ pair (§7).

**Numerical error control and hardware** (applies to every certificate in this report).
- **Upper bounds** are exact rational Rayleigh quotients of integer vectors. The operators have Gaussian-integer entries, so integer arithmetic is exact.
- **Lower bounds** come from a floating-point Cholesky factorization of the real form of H − μ, with μ a 20-bit dyadic rational. Then λ_min(H) ≥ μ − γ_{N+1}‖L‖_F²(1 + 2(N² + 1)u)·1.0001, by Higham, *Accuracy and Stability of Numerical Algorithms* (2002), Thm 10.3. The localization balls add the entrywise error of their amplification factors.
- That bound holds for every order of evaluating the inner products. So it covers three implementations used here:
  - Phase VII's column algorithm;
  - LAPACK's blocked `dpotrf` (OpenBLAS, conventional matrix multiplication), which this phase switched to. It agrees with the column algorithm to 10⁻¹³ and is 5–8× faster;
  - the GPU path below.
- **GPU** (from the QIS project's set-up):
  - Hardware and software: an NVIDIA RTX 5080 (sm_120), with torch 2.11+cu128 from the existing venv `C:\Users\super\.venvs\qisgpu`. The system torch 2.6+cu124 has no Blackwell kernels, and that venv's CuPy cuSOLVER returns `EXECUTION_FAILED` on this card.
  - Division of labour: CPU workers build each localization ball's sparse operator. The GPU assembles the dense real form by exact copies, factors it in float64 (`cholesky_ex`), and reads the breakdown flag.
  - The bound is applied with **u = 4·2⁻⁵³**, a four-ulp margin per operation. It holds for IEEE double in any summation order, with or without FMA, even if the vendor's division or square root is not correctly rounded.
  - Validation on the 747 FR30 R = 8 balls: pass/fail agrees with the CPU path on every ball, and the certified values differ by ≤ 10⁻⁸ (the larger u).
  - Speed: an N = 6600 float64 factorization takes 0.14 s on the GPU, against 4.1 s for one loaded CPU core.
- **Eigensolver accuracy**: residuals are reported with every float eigenvalue (≤ 10⁻⁹ unless stated). No float eigenvalue is used as a bound without a certificate.

---

## 3. Discovery (Part III)

### 3.1 Stage A: the census, screened

**What was computed for every one of the 1098 classes** (`phase10_census.py`, `phase10_certify.py`):
- Y₁…Y₄, F₁…F₄;
- plaquette and two-cycle class counts, and closed-walk moments, at L3;
- the Φ-closed legal 1-star types with U₀, U₁, μ₀ and the type-substitution graph;
- a certified bracket [F₃ certified, Y₄ exact Rayleigh].

| quantity | min | median | max | FR30 (class 1386) rank | class 1387 rank |
|---|---|---|---|---|---|
| Y₂ | 8.618 | 10.674 | 11.805 | 471 | 20 |
| Y₃ | 6.650 | 8.273 | 9.956 | 10 | **1** |
| Y₄ | 5.665 | 7.630 | 9.517 | **6** | **1** |
| F₁ | 1.672 | 3.063 | 4.026 | 695 | 350 |
| F₄ | 3.901 | 5.276 | 6.297 | 615 | 120 |
| certified lower (F₃) | 3.788 | — | 6.120 (class 3362) | 544 | 71 |

**Census-wide certified statements** [C], each by Theorem X.2 with a Higham Cholesky certificate and an exact rational Rayleigh quotient:
- **Every proper Chair44 frame rule has E_\* ≥ 3.788.** So every one of the 6561 rules has a strictly positive spectral floor. Theorem X.3 explains why: every class already has a non-flat level-1 supertile, with F₁ ≥ 1.672.
- **806 of the 1098 classes have E_\* ≤ Y₄ < 7.954292 ≤ E_\*(FR30)**, certified. So they are rigorously below FR30.
- Only **5 classes have Y₄ above FR30's**, and 9 have Y₃ above it.

**The high-Y region of the census surrounds FR30** [E, an observed association].
- Distance is the number of differing child-frame digits to the nearest member of FR30's class.
- The two best classes are single-child variants of FR30. In class 1387 (decorations 4753 and 4754) only the centre child's frame differs; in class 1389 (4755 and 4758) only the first octant child's.
- The next three (1391, 1144, 901) are at distance 2.
- 13 of the top 22 classes by Y₄ lie within distance 2 of FR30's class. Over the whole census the share is 67/1098 = 6.1 %.
- FR30 is therefore near a high-Y region of decoration space, but not at its top.

**Φ-closure.**
- In 1086 of 1098 classes, the level-5 supertile misses rare legal 1-star types. The closure adds them.
- In 316 classes the radius-1 minimum U₁ is attained on such a closure-only type, up to 0.33 below the value from T₅ alone.
- FR30's and 1387's level-5 sets are already closed (72 and 90 types).
- Every radius-1 quantity and every localization enumeration here uses the closure. That includes a correction to `phase10_ims.py` made before any bound for a non-closed class was computed.

**Descriptor audit** (`phase10_descriptors.json`). For each descriptor it records:
- resolution: the number of distinct values over the 1098 classes;
- redundancy: the largest |Spearman ρ| with another descriptor;
- the **937/938 falsification test**: does the descriptor separate the pair?
- rank correlation with Y₄ (all classes) and with Y₅ (the registered random sample).

| descriptor | distinct values (of 1098) | separates 937/938 | Spearman ρ with Y₄ (all) | ρ with Y₅ (held-out sample) | most redundant with (abs ρ) |
|---|---|---|---|---|---|
| f₋₁ (plaquette −1 fraction, L3) | 607 | **no** | 0.48 | 0.46 | two-cycle −1 fraction (0.93) |
| f_traceless | 729 | **no** | 0.07 | 0.07 | two-cycle traceless fraction (0.84) |
| two-cycle +1 fraction | 63 | **no** | −0.35 | −0.45 | two-cycle traceless (0.80) |
| moments m₂, m₃ | 83, 445 | **no** | −0.63, −0.71 | −0.67, −0.72 | m₃ ~ m₅ (0.996) |
| moments m₄, m₅ | 1091, 1097 | yes | −0.84, −0.73 | −0.82, −0.73 | m₄ ~ m₆ (0.98) |
| U₀ (pinned legal 1-star minimum) | 866 | yes | 0.84 | 0.87 | U₁ (0.94) |
| **U₁ (pinned σ(1-star) minimum)** | **1098** | **yes** | **0.90** | **0.955** | U₀ (0.94) |
| μ₀ (free 1-star minimum) | 918 | yes | 0.70 | 0.74 | U₀ (0.81) |
| legal 1-star type count | 789 | **no** | −0.13 | −0.11 | Φ self-loops (0.35) |
| hierarchy: depth enrichments, hierarchical variances, Φ self-loops | 253–1089 | **no** | −0.17 to −0.26 | −0.19 to −0.28 | each other (0.79–0.93) |
| Y₂, Y₃ | 1098 | yes | 0.81, 0.89 | 0.82, 0.79 | moments (0.91) |

**Reading the table.**
- Every frequency-type curvature descriptor fails the 937/938 test, as Theorem 9.1 requires: the plaquette and two-cycle class fractions, and the moments up to order 3.
- So does every registered hierarchy descriptor.
- The descriptors that pass are spectral or environment-type: U₀, U₁, μ₀, the moments m₄–m₈, and Y_L.
- The class fractions are redundant with each other (|ρ| 0.80–0.93) and weakly predictive. The traceless fraction carries almost no information about the floor (ρ = 0.07).

**Cheap selection criteria** (`phase10_criteria.json`): the rank agreement of each cheap quantity with the deeper level, and its top-k recall.

| cheap criterion | ρ with Y₄ (1098 classes) | top-20 recall in its top 20 / 40 / 100 | ρ with Y₅ (held-out sample of 200) | top-10 recall in its top 10 / 20 / 50 |
|---|---|---|---|---|
| Y₂ | 0.81 | 0.05 / 0.10 / 0.45 | 0.82 | 0.2 / 0.4 / 0.9 |
| Y₃ | 0.89 | 0.60 / 0.80 / **1.00** | 0.79 | 0.3 / 0.6 / 0.9 |
| F₂, F₃, F₄ | 0.80–0.84 | ≤ 0.15 / ≤ 0.30 / ≤ 0.55 | 0.82–0.84 | 0.2 / 0.5–0.6 / 0.7–0.9 |
| U₀ | 0.84 | 0.50 / 0.55 / 0.70 | 0.87 | 0.5 / 0.7 / 1.0 |
| **U₁** | **0.90** | 0.60 / 0.70 / 0.70 | **0.955** | **0.7 / 0.9 / 1.0** |
| μ₀ | 0.70 | 0.60 / 0.60 / 0.65 | 0.74 | 0.5 / 0.6 / 0.9 |

**The prediction deliverable.**
- **U₁ is the criterion that selects a promising rule before any expensive eigensolve.** It is the minimum, over the legal 1-star types, of the pinned ground energy of the once-inflated 1-star: patches of about 200 tiles, versus 32 768 for Y₅. It is gauge-invariant.
- On the held-out sample it ranks Y₅ with ρ = 0.955, and its top 20 contains 9 of the sample's top 10.
- It is the radius-1 instance of Theorem X.7's "worst legal environment": an *upper* bound on E_\* that tracks the floor because the floor is set by the worst environment.
- For the very top of the census, Y₃ recalls better: all of the top 20 by Y₄ lie in Y₃'s top 100.
- None of these criteria is a proof. Their accuracy is empirical (§5).

### 3.2 Stage B: deep confirmation

**Selection** (registered before the census existed; `phase10_stageB_selection.json`):
- the 15 classes with the largest Y₄;
- the 5 with the largest F₄ not already chosen;
- the benchmarks.

The 20 selected classes are 1387, 1389, 1391, 1144, 901, 1386 (FR30), 929, 1146, 1150, 141, 156, 1390, 902, 933, 928, 3364, 1599, 3362, 1371 and 2030.

**Level 5** (`phase10_y5.jsonl`).
- Every selected class and benchmark was computed. Eigensolver residuals are ≤ 7·10⁻¹⁰.
- Each Y₅ is certified from above by an exact rational Rayleigh quotient, which is a rigorous upper bound on E_\*.

| class | Y₃ | Y₄ | Y₅ ≥ E_\* (exact) | Y₄ − Y₅ | legal 1-star types |
|---|---|---|---|---|---|
| **1387** | 9.9559 | 9.5169 | **9.392829** | 0.124 | 90 |
| 1389 | 9.7869 | 9.3464 | 9.218731 | 0.128 | 102 |
| 1391 | 9.6711 | 9.1738 | 9.122101 | 0.052 | 104 |
| **1386 (FR30)** | 9.3785 | 8.9196 | **8.797011** | 0.123 | 72 |
| 901 | 9.6596 | 9.0825 | 8.794624 | 0.288 | 239 |
| 1144 | 9.6626 | 9.1036 | 8.776802 | 0.327 | 427 |
| 929 | 9.3360 | 8.9002 | 8.764472 | 0.136 | 286 |
| 1390 | 9.2285 | 8.6858 | 8.591907 | 0.094 | 96 |
| … 12 more selected classes | | | 7.78 – 8.52 | | |
| 937 / 938 | 8.4910 / 8.2134 | 8.0357 / 7.7855 | 7.972840 / 7.728538 | 0.063 / 0.057 | 201 / 201 |

**What level 5 changes.**
- Classes 901 and 1144 beat FR30 at level 4 but **fall below it at level 5**. Their level-4 advantage was a finite-size effect, with large decrements of 0.29 and 0.33.
- This is the failure mode the brief warns against: picking a winner from level-4 values alone.
- The three classes that stay above FR30 (1387, 1389, 1391) have small, FR30-like decrements (0.05–0.13).

**A structural association** [E; a correlation, not a mechanism].
- The four classes that stay at the top through level 5 are 1387, 1389, 1391 and FR30. All four are among the **six classes with the fewest legal 1-star types**: 72–104, against a census median of 1101. The other two have 46 types and 96 types (class 1390).
- The classes that fall at level 5 have many more: 901 has 239 and 1144 has 427.
- Census-wide the rank correlation between type count and Y₄ is only −0.13.
- So having few legal environments is shared by the top rules but far from sufficient.
- It fits Theorem X.7: the floor is the minimum over legal environments, so a rule that admits fewer environments has fewer chances to admit a weakly frustrated one.

**The deep stage** (pre-declared: the five selected classes with the largest Y₅, which here include FR30; `phase10_deep.jsonl`, `phase10_stageB_promotion.json`):

| class | L3 reconstruction (two builders) | certified Y₄ enclosure | U₂ | U₃ (20 lowest) | Y₆ ≥ E_\* (exact; residual) |
|---|---|---|---|---|---|
| **1387** | 0.0 | [9.5168643, 9.5168661] | 9.4963 | 9.3861 | **9.3679502** (7·10⁻¹²) |
| 1389 | 0.0 | [9.3464284, 9.3464301] | 9.3147 | 9.2316 | 9.2104998 (6·10⁻¹²) |
| 1391 | 0.0 | [9.1738468, 9.1738491] | 9.2269 | 9.1357 | 9.1104007 (2·10⁻¹²) |
| FR30 | 0.0 (L4 enclosure [8.9196325, 8.9196344]) | — | 8.8608 | 8.7795 | pending (8.770134 from Phase V-E) |
| 901 | pending | pending | pending | pending | pending |

- The level-6 sequence keeps the order 1387 > 1389 > 1391 > FR30.
- 1387's certified enclosure tightens to **[8.7644994, 9.3679502]**.
- The last-ratio extrapolations (conjectural [X]) are about 9.362 (1387), 9.200 (1389) and 9.107 (1391), against FR30's 8.7639.

**Promotion checks** (`phase10_stageB.py promote`): pending until the FR30 and 901 deep records finish. For 1387, 1389 and 1391 every computed check passes: reconstruction, residuals below 10⁻⁸, certified level-4 enclosure, monotone and convergent levels.

**Certified infinite-volume bounds** (`phase10_ims.jsonl`; Theorem X.7):

| rule | R | legal 1-star types | distinct R-balls (tiles) | **Λ_R certified** (≤ E_\*) | D_R (≥ E_\*) | mode, device |
|---|---|---|---|---|---|---|
| FR30 (4752) | 6 | 72 | 325 (118–145) | 3.6555586 | 9.4166 | full, CPU; reproduces Phase VII |
| FR30 | 8 | 72 | 747 (290–321) | 6.5627832 | 9.0515 | full, CPU; reproduces Phase VII |
| FR30 | 12 | 72 | 2315 | 7.9542923 | 8.8570 | Phase VII |
| 1387 | 8 | 90 | 1450 (290–321) | 7.3114948 | 9.7299 | full, CPU |
| **1387** | **14** | 90 | 7527 (1580–1640) | **8.7644994** | — | μ = 2297561/262144, GPU (29 min) |
| 1387 | 15 | 90 | 10321 | pending | — | μ ≈ 8.80, GPU |
| 1389 | 8 | 102 | 1431 | 7.0091524 | 9.4621 | full, CPU |
| 1391 | 8 | 104 | 1614 | 6.9198389 | 9.4009 | full, CPU |
| 901 | 8 | 239 | 5728 | 6.5510740 | 9.0556 | full, CPU |
| 1144 | 8 | 427 | 11805 | 5.4726372 | **8.1414086** (exact) | full, CPU |
| twin 539311 | 8 | 90 | 1450 | 7.3378239 | 9.7536 (exact) | full, CPU |
| twin 539311 | 14 | 90 | 7527 | pending | — | μ = 2297561/262144, GPU |
| twin 539291 | 8 | 97 | 1532 | 7.1408386 | 9.6034 (exact) | full, CPU |

**Reading the table.**
- At the common radius R = 8, both Λ_R and D_R order the rules as every finite level does: 1387 > 1389 > 1391 > FR30 ≈ 901, and each twin above its original.
- **The R = 14 certificate puts 1387's floor above FR30's certified upper bound**: E_\*(1387) ≥ 8.7644994 > 8.7642270 ≥ E_\*(FR30).
  - The completeness hypotheses hold: the Φ-closure equals the T₅ type set (90 types), the frame substitution is primitive with M² > 0, and no ball was rejected as incomplete.
  - Every one of the 7527 balls passes the Cholesky test. The certified bound is μ minus a rounding margin below 3·10⁻⁷.
- **Class 1144's environment minimum D₈ = 8.1414 is far below its supertile values** (Y₄ = 9.10, Y₅ = 8.78). Its weakest legal environment is a rare 1-star type absent from T₅ (427 legal types, 365 in T₅). The certified upper bound E_\*(1144) ≤ 8.1414 is the exact Rayleigh quotient on that ball.


### 3.3 Stage C: improper frames, a controlled extension outside the census

**Specification** (fixed before running; `phase10_improper.py` docstring):

| | |
|---|---|
| configuration space | each child takes any of the 6 coordinate permutations (3⁸ → 6⁸ = 1 679 616 decorations). Proper decorations are the subset with det = +1 |
| what is held fixed | geometry: every permutation maps the chair to itself, so tiles and panels are identical. Link formula, group (Q₈), operator 24 − A_U, normalization, volume convention |
| what changes | only admissibility: frames with det = −1 (reflections) are allowed |
| gauge action | unchanged. S₃ axis permutations act as before, and S₃-orbit representatives are screened. Gauge merging beyond S₃ is not computed. Exact spectral duplicates are removed at the end |
| baseline | the proper census, the same pipeline restricted to det = +1 |
| feasibility | Y₂ for all 6⁸ (batched dense, ≈ 2000 per 3 s). Sparse Y₃ for the top half by Y₂ of the orbit representatives. Y₄ for the top 10 % by Y₃. Y₅ for the 10 best distinct |
| funnel calibration | on the proper census, before any extended value was computed: the top 50 % by Y₂ recall all of the top-20 classes by Y₄, and the top 10 % by Y₃ recall all of the top-20 by Y₄. An earlier draft funnel (top 1.8 % by Y₂) recalled only 5 % and was discarded |

**Results** (`phase10_improper_*.json`, `phase10_improper_certify.jsonl`).

**The funnel.**
- Y₂ for all 1 679 616 decorations, which form 280 332 S₃-orbit representatives.
- Y₃ for the 140 166 representatives with Y₂ ≥ the median (11.044).
- Y₄ for the top 10 % by Y₃ (14 016).
- Y₅ for the 10 best spectrally distinct ones.
- 55 of the 14 016 are proper, and the top proper classes reappear (1387, 1389, 1391, 1144, 901). That is a check on the funnel.

**Positivity does not need properness.**
- Every one of the 6⁸ decorations has a non-flat level-1 supertile: min F₁ = 1.6716 for proper and improper alike (`phase10_improper_f1.json`).
- With Theorem X.3, every decoration with an irreducible frame substitution therefore has E_\* > 0.

**The best extended decorations are mirror twins.**
- The top improper candidates are exactly the top proper classes with every child frame right-multiplied by the transposition S = (x ↔ y), which has det −1:
  - j = 539311 = 1387·S;
  - j = 539291 = 1389·S;
  - j = 539288 = 1391·S (each up to S₃ conjugation).
- The geometry does not change, because the chair is symmetric under coordinate permutations. Only the link field changes.
- Every child has det −1, so the frame substitution is irreducible with period 2 (48 frames): each generation alternates handedness.
- Hence:
  - every tiling of the hull has uniform handedness;
  - the hull's two halves are exchanged by a global mirror Q, which leaves every link unchanged since (QM)ᵀ(Qn) = Mᵀn;
  - E_\* is well defined and equal on both halves;
  - each half is minimal under σ²;
  - Theorems X.2, X.3 and X.7 apply, since their completeness arguments need irreducibility, not aperiodicity.

| | 1387 | **twin 539311** | 1389 | twin 539291 | FR30 | FR30's twin |
|---|---|---|---|---|---|---|
| Y₃ | 9.95592 | **9.95733** | 9.78693 | 9.79181 | 9.37847 | 9.22325 |
| Y₄ (certified enclosure) | [9.516864, 9.516866] | **[9.522249, 9.522251]** | [9.346428, 9.346430] | 9.33435 | [8.919632, 8.919634] | 8.70178 |
| Y₅ (exact upper bound) | 9.392829 | **9.415853** | 9.218731 | 9.271826 | 8.797011 | — |
| Y₆ | 9.367950 | pending | 9.210500 | pending | 8.770134 (Phase V-E) | — |
| D₈ (exact upper bound on E_\*) / Λ₈ (certified) | 9.7299 / 7.3115 | **9.7536 / 7.3378** | 9.4621 / 7.0092 | 9.6034 / 7.1408 | 9.0515 / 6.5628 | — |
| legal 1-star types, distinct 8-balls | 90, 1450 | 90, 1450 | 102, 1431 | 97, 1532 | 72, 747 | — |

**Handedness is not a uniform improvement.**
- FR30's twin is lower: Y₃ 9.2233 against 9.3785, Y₄ 8.7018 against 8.9196.
- 1389's twin is lower at level 4 (9.3344 against 9.3464) but higher at level 5 (9.2718 against 9.2187).
- 1391's twin is lower at level 5 (9.1124 against 9.1221).

**A large Y₃ alone misleads here too.** The improper decoration with the largest Y₃ in the screen (10.3885, j = 343951) falls to Y₅ = 8.5920.

### 3.4 Which discovery target was achieved

| discovery target (brief) | achieved? | evidence |
|---|---|---|
| a candidate that rigorously exceeds FR30's best certified lower bound | **yes** | Λ₁₄(1387) ≥ 8.7644994, above FR30's Λ₁₂ = 7.954292 and above even FR30's certified *upper* bound |
| a demonstrably higher asymptotic floor | **yes, certified** | E_\*(1387) ≥ 8.7644994 > 8.7642270 ≥ E_\*(FR30); separation ≥ 2.7·10⁻⁴ |
| a structural property FR30 does not possess | **yes** | the handedness-alternating frame substitution (period 2, every child det −1) of the Stage C leader 539311, 1387's mirror twin. Its R = 14 certificate against FR30 was still running on the GPU when this report was written (no ball had failed after 2500 of 7527): pending. |
| the extremal rule of the census | **not decided** | 1387 is certified above 1094 of the other 1097 classes. 1389 and 1391, and the twin, are beyond both methods (§12) |

---

## 4. Theorems (Part IV)

**Which decisive outcomes were reached.**
- **B, insufficiency:** Theorem X.5, certified in infinite volume. It is the strong form: equal holonomy class on every plaquette, with gauge-equivalent Abelian shadows.
- **C, classification:** Theorem X.3, positivity if and only if some finite supertile is non-flat, with an explicit lower bound and a census-wide application (E_\* ≥ 3.788 for every proper rule).
- **D, no-go:** Theorem X.4. No lower bound in terms of curvature frequencies exists.
- **A, quantitative, in its standard form:** Theorem X.7. The lower bound's input is the *set* of legal local environments, a gauge-invariant support-type datum. It is sharp to O(R⁻²), uniformly in the rule.
  - A sharp-cutoff radius-1 version is valid but far from sharp (remark after X.7).
  - What F can legitimately depend on is therefore which environments are legal, not how often curvature occurs.

**General setting.**
- G = (V, E) is a countable, locally finite multigraph with uniformly bounded degree. Each oriented edge e = (v → w) carries U_e ∈ U(n), with U_ē = U_e⁻¹.
- The covariant difference is (D_Uψ)_e = ψ(v) − U_eψ(w).
- The free operator is H_U = D_U*D_U, with quadratic form ⟨ψ, H_Uψ⟩ = Σ_e |ψ(v) − U_eψ(w)|². It is bounded, self-adjoint and ⪰ 0.
- On a finite subset K of an infinite d-regular graph, the pinned operator d − A_U restricted to K is the compression P_K H_U P_K.
- The free operator of K, H_U(K), keeps only the edges inside K.

### Theorem X.1 (flatness) [P, standard]

Let G be connected and U a U(n)-connection. The following are equivalent:
- (i) U is gauge-trivial, i.e. U_e = g(v)g(w)⁻¹ for some g : V → U(n);
- (ii) every closed walk has holonomy I;
- (iii) for one spanning tree, every fundamental cycle has holonomy I.

If G is finite and U takes values in SU(2), they are also equivalent to:
- (iv) λ_min(H_U) = 0.

*Proof.*
- (i)⇒(ii): the holonomy telescopes. (ii)⇒(iii) is immediate.
- (iii)⇒(i): set g(root) = I and transport g along the tree. Each non-tree edge closes a fundamental cycle, whose trivial holonomy is exactly the gauge relation on that edge.
- (iv): ker H_U is the space of parallel sections, ψ(v) = U_eψ(w) on every edge.
  - A nonzero parallel section gives a vector ψ(v₀) ≠ 0 fixed by every holonomy at v₀.
  - An element of SU(2) with eigenvalue 1 has eigenvalues 1 and 1, so it is I.
  - Hence ker H_U ≠ 0 ⟺ all holonomies are trivial ⟺ (ii). ∎

*Remarks.*
- For U(n) with n ≥ 2 or for general groups, (iv) is weaker than flatness: a common fixed vector suffices.
- The statement is standard: [L1] Prop. 3.2 for general groups (balance ⟺ gauge-trivial); [L2] Prop. 2.1 for U(1).

### Theorem X.2 (bracketing on substitution hulls) [P; standard method]

Let r be any Chair44 decoration, proper or improper, and Y any tiling of its hull Ω_r (every finite patch of Y occurs in some σ_rⁿ(tile)). For all k, L ≥ 1:

  **F_k(r) := λ_min H_free(T_k(r))  ≤  inf σ(H_Y)**,  and, if Ω_r is minimal,  **inf σ(H_Y) ≤ Y_L(r) := λ_min H_pin(T_L(r))**.

Moreover:
- F_k is non-decreasing in k;
- Y_L is non-increasing in L, and Y_L ↓ E_\*(r) when Ω_r is minimal.

*Proof.*
- **Lower bound.** Take ψ finitely supported on Y and a finite patch P ⊃ supp ψ that contains every tile adjacent to supp ψ.
  - P occurs in some Q = σⁿ(tile with frame g). So ⟨ψ, H_Yψ⟩ equals the same form computed inside Q.
  - Q is the disjoint union of its level-k supertiles σᵏ(child). Dropping the panel terms between them (each ≥ 0) gives ⟨ψ, H_Yψ⟩ ≥ Σ_S ⟨ψ|_S, H_free(S) ψ|_S⟩.
  - Each S = σᵏ(tile with frame h) carries exactly the links of T_k(r). Its tiles have frames h·M_t and positions h·x_t, and the Pauli formula is invariant: (hM)ᵀ(hn) = Mᵀn for every signed permutation h, proper or improper.
  - So H_free(S) is H_free(T_k(r)), and ⟨ψ, H_Yψ⟩ ≥ F_k ‖ψ‖².
  - Neither recognizability nor minimality is used.
- **Upper bound.** T_L(r) is a patch of every tiling of a minimal hull, and the pinned operator is the compression of H_Y to it.
- **Monotonicity.**
  - H_free(T_{k+1}) ⪰ ⊕ of the 8 free child supertiles, each equal to H_free(T_k).
  - T_L embeds in T_{L+1} with identical links, which gives interlacing.
- **Convergence of Y_L.** T_L contains balls of radius ∝ 2ᴸ; then use minimality. ∎

*The lower side is not sharp in general* (§3.1). F_k saturates below E_\*: for FR30, F₄ = 5.21 against E_\* ≥ 7.954, because free supertiles carry surface states (Phase V-A). The pinned side converges.

### Theorem X.3 (positivity classification) [P; census application C]

For every decoration r with a minimal hull:

  **E_\*(r) > 0  ⟺  the connection on some finite supertile T_k(r) is not flat  ⟺  F_k(r) > 0 for some k.**

The first such k gives the explicit bound E_\*(r) ≥ F_k(r).

*Proof.*
- ⇐: Theorem X.1(iv) applies, because T_k is a connected finite graph with SU(2) links. Then Theorem X.2.
- ⇒: if every T_k is flat, every legal patch lies in some flat T_k. Gauge the connection to the identity on T_L. A product-sine bump on T_L then has pinned Rayleigh quotient O(4⁻ᴸ), so E_\* ≤ Y_L → 0. ∎

*Census application* [C].
- All 1098 classes have a primitive frame substitution (`frame_primitivity`, in the dataset), so every proper rule has a minimal hull.
  - One class reaches only 8 frames.
  - The other 1097 reach all 24: M² > 0 for 518 classes, M³ > 0 for 578, M⁴ > 0 for 1.
- Every class has a non-flat level-1 supertile (F₁ ≥ 1.672).
- **Hence every one of the 6561 proper rules has E_\* > 0. Certified: E_\* ≥ F₃ ≥ 3.788 for all of them.**
- The same holds in the extended space of Stage C: all 6⁸ decorations have F₁ ≥ 1.6716. Positivity does not come from properness.

### Theorem X.4 (no lower bound from frustration fractions) [P, with an explicit family]

For every R ≥ 1 there is a periodic Pauli-frame Q₈ connection U_R on ℤ³ with:
- a fraction of non-trivial plaquettes ≥ 0.78;
- **E_\*(U_R) ≤ 6(1 − cos(π/(R + 1))) → 0**.

Hence no inequality E_\*(U) ≥ F(class frequencies of U) with F > 0 holds for any F that is positive at frequency vectors near those of U_R.

*Construction and proof.*
- Take period 2R. Put constant frames on an R × R × R island, which makes it flat with trivial links, and independent random proper frames elsewhere.
- Test with the product-sine bump on the island. Its Rayleigh quotient for 6 − A_U is exactly the Dirichlet value 6(1 − cos(π/(R + 1))), and it bounds E_\* from above.
- Measured fractions of non-trivial plaquettes: 0.85, 0.82, 0.80, 0.79, 0.78 for R = 2, 3, 4, 6, 8 (`phase10_z3_noflat.json`).
- The mechanism is general: on any graph with arbitrarily large balls, flat islands make the floor arbitrarily small at a fixed frustration density.
- This is the discrete analogue of the random-flux Lifshitz mechanism [L5]. ∎

### Theorem X.5 (the plaquette holonomy classes do not determine the floor, in infinite volume) [P + C]

There are two period-2 Pauli-frame Q₈ connections A and B on ℤ³ (frames in `phase10_z3_classpairs.json`) with these properties:
- **the same Q₈ conjugacy class on every plaquette**: +1, −1, or ±q_k with the same axis k. Hence:
  - identical plaquette traces, class counts and Wilson action;
  - **gauge-equivalent Abelian shadows** χ_k∘U_A ≅ χ_k∘U_B for k = 1, 2, 3, so their shadow floors are identical (1.528, 1.528, 0);
- **E_\*(A) ≤ 177943087298/440306385467 = 0.40413470 < 0.58578587 ≤ E_\*(B)**, a certified separation ≥ 0.1816.

*Proof.*
- **The shadows.** χ_k is a class function on Q₈ and a homomorphism to {±1}. So χ_k∘U_A and χ_k∘U_B have equal holonomy around every plaquette. The plaquettes generate the cycle space of ℤ³, so the two shadows are gauge-equivalent on ℤ³ (X.1, (iii)⇒(i)) and isospectral as operators on ℓ²(ℤ³).
- **The upper bound for A.** The exact Rayleigh quotient of the θ = 0 Bloch matrix, whose entries are Gaussian integers. Every Bloch matrix bounds the floor from above.
- **The lower bound for B.** Theorem X.2 on ℤ³: partition ℤ³ into 2 × 2 × 2 cells and drop the links between them. The free cell's bottom is certified by the Higham Cholesky test. ∎

*How it was found.*
- Among 40 000 random period-2 fields (seed 7), 3817 distinct full plaquette class fields occur, and 3672 of them occur more than once.
- **1943 of the shared class fields carry numerically different floors.**
- A weaker pair, matched only in its trace field (`phase10_z3_pairs.json`), has the same certified numbers. Its class fields differ on 16 of 24 plaquettes, and its shadow floors are permuted.

*Meaning.* The floor depends on how the non-Abelian plaquette holonomies are oriented relative to one another, data carried by longer loops. No plaquette-level summary records it, not even the complete conjugacy-class field, which determines every Abelian shadow. Kenyon's formula (§8) shows the determinant needs the traces of *all* cycles.

### Theorem X.6 (non-Abelian structure needs three dimensions) [P]

In dimension d = 2, where frames are 2 × 2 signed permutation matrices of the plane, every Pauli-frame connection takes values in {±1, ±iσ_z} ≅ ℤ₄, so it is Abelian.

*Proof.* The normals are ±e_x and ±e_y, so σ·(Mᵀn) ∈ {±σ_x, ±σ_y}. Every link is then a product of two of these, and σ_xσ_y = iσ_z. ∎

The FR30-type construction therefore produces genuinely non-Abelian holonomy only in d ≥ 3.

### Theorem X.7 (localization for every rule: the floor is the worst legal environment) [P; Phase VII Thm 7.1 generalized]

Let r be any Chair44 decoration, proper or improper, whose frame substitution is irreducible. It is primitive for all 6561 proper rules (the census application of Theorem X.3). It has period 2 for the mirror twins of Stage C, whose hull splits into two mirror halves with equal floors (§3.3). Let 𝒯(r) be the Φ-closure of the 1-star types of T₅(r). For R ≥ 6 (the range of Phase VII Thm 7.1) and m with 2ᵐ ≥ R:
- let 𝓑_R(r) be the set of R-balls around the tiles of the central level-m supertile of σᵐ(τ), τ ∈ 𝒯(r);
- 𝓑_R(r) is checked to have no incomplete ball.

Then 𝓑_R(r) contains every legal R-ball of Ω_r up to translation, and

  **Λ_R(r) := min_{B∈𝓑_R} λ_min(24 − Ã_ρ)|_B ≤ E_\*(r) ≤ D_R(r) := min_{B∈𝓑_R} λ_min(24 − A_U)|_B**, with D_R − Λ_R ≤ ε(ρ) ≤ K(ρ)S₁/ρ²,

where:
- ρ = R − 311/175 and c(η) is Phase VII's overlap function.
- S₁(r) = max over legal 1-stars of Σ_f |h_f|², with h_f the centroid offset across the 24 panels of the central tile.
- K_r(ρ) = (π²/6)/(1 − π² h_max(r)²/(6ρ²)).

For FR30, 1387 and 1389 these were computed on the Φ-closed type sets. All three have S₁ = 4734/49 and h_max = 15/7, which are Phase VII's values. In general |h_f| ≤ 2r_c = √619/7, so the rate is uniform in r. Consequently

  E_\*(r) = lim_{R→∞} min_{B ∈ 𝓑_R(r)} λ_min(H_B), uniformly in r at rate O(R⁻²).

The certified lower bounds Λ_R are computed directly from the amplified matrices, so they use none of these constants.

*Proof.*
- **The inequalities.** Phase VII's IMS identity uses only:
  - (a) the chair geometry: the panel set, the centroid distances, the constants S₁ and r_c;
  - (b) degree 24 on every tiling;
  - (c) the fact that the localized pieces are legal R-balls.

  (a) and (b) do not depend on the decoration.
- **Completeness of 𝓑_R** (c).
  - σ maps Ω_r onto itself, since every legal patch lies inside σ of a legal patch (compactness); recognizability is not needed. So Y = σᵐ(Y_m) for some Y_m ∈ Ω_r.
  - Each tile t of Y lies in σᵐ(s) for a tile s of Y_m, and the 1-star τ of s in Y_m is legal.
  - The legal 1-star types are exactly 𝒯(r):
    - every legal 1-star of σ(Y′) lies inside σ of its parent's legal 1-star (the closure lemma, asserted on every type);
    - irreducibility makes every legal type reachable from every other. A legal patch occurs in σᵏ(t₀) for some tile t₀, the frame of t₀ is reached from any frame c in some j steps, so the patch occurs in σʲ⁺ᵏ(c), and following its ancestors gives a Φ-chain from the 1-star of c.
  - Types are taken up to a global frame, mirrors included, which leaves every link unchanged. So the two halves of a period-2 hull share their types.
  - The completeness check ensures that the R-ball of t lies inside σᵐ(τ) ⊂ Y. ∎

*Remarks.*
- **Why smooth cutoffs are needed.** Cover the tiling by the sharp patches star′(t) = t ∪ its panel-neighbours.
  - Each tile lies in 1 + n_t ≥ 8 of these patches, and each panel in at most N_max = 5 (its two tiles and at most three common neighbours; computed over the legal 1-star types).
  - Summing the free forms gives the rigorous radius-1 bound **E_\*(r) ≥ (8/5) μ₀′(r)**, with μ₀′ = min over legal 1-star types of λ_min of the free operator on star′.
  - This is a quantitative bound of the kind Part IV asks for, with a minimum over legal environments as its input. But it is weak: E_\*(FR30) ≥ 1.10 and E_\*(1387) ≥ 1.57, against floors near 8.8 and 9.3. It also gives 937 and 938 the same value.
  - Sharp (Neumann) cutoffs create surface states, the same reason F_k saturates. IMS replaces them with smooth cutoffs, and only then does the local minimum converge to E_\*.
- This is standard mathematics (IMS localization; the variational principle) applied to the whole rule family. Its content is the principle it gives: **the floor is the minimum, over the finitely many legal local environments, of their local ground energies, up to O(R⁻²)**.
- This is a support-type statement. Which environments are legal matters; how often they occur does not.
- It is the precise form of "local frustration determines the floor", and it is consistent with X.4 and X.5: frequencies and traces fail, while the set of legal environments with their full SU(2) data succeeds.
- Before this phase the ball enumeration used only the level-5 types. They are the full legal set for FR30 and for 1387, but not in general. Classes 1389 and 1391 gain 8 and 9 types under the closure. The code now uses the closure (`phase10_ims.phi_closed_types`, tested).

### Recalled: Theorem 9.1 (Phase IX)

Rules 937 and 938 have identical plaquette and two-cycle class counts, but their pinned level-3 and level-4 bottoms are rigorously separated, by ≥ 0.2776 and ≥ 0.2502. It is the finite-volume Chair44 counterpart of X.5.

---

## 5. Local frustration versus hierarchy (Part V)

**The question.** After conditioning on local geometry and gauge-invariant frustration data, do substitution-hierarchy descriptors add out-of-sample predictive power for spectral behaviour?

**The design** (registered in `phase10_preregistration.json` before the census existed; `audit/phase10_hierarchy.py`):

| | |
|---|---|
| unit | gauge classes, one row each. Every split is grouped by class by construction, so symmetric, gauge-equivalent or duplicated decorations cannot leak across folds |
| targets | Y₄ for all 1098 classes. Y₅ for the registered random sample of 200 classes (seed 20261024), not selected by outcome: the deeper level |
| M1, local | plaquette class fractions (f₋₁, f_traceless), two-cycle class fractions, U₀, U₁, μ₀, number of legal 1-star types |
| M2, loops | M1 + closed-walk moments m₂…m₈ + 2 × 2 Wilson-loop class fractions |
| M3, correlations | M1 + the V-B correlation statistics (C_t, C_p, pair, cv) |
| M4, hierarchy | M1 + M2 + M3 + depth enrichments, hierarchical variances, Φ self-loops, Φ's second eigenvalue, frequency of the U₁-minimising type |
| learners | OLS on standardized features; gradient-boosted trees (sklearn defaults, no tuning). 10-fold CV, seed 20261024 |
| decision | the hierarchy adds information **only if**, for both targets and both learners, the paired bootstrap 95 % interval (2000 class resamples) of RMSE(best of M1–M3) − RMSE(M4) lies entirely above 0 |

**Results** (`phase10_hierarchy.json`). RMSE is out-of-fold, over held-out gauge classes.

| target | learner | M1 local | M2 loops | M3 correlations | M4 + hierarchy | gain = best of M1–M3 − M4 (95 % CI) | R² of M4 | calibration slope of M4 |
|---|---|---|---|---|---|---|---|---|
| Y₄ (1098) | OLS | 0.1874 | **0.1441** | 0.1686 | 0.1328 | 0.0113 [0.0066, 0.0159] | 0.949 | 0.998 |
| Y₄ (1098) | boosting | 0.1952 | **0.1651** | 0.1779 | 0.1390 | 0.0261 [0.0205, 0.0314] | 0.944 | 1.005 |
| Y₅ (200, held-out sample) | OLS | 0.1375 | **0.1144** | 0.1368 | 0.1226 | −0.0081 [−0.0179, 0.0012] | 0.957 | 0.989 |
| Y₅ (200) | boosting | 0.1635 | **0.1533** | 0.1577 | 0.1408 | 0.0125 [0.0043, 0.0204] | 0.943 | 1.008 |

For scale: the standard deviation of both targets is about 0.59. The local model M1 alone reaches R² = 0.90 (Y₄) and 0.95 (Y₅) with OLS.

**The registered decision: no reproducible gain.** The criterion requires all four intervals to lie above 0; Y₅ with OLS fails, with the hierarchy model worse.

**A post-hoc control (not registered).**
- M4 contains the loop *and* correlation descriptors together. The registered comparator took them only separately, so part of M4's gain could come from their union.
- M123 = M1 + M2 + M3 against M4 gives the same pattern:
  - Y₄ OLS: 0.1395 against 0.1328, CI [0.0024, 0.0109];
  - Y₄ boosting: 0.1582 against 0.1390, [0.0147, 0.0241];
  - Y₅ OLS: 0.1186 against 0.1226, [−0.0099, 0.0022];
  - Y₅ boosting: 0.1521 against 0.1408, [0.0039, 0.0183].
- So the hierarchy descriptors add a small, learner- and target-dependent amount: 3–12 % of RMSE, and nothing for the linear model at the deeper level.

**Failure cases.**
- The largest M4 residuals include class 1387: boosting underpredicts its Y₄ by 0.51. Trees cannot extrapolate to the census maximum, the same failure Phase IX found for FR30.
- Also among them are classes 353, 0, 1818 and 1145.
- Every registered hierarchy descriptor fails the 937/938 falsification test (§3.1). None can explain that certified separation.

**What this does and does not show.**
- A null result means the registered hierarchy descriptors add no reproducible predictive information at this sample size, given these local descriptors and learners. It does not show that the hierarchy is irrelevant to E_\*.
- The hierarchy fixes which local patterns are legal (Phase VIII §6(c)). Legality is already inside the local descriptors, through the legal 1-star set.
- Phase VIII §6(c) proved that a control with "the same legal local patches but different long-range order" does not exist at radius ≥ 1. So the remaining question can only be predictive, never interventional.
- No feature importance is read causally.

---

## 6. The abstraction (Part VI)

**The object: the local frustration profile of a rule.** For a decoration r it consists of four nested sequences of numbers:
- the free supertile bottoms F_k(r) and the pinned bottoms Y_L(r) (Theorem X.2);
- the localization pair (Λ_R(r), D_R(r)), the minima over legal radius-R balls of the amplified and plain local bottoms (Theorem X.7, for every decoration with an irreducible frame substitution);
- the radius-1 environment minima U₀(r), U₁(r), U₂(r), … over the legal 1-star types and their inflations.

It is a compression: a handful of numbers per scale, not the operator.

| property | free/pinned (F_k, Y_L) | localization (Λ_R, D_R) | environments U_m |
|---|---|---|---|
| exactly gauge-invariant | yes: λ_min of gauge-covariant finite operators | yes | yes |
| invariant under the geometric symmetries | yes (constant on S₃-orbits and gauge classes; verified on the census) | yes | yes |
| controls E_\* with a proof | yes, two-sided: F_k ≤ E_\* ≤ Y_L | yes: Λ_R ≤ E_\* ≤ D_R and D_R − Λ_R ≤ ε(R) = O(R⁻², uniformly in the rule (Theorem X.7) | one-sided: U_m ≥ E_\*, with U_m ↓ E_\* along self-loops |
| converges to E_\* | upper side yes; **lower side no** (surface states: F_k saturates, F₄(FR30) = 5.21 against E_\* ≥ 7.954) | yes, at an explicit rate | yes (upper side) |
| sufficient for the finite-level spectrum | no | no | no. Closed-walk trace data (the moments) suffices, but compresses nothing. Plaquette-level data does not (X.5) |
| closed under substitution | the T_k data are, exactly, through the Schur recursion (Phase VIII; growing dimension) | the set of legal R-balls maps into the legal 2R-balls under σ | U_m(τ) = F_τ(R_m) (Phase VIII Thm 8.2) |
| tractable | k, L ≤ 4 for all 1098 classes; L = 5, 6 for candidates | R = 8 for the leading classes; R = 14–15 for single rules (prescribed-μ certificates on the GPU) | m ≤ 1 for all classes; m ≤ 3 for candidates |
| predictive on held-out classes | Y₃ ranks Y₄ with ρ = 0.89 and recalls all of the top 20 within its top 100; the free bottoms F_k only ρ ≈ 0.80–0.84 | not needed: it has a proved error bound | **U₁: ρ = 0.90 against Y₄, and 0.955 against the held-out Y₅ sample**, the best cheap predictor (§3.1) |

**The equivalence relation it induces.** Call r ~_R r′ when their sets of gauge classes of legal radius-R balls coincide. Then |E_\*(r) − E_\*(r′)| ≤ 2ε(R) by Thm 7.1, and E_\* is constant on the limit relation (all R). This is "local spectral equivalence". It is defined by support, not by frequencies. The 937/938 pair is *not* equivalent at R = 1: their radius-1 environments have different bottoms (U₁ = 8.596 against 8.367, §3.1).

**What the abstraction does and does not do.**
- It turns "why does FR30 have a high floor" into "which legal local environments does the rule admit, and how frustrated is the worst one". The floor is the minimum over legal environments, up to an explicit localization error.
- It does **not** supply a formula for E_\* in terms of curvature data. Every curvature-frequency summary fails: X.4, X.5, 9.1.
- The finite truncations predict to the accuracy quantified in §3.1 and §5, but only the localization pair has a proved error bound.
- That bound is O(R⁻²), with a constant of about 80/ρ² for FR30 and 1387. At R = 14 it separates 1387 from FR30, whose floors differ by about 0.6. It cannot separate 1387 from 1389 or 1391, whose floors differ by 0.1–0.2 (§12).
- **Rare environments.** The support-type principle has a practical sting. Class 1144's weakest legal environment is a rare 1-star type absent from T₅. Its environment minimum certifies E_\*(1144) ≤ 8.1414, far below its supertile values Y₄ = 9.10 and Y₅ = 8.78. The supertile sequence converges slowly exactly when the worst environment is rare.

---

## 7. A second geometry: Pauli-frame connections on ℤ³ (Part VII)

**The controlled change.** Only the geometry changes. The following stay fixed:
- the frame alphabet (signed permutation matrices, proper unless stated);
- the link formula U(q → q + e_j) = (σ·M_qᵀe_j)(σ·M_{q+e_j}ᵀe_j) ∈ Q₈;
- the degree-normalized operator H = 6 − A_U = D_U†D_U.

The tiles are the unit cubes of ℤ³, adjacent across faces. Frame fields are periodic with period p, and E_\* = min_θ λ_min H(θ) over Bloch momenta (`audit/phase10_z3.py`).

What differs from Chair44:
- the graph is the cubic lattice: 6 neighbours, bipartite, no two-cycles;
- there is no substitution hierarchy and no matching rule;
- the period is chosen freely.

Both graphs are amenable.

**What transfers, with proof.**
- Theorems X.1 (flatness) and X.2 (bracketing) are graph-general.
- X.2's lower bound on ℤ³ is the cell partition: E_\* ≥ λ_min H_free(cell) for any periodic connection. It is used for the certificates below.
- X.3 transfers in this form: a periodic connection on ℤ³ has E_\* > 0 iff it is not flat.
  - ⇐: a non-trivial plaquette in every period cell makes the free 2p-cell non-flat, so its bottom is positive by X.1(iv), and X.2 applies.
  - ⇒: a flat connection on ℤ³ is gauge-trivial, since the plaquettes generate the cycle space. Then E_\* = 0.
- Both directions use only bounded degree, a partition into uniformly bounded blocks, and, for ⇒, an exhausting family of blocks with vanishing boundary-to-volume ratio.

**What was constructed on ℤ³.**
- Theorem X.4, the no-go: flat islands give E_\* ≤ 6(1 − cos(π/(R + 1))) at a non-trivial-plaquette fraction ≥ 0.78. Measured R = 2, 3, 4, 6, 8 give fraction 0.854 → 0.784 and E_\* ≤ 3.000 → 0.362.
- Theorem X.5, insufficiency in infinite volume:
  - **Trace fields.** Among 40 000 random period-2 fields (seed 7), 497 distinct plaquette trace fields occur, and 492 are shared by at least two fields. 70 of those are shared by fields with numerically different floors.
  - **Full Q₈ class fields** (the traceless axis included). 3817 distinct fields occur, 3672 are shared, and **1943 are shared by fields with numerically different floors**.
  - **The certified pair** (`phase10_z3_classpairs.json`): identical class on every plaquette, class counts (+1, −1, traceless) = (8, 0, 16) per cell, gauge-equivalent Abelian shadows with floors (1.528, 1.528, 0). Yet E_\*(A) ≤ 177943087298/440306385467 = 0.404135 < 0.585786 ≤ E_\*(B).
  - A pair matched only in its trace field (`phase10_z3_pairs.json`) has the same certified numbers. Its class fields differ on 16 of 24 plaquettes.

**Abelian shadows.**
- In the class-field-matched pair the shadows are gauge-equivalent (X.5), so no shadow distinguishes A from B.
- For the trace-matched pair's low connection A′ (`phase10_z3_pairs.json`), two shadows are certified above the non-Abelian floor: E_\*(χ_k∘U_A′) ≥ 0.76393 > 0.40414 ≥ E_\*(U_A′).
- On Chair44 the opposite holds, certified:
  - E_\*(FR30) ≥ 7.954 > 7.6346 ≥ E_\*(χ₁∘U_FR30) (Phase VII);
  - E_\*(1387) ≥ 8.7645 > 7.7717 ≥ max_k E_\*(χ_k∘U_1387) (`phase10_shadows.json`).
- **"Non-Abelian holonomy raises the floor above its Abelian shadows" is therefore connection-dependent, not a principle.**

**Which ingredients are essential.**

| ingredient | evidence | verdict |
|---|---|---|
| non-Abelian holonomy | X.5: the certified pair differs only in non-Abelian orientation data. X.6: in 2D the Pauli-frame construction is Abelian (ℤ₄), so the 3D geometry is what makes it non-Abelian | necessary for the X.5 phenomenon; neither raises nor lowers the floor by itself |
| local geometric frustration (density) | X.4 on ℤ³; 937/938 on Chair44 | **not sufficient**: frequencies do not bound the floor |
| local frustration (support: the worst legal environment) | localization (Phase VII Thm 7.1, Theorem X.7) holds on any bounded-geometry graph; X.4's islands are exactly a low-energy legal environment | **the controlling quantity** on both geometries [P, for Chair44 hulls and periodic ℤ³] |
| connectivity and expansion | both graphs are amenable. On a non-amenable graph (e.g. a regular tree) inf σ(d − A) > 0 already for the trivial connection (Kesten), so X.3's "⇒" fails there | amenability is used in X.3, and only there |
| substitution structure | X.4 and X.5 hold on periodic ℤ³ without any hierarchy | not needed for the theorems |
| Chair44 matching rules | not used on ℤ³ | not needed |

**Not done on ℤ³.** A predictive statistics sample analogous to Part V (random period-3 fields with floors, class counts and shadow floors) was started and stopped for CPU. It is not reported, and nothing in this section depends on it.

---

## 8. Novelty and interpretation (Part VIII)

**Categories** (the brief's):
1. established mathematics;
2. new computation or application;
3. potential mathematical novelty;
4. physical conjecture.

Phase IX's categories map onto these as A → 1, B → 2, C → 3, D → 4.

**The 2026 Chair44 preprints, read in full.** All are unrefereed, with no journal reference; checked 2026-10-23.

| preprint | object | local rule | spectral content | overlap with this project |
|---|---|---|---|---|
| Tsiokos, arXiv:2609.19214v1 (16 Sep 2026) | the 7-cube chair with 192 pyramid bumps and dents. "Chair44": the geometry admits 44 of 2 388 contacts. Child poses are written as signed-permutation frames | geometric; unique parent from the first shell (Thm 6.4, Lean-formalized) | diffraction only (pure point) | the geometry and its name. No operators or connections |
| Flicker, arXiv:2609.23783v2 (29 Sep 2026) | the chair with face arrows or colours | face contacts. 33 one-shell clusters, 15 survive a second shell | no. Proposes a classical 24-state lattice model | radius-1 forcing of the hierarchy, with a different decoration |
| Goodman-Strauss, arXiv:2609.24779v1 (21 Sep 2026) | the chair with three-colour face markings | face contacts, prose proof | no | radius-1 forcing |
| **Kamenetsky, arXiv:2610.00916v1 (1 Oct 2026)** | the chair with each tile marked by its frame g ∈ B₃. The 3⁷ = 2187 child-frame assignments with the centre child fixed to the identity | 135 pairwise facet-contact triples (radius 1). **Thm A**: every lattice-registered tiling obeying them is uniquely hierarchical and strongly aperiodic. Computer-certified (`cert6.py`), not formally verified. **Thm B**: only 3 of the 2187 assignments pass the coarsening-closure test | no | see below |

**Overlap with Kamenetsky.**
- **FR30 is exactly his certified assignment "frames30"** (his Fig. 2(c), entry for entry, with the same conventions).
- His three passing assignments are FR30's gauge class {1386, 3690, 4752}.
- The 4374 decorations with a non-identity centre child are outside his study, which lists them as future work. They include **the top class 1387 of this phase**, which differs from FR30 only in the centre child's frame.
- None of the four preprints studies an operator, a spectrum or a connection Laplacian.

**Corrections to earlier claims.**
- Phase VII Theorem 6.2 (the FR30 frame decoration is a radius-1 matching rule) is an *independent re-derivation* of Kamenetsky's Thm A, with a different local rule: legal 1-stars rather than pairwise contacts. **It is not new.**
- Phase IX's novelty table listed it as "C, provisional". That entry is corrected here to **2: an independent computational verification of a preprint result.**
- The name "FR30" coincides with Kamenetsky's "frames30".

**Each result of this phase against the closest prior work:**

| result | closest prior work | category |
|---|---|---|
| X.1 flatness ⟺ gauge-trivial ⟺ zero mode (SU(2)) | Lange–Liu–Peyerimhoff–Post, Calc. Var. PDE 2015, Prop. 3.2 (any group); Bonnefont–Golénia–Keller–Liu–Münch, AHP 2020, Prop. 2.1 (U(1)) | 1 |
| X.2 bracketing F_k ≤ E_\* ≤ Y_L on substitution hulls | Dirichlet–Neumann bracketing: Kirsch, arXiv:0709.3707, §5.2; Fabila-Carrasco–Lledó–Post, LAA 2018 (U(1) magnetic graphs); Reed–Simon IV §XIII.15. The substitution-hull SU(2) form was not found | 1 (method), 2 (application) |
| X.3 positivity ⟺ a non-flat finite supertile; census-wide E_\* ≥ 3.788 | continuum analogue: Kondratiev–Maz'ya–Shubin, CPDE 2009, Thm 1.5 (strict positivity ⟺ a uniform condition on cubes of one size). Discrete special case: Nakamura, AHP 2000 (plaquette bound for random flux). No discrete "iff" for hulls was found | 1/2 |
| X.4 no frequency-type lower bound | the Lifshitz rare-region mechanism (Nakamura 2000, random flux) | 1 (mechanism), 2 (explicit Pauli-frame family) |
| X.5 equal plaquette holonomy classes (hence equal traces and gauge-equivalent Abelian shadows), certified different infinite-volume floors | that Wilson loops beyond plaquette traces are needed is classical (Giles, PRD 1981). The full determinant of a finite SL₂ connection Laplacian is a sum over cycle-rooted spanning forests weighted by Π(2 − tr w_γ) over *all* cycles (Kenyon, Ann. Probab. 2011, Thm 9; Forman 1993 for line bundles). This is why plaquette data cannot suffice. **No explicit lattice pair with equal plaquette data and certified different λ_min was found** | 2 (explicit certified example); 3 only in the weak sense of an explicit obstruction |
| X.6 Pauli frames are Abelian in 2D | elementary | 1 |
| X.7 localization for every rule (the floor is the worst legal environment) | IMS localization (Cycon–Froese–Kirsch–Simon 1987, Ch. 3); Phase VII Thm 7.1 for FR30. Quantitative frustration bounds of Cheeger type: Bandeira–Singer–Spielman, SIMAX 2013, Thm 5, λ₁ ≥ λ₂(𝓛₀) η_G/44; LLPP 2015 for U(1). These need a graph spectral gap, which vanishes on large amenable blocks | 1 (machinery), 2 (application to the rule family) |
| maximizing λ_min over connections | Marcus–Spielman–Srivastava 2015 (Ramanujan signings), Hall–Puder–Sawin 2018, Huang 2019 (hypercube signing with A² = nI). Lieb and Lieb–Loss concern energies and determinants, not λ_min | context |
| **the extremal search: FR30 is not optimal; class 1387** | none: no spectral study of the Chair44 rules exists. Kamenetsky's assignment space excludes 1387 | 2. The certified comparison E_\*(1387) > E_\*(FR30), the census-wide certified positivity and the mirror-twin leader of Stage C are new computations. Whether 1387 or its twin is the extremizer is open (§12) |

**No result of this phase reaches category 3 with confidence.**
- The closest candidates are the certified ℤ³ class-field-matched pair (X.5), the census-wide positivity, and the certified comparison of class 1387 with FR30.
- All three are explicit computations, without a new general theorem.
- The general statements (X.1–X.3, X.7) are standard mathematics applied to a new class of examples.

**Physical interpretation: none is claimed (category 4 is empty).** A positive spectral floor of a covariant Laplacian is a statement about a discrete operator. It implies nothing about quantum mechanics, the Standard Model or mass spectra without additional dynamics and a continuum limit, and none was studied.

---

## 9. Failed conjectures and negative results

| # | conjecture or assumption | verdict | evidence |
|---|---|---|---|
| 1 | FR30 is spectrally optimal among the Chair44 frame rules | **[F]**, at finite volume and, certified, in infinite volume: E_\*(1387) ≥ 8.7644994 > 8.7642270 ≥ E_\*(FR30) | Class 1387 = {1387, 1388, 3691, 3692, 4753, 4754}, which contains FR30 with only its centre frame changed, is above FR30 at L = 3, 4, 5, 6. The L4 comparison is certified at finite volume: [9.51686, 9.51687] against [8.91963, 8.91963]. 1389 and 1391 are also above FR30 at every computed level |
| 2 | the fraction of non-trivial plaquettes (or any frequency of curvature classes) lower-bounds the floor | **[F]**, Theorem X.4 | flat islands: fraction ≥ 0.78 with E_\* ≤ 6(1 − cos(π/(R + 1))) → 0 |
| 3 | the plaquette holonomy data determine the floor: traces, conjugacy classes per plaquette, or the Abelian shadows they fix | **[F]**, Theorem X.5, infinite volume, certified | identical Q₈ class on every plaquette, gauge-equivalent Abelian shadows, floors ≤ 0.4041 and ≥ 0.5858 |
| 4 | a non-Abelian connection's floor is at least that of each of its Abelian shadows (as FR30 > χ₁) | **[F]**, certified | on ℤ³, E_\*(χ_k∘U_A) ≥ 0.7639 > 0.4041 ≥ E_\*(U_A) for two shadows (the trace-matched pair of §7). The direction depends on the connection |
| 5 | class counts determine the bottom (Phase IX) | **[F]** at finite volume | Theorem 9.1. In infinite volume on ℤ³, X.5 is stronger |
| 6 | the free-supertile bound converges to the floor | **[F]** | F_k saturates near 5.2 (FR30) and 5.7 (class 1387), far below the floors (≥ 7.954), because of free surface states. The radius-1 covering bound fails the same way (E_\* ≥ 1.10 for FR30) |
| 7 | the level-5 supertile exhibits every legal radius-1 environment | **[F]** (methodological) | in 1086 of 1098 classes the Φ-closure adds rare legal 1-star types missing from T₅. In 316 classes the radius-1 minimum U₁ is attained on a closure-only type, up to 0.33 below the T₅ value |
| 8 | Y₂ is a usable screen for strong rules | **[F]** | in the census, Y₂'s top 1.8 % recalls only 5 % of the top-20 classes by Y₄. Keeping all of them needs its top ≈ 45 % |
| 9 | Phase VII's radius-1 matching rule for FR30 is a new result | **[F]** (novelty) | it is Kamenetsky's Thm A for "frames30" (arXiv:2610.00916) |
| 10 | the substitution hierarchy carries predictive information beyond local data | **not established**: positive in 3 of 4 registered comparisons, so the all-four criterion fails. The post-hoc union control shows the same pattern | Part V (§5) |
| 11 | periodic arrangements of a rule's own supertile reproduce its floor | **[F]** (evidence; the Bloch minima are numerical) | FR30: 8.335, 7.510, 8.246 (k = 1, 2, 3), all below the estimated hull floor ≈ 8.764; k = 2 is below even the certified hull lower bound 7.954. Class 1387: 8.901, 8.276, 9.020, all below its Y-based estimate ≈ 9.36; k = 2 is below even its certified lower bound 8.7645. The non-hierarchical seams create lower-energy states [E] |
| 12 | self-similar (selection-chain) patches give better bounds than generic balls (Phase IX) | **[F]** | equal at equal patch size |
| 13 | the level-4 leaders are the deep leaders | **[F]** | classes 901 and 1144 are above FR30 at L4 (9.0825, 9.1036 against 8.9196) and below it at L5 (8.7946, 8.7768 against 8.7970) |
| 14 | properness (det = +1) is what makes every rule's floor positive | **[F]** | in the extended space all 6⁸ = 1 679 616 decorations have a non-flat level-1 supertile (min F₁ = 1.6716 for proper and improper alike). Positivity comes from the chair geometry and the Pauli construction, not from properness |
| 15 | fewer legal environments imply a higher floor | **[F] as a law**; supported only as an enrichment | the four classes that stay on top through level 5 all have ≤ 104 legal 1-star types (census median 1101), but census-wide the rank correlation with Y₄ is only −0.13 |

---

## 10. Decision table

| claim | status | where |
|---|---|---|
| X.1: SU(2) flatness ⟺ gauge-trivial ⟺ λ_min(H_U) = 0 on a finite connected graph | **proven** (standard) | §4 |
| X.2: F_k(r) ≤ E_\*(r) ≤ Y_L(r) for every decoration | **proven** | §4 |
| X.3: E_\*(r) > 0 ⟺ some T_k(r) is non-flat | **proven** | §4 |
| every proper Chair44 rule has a primitive frame substitution (minimal hull) | **computationally certified** (exact integer matrix powers, all 1098 classes) | §4 |
| every proper Chair44 rule has E_\* ≥ 3.788 | **computationally certified** (Higham-bounded Cholesky, all 1098 classes) | §3.1 |
| 806 of 1098 classes are rigorously below FR30 | **computationally certified** (exact Rayleigh Y₄ < 7.954292) | §3.1 |
| X.4: no lower bound on E_\* from plaquette class frequencies | **proven** (explicit family) | §4, §7 |
| X.5: the plaquette holonomy class field (hence traces, class counts and every Abelian shadow) does not determine E_\* (infinite volume) | **proven + computationally certified** | §4, §7 |
| X.6: Pauli-frame connections are Abelian in 2D | **proven** | §4 |
| X.7: localization (Λ_R ≤ E_\* ≤ D_R, O(R⁻²)) for every rule with an irreducible frame substitution | **proven** (Phase VII Thm 7.1 generalized; completeness through the Φ-closure) | §4 |
| 937/938: class counts do not determine finite-level bottoms | **computationally certified** (Phase IX; re-verified) | §1 |
| FR30 is spectrally optimal among Chair44 frame rules (finite levels) | **falsified** | §3 |
| E_\*(1387) > E_\*(FR30) in infinite volume | **computationally certified** (Theorem X.7 at R = 14, 7527 balls; Phase VIII exact upper bound) | §3.2 |
| 1387 is the maximizer of E_\* over the 1098 classes | **open**: certified against 1094 of the other 1097 | §3.2, §12 |
| U₁ (the radius-1 environment minimum) predicts held-out floors | **empirically supported** (ρ = 0.955 on the registered random sample) | §3.1 |
| the mirror twin 539311 exceeds 1387 at finite levels | **certified at level 4** (enclosures); numerical at levels 3 and 5 | §3.3 |
| the twin exceeds 1387 in infinite volume | **open** | §3.3 |
| E_\*(1144) ≤ 8.1414 although Y₅(1144) = 8.7768 | **computationally certified** (exact Rayleigh quotient on a legal 8-ball) | §3.2 |
| hierarchy descriptors add out-of-sample predictive power | **not established** (3 of 4 registered comparisons; the criterion fails) | §5 |
| "non-Abelian holonomy raises the floor above its Abelian shadows" | **falsified** as a principle (certified counterexample on ℤ³). True and certified for FR30 (margin ≥ 0.32, Phase VII) and for 1387 (margin ≥ 0.99) | §7 |
| the free-supertile bound converges to E_\* | **falsified** (F_k saturates) | §9 |
| T₅ exhibits every legal 1-star type | **falsified** (1086 of 1098 classes) | §3.1 |
| the high-Y region of the census surrounds FR30 | **empirically supported** (13 of the top 22 within digit distance 2, against 6.1 %) | §3.1 |
| extrapolated floors (last-ratio tails) | **conjectural** | §3.2 |
| Phase VII Thm 6.2 is new | **falsified** (Kamenetsky, arXiv:2610.00916) | §8 |
| a physical law, quantum mechanics or a mass spectrum follows | **not claimed** | §8 |

---

## 11. Corrected abstract

> **Spectral floors of Pauli-frame connections on the three-dimensional chair tiling.**
>
> **The family.**
> - Each assignment of signed-permutation frames to the eight children of the 3D chair substitution ("Chair44") defines a self-similar tiling hull.
> - It also defines an SU(2) connection with values in the quaternion group Q₈, built from the frames by a Pauli formula.
> - We study the infimum E_\* of the spectrum of the covariant Laplacian 24 − A_U on the hull. This is a discrete operator; no physical interpretation is implied.
> - The 6561 orientation-preserving rules fall into 1098 gauge classes.
>
> **Exact results.**
> - (i) Every rule has a primitive frame substitution.
> - (ii) E_\* > 0 if and only if some finite supertile carries a non-flat connection. Every rule satisfies this, and computer-assisted bounds give E_\* ≥ 3.788 for all of them.
> - (iii) For every rule, E_\* equals the minimum over the finitely many legal local environments of radius R of their local ground energies, up to an explicit O(R⁻²) error: an application of IMS localization with geometric constants.
>
> **Discovery.**
> - The rule FR30, an independently known radius-1 matching rule (Kamenetsky 2026), is not extremal.
> - Rule class 1387, which differs from FR30 only in the frame of the central child, exceeds it at every computed finite level. A computer-assisted proof shows that its infinite-volume floor is strictly larger: E_\* ≥ 8.7644994, against FR30's E_\* ≤ 8.7642270.
> - The three classes above FR30 at every computed level are 1387, 1389 and 1391, all within one or two frame changes of FR30. They are among the six rules with the fewest legal local environments.
>
> **Limits of curvature summaries.**
> - On the cubic lattice we construct two periodic connections with the same Q₈ holonomy class on every plaquette, and hence gauge-equivalent Abelian shadows, whose infinite-volume floors are rigorously separated (≤ 0.4042 versus ≥ 0.5857).
> - We also give connections whose fraction of non-trivial plaquettes stays above 0.78 while the floor tends to zero.
> - So no function of plaquette-level curvature data bounds or determines E_\*. The floor is controlled by which local environments are legal, not by how frequent the curvature is.
>
> **Hierarchy.** A pre-registered held-out test does not establish that substitution-hierarchy descriptors improve the prediction of finite-level floors beyond local data.
>
> **Status.** The general statements are standard results (flatness, Dirichlet–Neumann bracketing, IMS localization) applied to a new family. The new content is the certified extremal comparison and the explicit obstructions.

---

## 12. The single most promising next experiment

**Make the geometric tail rigorous: certify a contraction bound for the interface recursion, then use it to decide the extremal rule.**

**Status after this phase.**
- Class 1387 is certified above FR30 and above 1094 of the other 1097 proper classes.
- Open: 1387 against 1389 and 1391, and against its own mirror twin outside the census.

**Why localization cannot finish the job.**
- After this phase, only classes 1389 and 1391 remain unresolved against 1387. All three sit within one or two child-frame changes of FR30.
- At every computed level their order is 1387 > 1389 > 1391, with gaps of 0.10–0.17 (L4: 9.517, 9.346, 9.174; L5: 9.393, 9.219, 9.122).
- The certified upper sides are already sharp: exact Rayleigh quotients near the floors.
- The certified lower side converges like 80/ρ² for both FR30 and 1387. That is intrinsic to localization: a cutoff of width ρ costs kinetic energy of order ρ⁻². Separating floors 0.1–0.2 apart would need ρ ≈ 20–30, which means 10⁴-tile balls and about 10⁵ of them. Even the GPU path cannot reach that.

**The missing theorem.**
- Along a Φ-self-loop chain, the legal-patch bounds U_m(τ) decrease to E_\* (Phase VIII Thm 8.3), with observed decrement ratios 0.15–0.27.
- A proved bound U_{m+1} − E_\* ≤ r (U_m − E_\*) with explicit r < 1 would give the rigorous lower bound E_\* ≥ U_m − (U_{m−1} − U_m) r/(1 − r). It converges geometrically instead of as O(R⁻²).
- Phase IX recorded the FR30 enclosure [8.76385, 8.76423] *conditional* on exactly such a ratio bound (r ≤ 0.1541).
- The recursion is an exact Schur-complement map on the labelled surface response, Loewner monotone and concave (Phase VIII Prop 8.1).

**The experiment.**
- Look for a metric in which this map contracts for energies just below E_\*, and certify the contraction constant on the finitely many legal 1-star types. Candidates are the Thompson or Hilbert projective metric on positive operators, where monotone concave maps are known to be non-expansive.
- Validate on FR30, where the conditional enclosure predicts the answer.
- Then decide 1387 against 1389 and 1391.

**Decisive in either direction.**
- If it succeeds, class 1387 is either certified as the maximizer of the spectral floor over all 6561 proper frame rules (a certified extremizer, category 3), or overtaken.
- If no contraction holds, the decrement ratios are not uniformly bounded. That would mean the conditional enclosures of Phases VIII–IX cannot be made rigorous by this route.

---

## Reproduction

All commands run from the repository root with Python 3.12, numpy, scipy, mpmath and scikit-learn 1.9.1. Single-threaded BLAS is recommended for the pooled jobs (`OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1`). Wall times are on a 24-thread desktop under load.

| step | command | output | wall time |
|---|---|---|---|
| census (stage A) | `python -u -I audit/phase10_census.py 8` | `phase10_census.jsonl` / `.json` | about 1.5 h with 8 processes for the closure pass (the level 1–4 eigenvalues can be reused from an earlier pass with PHASE10_REUSE) |
| certified brackets, all classes | `python -u -I audit/phase10_certify.py 12` | `phase10_certify.jsonl` | tens of minutes |
| stage B selection (registered rule) | `python -u -I audit/phase10_stageB.py select` | `phase10_stageB_selection.json` | seconds |
| Y₅ and exact Y₅ upper bounds | `python -u -I audit/phase10_stageB.py y5 10` | `phase10_y5.jsonl` | about 1 h with 10 processes |
| deep stage | `python -u -I audit/phase10_stageB.py deep_targets`, then `deep_one <class>` per class | `phase10_deep.jsonl` | 40–90 min per class, one process each (dominated by the level-6 eigensolve) |
| promotion checks | `python -u -I audit/phase10_stageB.py promote` | `phase10_stageB_promotion.json` | seconds |
| localization bounds | `python -u -I audit/phase10_ims.py <decoration> <R> <m> <nproc> [mu]` | `phase10_ims.jsonl` | R = 8: ≈ 4 min |
| localization certificates on the GPU | `set IMS_GPU=1` and `C:/Users/super/.venvs/qisgpu/Scripts/python -u -I audit/phase10_ims.py 1387 14 4 6 8.7645`; likewise `1387 15 4 5 8.80` and `x539311 14 4 5 8.7645` (`x<j>` is an extended-space index). Needs a CUDA build of torch with Blackwell (sm_120) kernels: the venv's torch 2.11+cu128 has them, the system torch 2.6+cu124 does not | `phase10_ims.jsonl` | 29 min for 1387 at R = 14 (13 min CPU enumeration, 16 min GPU) |
| Abelian shadows | `python -u -I audit/phase10_shadows.py 5 4752 1387` | `phase10_shadows.json` | ≈ 7 min |
| periodic approximants | `python -u -I audit/phase10_periodic.py <decoration> 1 2 3` | `phase10_periodic.jsonl` | minutes |
| stage C (improper frames) | `phase10_improper.py f1 8`, `y2 8`, `y3 8`, `y45 8`, `pack 6`; then `certify <j>` for the leaders | `phase10_improper_*.json`, `phase10_improper_y2_reps.npz`. The full 6⁸ arrays `phase10_improper_{y2,f1}.npy` (13 MB each) are regenerated by `y2` and `f1` and are not committed | f1 1 min, y2 16 min, y3 7 min, y45 26 min with 8 processes; certify about 1–2 h per candidate |
| Part V | `python -u -I audit/phase10_hierarchy.py` | `phase10_hierarchy.json` | minutes |
| ℤ³ laboratory | `python -u -I audit/phase10_z3.py noflat pairs certpair classpairs certclasspair` | `phase10_z3_*.json` | ≈ 3 h, mostly `classpairs` (single core) |
| dataset, leaderboard, descriptors, criteria | `python -u -I audit/phase10_analysis.py` | `phase10_dataset.*`, `phase10_leaderboard.*`, `phase10_descriptors.json`, `phase10_criteria.json` | ≈ 2 min |
| ledger | `python -u -I audit/phase10_ledger.py` | `phase10_ledger.json` | seconds |
| tests | `python -m pytest -q tests/test_phase10.py` | — | about 40 s |
