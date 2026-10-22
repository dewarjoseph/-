# Phase V-B — The FR30 Excess: Mechanism, Scaling, and Falsification

Branch `claude/phase5b-excess-mechanism` (from `main` at aa05095, which contains all Phase V-A work). Final commit: 2aede8a (report; this hash-recording commit follows it). Status vocabulary: **[K]** kernel-checked in Lean; **[P]** proved outside Lean (hypotheses stated); **[X]** exact computational certificate (integer or rational arithmetic); **[E]** numerical evidence with residuals reported; **[C]** conjecture; **[U]** unresolved.

## 0. Executive summary

All computations were stopped at 18:01 UTC on the user's instruction ("usage is too much"); every result below is from runs that completed before that, and the incomplete runs are described as incomplete. Repository state: 25 commits on this branch, 91 files added, no pre-existing file modified.

1. **The Phase V-A baseline reproduces completely** with independently written code (class counts, bottoms, census checks, controls, participation statistics, exact certificates, Lean axiom list); five documentation-level discrepancies, no numerical one (§1).
2. **The rigorous bracket is now $4.008189\le E_{\rm bulk}\le8.7701336$, both ends exact** (radius-2 collared census of 165 types with a proved closure theorem and certified 3-block inequalities; exact Rayleigh quotient of the level-6 ground vector) (§5).
3. **FR30 is not exceptional among substitution decorations.** The decoration space is finite (6561). In a uniform random 36 % of it (2371 decorations, level-3 census) 23 decorations have a higher pinned bottom than FR30, and in the preregistered level-4 sample one decoration (index 4757, which differs from FR30 only in the centre frame and one octant frame) lies 0.25 above FR30. FR30 sits at the 99th percentile of the flux-corrected residual (+2.5 sd), not at the top (§2).
4. **Flux fractions explain 80 % of the variance of the edge across decorations** (cross-validated); the 30 structural predictors tested add at most 5 percentage points (forward selection, cross-validated) and **do not explain the FR30 residual** (+0.61 → +0.54 at level 3; +0.75 → +0.43 at level 4, still +2.3 to +2.6 sd). Two of the three preregistered primary predictors (traceless depletion from top-level interfaces, uniformity of $-1$ frustration) are statistically significant but with negligible effect size (ΔR² ≈ 0.001); the leading exploratory predictor is a near-duplicate of $f_{-1}$ (VIF 27). The mechanism question is therefore answered negatively for every local statistic tried (§2).
5. **The causal interventions locate the excess in the self-similar arrangement of the frames, not in flux, not in the local blocks, and not in the coarse hierarchy alone.** After flux correction, keeping only FR30's finest-scale blocks under a random coarse arrangement leaves **no** excess at level 4 (residual −0.16 to −0.26); keeping only the coarse FR30 hierarchy leaves none (−0.12 to −0.20); shuffling FR30's own rotations among positions leaves none (−0.19 to −0.60); 5 % local defects remove three quarters of it (+0.14 to +0.20 versus +0.75) (§3).
6. **Eigenstate scaling:** $D_2=1.88$ and $1.90$ in the 4→5 and 5→6 windows but 2.49 in 3→4; a clean localized→extended crossover is contradicted at accessible sizes, the "ordinary state on the interface network" picture holds only in its weak form, and the pinned wall sets the child-weight hierarchy anew at each level. Asymptotics remain undecided: the level-7 run was stopped at pass 1 (§4).
7. **Physical prediction:** a two-orbital tight-binding patch with Q₈ Peierls phases; the FR30 lowest pinned mode lies 0.31 hopping units above a flux-matched substitution control at level 4, robust to link errors ≤ 0.1 rad and on-site disorder ≤ 4 %; the free (unpinned) patch cannot be used because its lowest mode is a surface state (§6).

**Decision standard.** The phase did not find a reproducible structural predictor of the FR30 residual; it did rule out, with controls and cross-validation, every local-statistic mechanism tested, and it re-identified the phenomenon: the excess belongs to a top-percentile family of fully self-similar admissible rules, several of which exceed FR30, and it is destroyed by any randomization of the arrangement at any scale.

## 1. Baseline reproduction (Workstream A)

Every Phase V-A number in the six requested groups reproduces, most of them with code written independently in this phase (`audit/phase5b_a_validation.py`; table with methods in `audit/results/phase5b_a_baseline_reproduction.md`). Independent implementations: a per-tile Pauli-matrix plaquette enumerator (levels 1–5), own sparse assembly and own solver calls for the pinned bottoms (levels 2–5), own Λ₇ crystal / Bloch / real-space-torus code for the periodic census checks, own exact LDL with `fractions.Fraction` for the lower-bound certificate, own data-free Lean extract compiled with the kernel. Repeated runs of the same implementation are marked as such in the table.

| group | result |
|---|---|
| (1) class counts and flux fractions, levels 1–5 | identical to the dossier (independent enumerator) |
| (2) pinned bottoms 10.776951, 9.378470, 8.919634, 8.797011 | identical to 9 digits; residuals 2e-14 … 1.9e-8; Kramers splits ≤ 1.3e-13 |
| (3) census real-space checks (10.644234146; 9.633732) | own Bloch and own torus Hamiltonians agree to 3e-10 |
| (4) substitution controls and residuals (+1.141, +2.234) | identical; regression constants verbatim from the stored census file |
| (5) IPR·n, interface enrichment, D₂ | identical (own eigenvectors and stored weight files; D₂ = 2.49, 1.88, 1.90) |
| (6) 3137451/2000000 and 12805833/4000000; Lean axioms | own exact certificates reproduce the first; the second re-run only; axiom list reproduced by a data-free kernel compile |

Discrepancies found (none numerical): the framework document's statement that all entries of H lie in {0, ±1, ±i, 24} is false when two tiles share several panels (blocks −2C occur from level 2); the level-5 certified upper bound is "one certified upper bound" (a re-run gives a different, tighter rational 8.797011315), not a canonical value; plaquette-signature counts differ between scripts by canonicalisation only; the depth-first index block of T_L inside T_{L+1} is the centre child's. New tests: `tests/test_phase5b_a_validation.py` (14 tests: boundary conditions, graph construction, Q8 and SU(2) gauge invariance of spectra and classes, dense/LOBPCG/shift-invert agreement and monotone bottoms, exact Gaussian-integer entries and zero Hermiticity defect), `tests/test_phase5b_sweep.py` (9), `tests/test_phase5b_d_scaling.py` (7). `tests/test_phase5b_e_results.py` (5).

## 2. Structural-predictor analysis (Workstream B)

**Design (preregistered; protocol committed as 140a815 before any census result).** The admissible decoration space is finite: 3 choices for the centre frame and 3 parity-constrained choices for each of the 7 octants, 3⁸ = 6561 decorations including FR30. Rather than sampling 200, the census computes for **all** decorations the level-3 pinned bottom Y₃ (dense, exact) and the level-4 inter-tile plaquette class counts plus 30 structural statistics; a preregistered random sample of 400 decorations plus FR30 (seed 20261022, drawn before any spectral computation) also gets the level-4 bottom Y₄ (LOBPCG, residual ≤ 1e-7). The census is processed in a fixed random order (seed 20261023) so that any completed prefix is a uniform subsample. Flux baseline: OLS on (f_trl, f_m1) with 10-fold cross-validation (fold seed fixed). Primary predictors (from Phase V-A, α = 0.05/3): depth-1 interface enrichment of traceless plaquettes, coefficient of variation of the per-tile count of −1 plaquettes, nearest-neighbour clustering of −1 plaquettes. Exploratory (Bonferroni over 28): depth-2/3 enrichments, CVs of other classes, class-pair correlation matrices for plaquettes sharing a panel or a tile, 2×1 and 2×2 loop-class fractions, hierarchical variances, axis-resolved fractions. Test statistic: out-of-sample ΔCV-R² with a 200-permutation p-value; collinearity by VIF against flux; exact-flux-matched groups (identical class-count vectors) give zero-tolerance matched comparisons.

**Status at stop.** 2371 of 6561 decorations in the census (a uniform random prefix by construction), 128 of 401 in the level-4 sample (FR30 included). Results: `audit/results/phase5b_sweep_analysis.txt`, data `audit/results/phase5b_sweep.json` (seeds, decorations, class counts, residuals, all predictor values), fits `audit/results/phase5b_sweep_fit_L{3,4}.json`.

**Outcome Y₃ (level 3, n = 2371).** Range 6.65–9.96, sd 0.54. FR30 = 9.3785, **rank 24** (23 decorations higher; the three highest, indices 1387, 4753, 3692, reach 9.956 and are symmetry copies of one another). Flux baseline $Y_3\approx0.808+14.212f_{\rm trl}+28.378f_{-1}$: in-sample R² 0.799, 10-fold CV-R² 0.798, CV-RMSE 0.242. FR30 residual **+0.613 = +2.53 sd**, residual rank 20 of 2371 (99.2nd percentile).

| predictor (level-4 statistic) | corr with Y₃ | VIF vs flux | ΔCV-R² | permutation p | FR30 percentile |
|---|---|---|---|---|---|
| **primary** enr1_trl | +0.04 | 1.45 | +0.0013 | 0.005 (significant at 0.0167) | 0.5 |
| **primary** cv_m1 | −0.56 | 1.64 | +0.0006 | 0.010 (significant) | 3.3 |
| **primary** pair_m1 | −0.37 | 1.18 | +0.0002 | 0.035 (not significant) | 4.3 |
| exploratory, best: loop21_f_m1 | +0.64 | **27.5** | +0.0130 | 0.005 | 80 |
| enr2_trl | +0.06 | 1.52 | +0.0058 | 0.005 | 0.5 |
| enr3_m1 | −0.48 | 1.34 | +0.0059 | 0.005 | 77 |
| Ct_m1_trl (tile-sharing class pairs) | −0.41 | 1.36 | +0.0031 | 0.005 | 90 |
| all others | | | ≤ +0.0016 | | |

Greedy forward selection (cross-validated, stop at +0.002): {loop21_f_m1, loop22_f_m1, enr2_trl, hvar1_m1, cv_m1} raises CV-R² from 0.798 to 0.851; under this model FR30's residual is still **+0.537 (+2.59 sd), rank 19**. The best exploratory predictor is collinear with $f_{-1}$ (VIF 27; it is the $-1$ fraction of 2×1 loops), i.e. a flux proxy, not a new mechanism.

**Outcome Y₄ (level 4, preregistered sample, n = 128).** Range 6.10–9.17. FR30 = 8.9196, **rank 2**: decoration **4757** (centre frame (2,0,1) and octant (0,0,0) frame (1,2,0) instead of FR30's (0,1,2), (0,1,2); all other frames identical) has $Y_4=9.1738$ and $Y_3=9.6711$, with $f_{-1}=0.0721$, $f_{\rm trl}=0.4564$. Flux baseline CV-R² 0.742 (RMSE 0.29); FR30 residual **+0.751 = +2.63 sd, rank 1 of 128**. No primary predictor is significant at level 4; forward selection (nine predictors, CV-R² 0.876) leaves FR30 at +0.426 (+2.33 sd), rank 4. corr(Y₃, Y₄) = 0.895 over the sample.

**Exact flux matching.** 2331 distinct level-4 class-count vectors among 2371 decorations; the only exact coincidences (groups of 3–5, spread 0.0000) are symmetry copies (global axis relabelings), so zero-tolerance matched comparisons between *different* decorations do not exist in this space; matched comparisons must use tolerances (as in §3) or the regression. There are 997 distinct Y₃ values among 2371 records, i.e. the census is effectively a census of ≈ 2.4 symmetry copies per distinct decoration.

**Reading.** Flux fractions are the dominant, reproducible predictor (80 % of the variance). The structural statistics available to a bounded-radius observer add little and leave FR30's residual essentially intact; FR30's own values of the significant predictors are extreme (0.5th–3rd percentile for interface depletion of traceless plaquettes and for frustration uniformity), consistent with Phase V-A, but these extremes are shared with other high-edge decorations and do not single FR30 out. Collinearity, selection effects and multiple testing were controlled as preregistered; the sample is a uniform random 36 % of the space, and the level-4 sample is 32 % of its preregistered size, both because computation was stopped.

## 3. Causal-control matrix (Workstream C)

All systems in this matrix share the chair geometry, the tile graph of the level-L supertile, the panel multiset, the Q8 link rule and the pinned diagonal; only the frame field is changed (`audit/phase5b_controls.py`, results `audit/results/phase5b_controls.txt`). The periodic Λ₇ crystal of Phase V-A differs also in geometry (translated chairs, 14-neighbour pattern) and is kept as a separate reference.

| system | fixed | changed | f_m1 / f_trl (L4) | λ_min L3 | λ_min L4 |
|---|---|---|---|---|---|
| FR30 | — | — | 0.080 / 0.401 | 9.3785 | 8.9196 |
| `fine` (3 seeds): random admissible rule at every inflation step except the last, FR30 at the last | finest-scale (level-1) FR30 blocks | coarse arrangement random, no self-similarity | 0.073 / 0.428–0.429 | 9.37–9.52 | 8.23–8.30 |
| `coarse` (3 seeds): FR30 at every step except the last, random rule at the last | coarse FR30 hierarchy | finest-scale frames random | 0.058 / 0.410–0.414 | 8.35–8.42 | 7.45–7.55 |
| `iid` (3 seeds): independent random admissible rule per parent at every step | block structure, parity rule | all scales random | 0.057–0.058 / 0.410–0.413 | 8.05–8.42 | 7.37–7.44 |
| `shuffle` (3 seeds): FR30's own rotations re-assigned among equal-parity octants per parent | multiset of local rotations per parent, parity rule | spatial arrangement of the FR30 rotations, self-similarity | 0.072–0.074 / 0.386–0.390 | 8.21–8.52 | 7.09–7.53 |
| `flip` p = 0.05 (2 seeds): FR30 with 5 % of tiles rotated about their own axis | FR30 everywhere else | 5 % local defects | 0.074–0.075 / 0.404–0.406 | 9.20–9.29 | 8.23–8.26 |
| `flip` p = 0.2 | FR30 everywhere else | 20 % local defects | 0.065 / 0.408 | 8.64 | 7.79 |
| `dec2238` (= Phase V-A seed 108, highest random control) | deterministic substitution | different rule | 0.087 / 0.388 | 9.02 | 8.61 |
| `dec2159` (= seed 4) | deterministic substitution | different rule | 0.106 / 0.366 | 8.89 | 8.40 |

Reading before the flux correction (§2 supplies it): destroying the arrangement of FR30's own rotations while keeping their multiset (`shuffle`) costs 1.4–1.8 at level 4 at nearly unchanged flux fractions; keeping only the finest-scale FR30 blocks (`fine`) retains most of the edge (8.23–8.30), whereas keeping only the coarse FR30 hierarchy (`coarse`) retains none of it (7.45–7.55, indistinguishable from `iid`); 5 % local defects cost 0.65. What cannot be matched simultaneously: the interventions change f_m1 by up to 0.02 (worth ≈ 0.7 in the periodic flux regression and ≈ 0.4–0.7 in the census baseline), so the quantitative attribution uses the census flux baseline residuals. **Flux-corrected attribution** (level-4 census baseline, rms 0.29; residuals in the table `audit/results/phase5b_controls.txt`):

| system | residual at level 4 | residual at level 3 |
|---|---|---|
| FR30 | **+0.75** | +0.64 |
| `fine` (FR30 blocks, random coarse arrangement) | −0.16, −0.18, −0.26 | +0.53, +0.35, +0.43 |
| `coarse` (FR30 coarse hierarchy, random finest frames) | −0.12, −0.20, −0.15 | −0.06, +0.03, −0.17 |
| `iid` | −0.25, −0.22, −0.31 | −0.01, +0.07, −0.35 |
| `shuffle` (FR30 rotations, random positions) | −0.19, −0.40, −0.60 | +0.04, −0.15, −0.23 |
| `flip` 5 % | +0.20, +0.14 | +0.65, +0.49 |
| `flip` 20 % | −0.02 | +0.06 |
| `dec2238`, `dec2159` | +0.44, +0.01 | +0.11, −0.26 |

At level 4 every randomization of the arrangement, at whatever scale, removes the whole flux-corrected excess (residuals at or below the population mean); the `fine` systems still carry an excess at level 3, where "random coarse arrangement" means a single random step above the FR30 blocks, and lose it at level 4, where two random steps intervene. Five percent of local frame defects remove about three quarters of the level-4 excess. Properties that cannot be matched simultaneously: each intervention changes $f_{-1}$ by up to 0.02 (worth 0.7 in the baseline), which is why residuals rather than raw bottoms are compared; and no intervention preserves FR30's exact class-count vector (exact matches exist only among symmetry copies, §2).

## 4. Eigenstate scaling (Workstream D)

Independent recomputation at levels 3–5 (own vectorised builder validated entry-by-entry against the object builders; dense, ARPACK shift-invert and own Chebyshev-filtered subspace iteration cross-checked to 8e-14) reproduces every stored IPR·n, interface weight and box-counting value; level-6 quantities are taken from stored artifacts. `audit/phase5b_d_scaling.py`, `audit/results/phase5b_d_scaling.txt`.

**D₂ by window** (ground state; D₂ = 3 ln(IPR_a/IPR_b)/ln(n_b/n_a); solver error ±0.000–0.009):

| window | 3→4 | 4→5 | 5→6 | 3→5 | 4→6 | 3→6 | LS 3–6 |
|---|---|---|---|---|---|---|---|
| FR30 ground | 2.49 | 1.88 | 1.90 | 2.18 | 1.89 | 2.09 | 2.07 ± 0.10 |
| FR30 lowest 8 | 2.32 | 1.69 | 1.65 | 2.00 | 1.67 | 1.89 | |
| cube control (same decoration hierarchy) | 2.61 | 2.26 | 2.14 | 2.43 | 2.20 | 2.33 | 2.33 ± 0.08 |
| trivial chair | 2.65 | 2.82 | — | 2.73 | | | |
| exact Dirichlet box | 2.75 | 2.87 | 2.93 | | | | → 3 |
| random decoration seed 108 | 2.25 | 0.84 | — | 1.54 | | | |

Within-level box counting gives local D₂(d) between 1.7 and 2.5 inside a single patch, with the mean over d ≥ 2 drifting 2.53 → 2.05 from level 3 to 6. The two largest windows agree (1.88, 1.90; D₃ ≈ D₂ within 0.24) but the 3→4 window does not, so **no single power law** is claimed. Energy-resolved analysis at level 5 (lowest 34 states): IPR·n 14.6–22.6 with no trend in energy, interface enrichment 3.6 for all, no spectral gap inside the group.

| explanation | verdict from the data |
|---|---|
| (1) hierarchical critical / multifractal state | supported in part (non-integer, window-stable D₂ ≈ 1.9 for 4→6, weak q-dependence); contradicted as a clean scale-invariant fractal (3→4 window 2.49, local D₂ drifts); asymptotics undecided below level 7 |
| (2) crossover localized → extended | contradicted at accessible sizes (extended controls move 2.7 → 2.9 → 3; FR30 flat at 1.9; no localizing trend either) |
| (3) ordinary states on a growing interface network | weak form supported (82–99 % of the weight within distance 1 of the depth-1 interface), strong form contradicted (the density on the network is itself hierarchical: P/T_L drifts 0.30 → 0.26, overlap with the uniform network state falls 0.40 → 0.25) |
| (4) finite-size / pinned-boundary effects | boundary weight excluded as the cause (2e-5 at level 6); but the pinned wall sets the child-weight hierarchy: the level-L ground state has overlap only 0.35, 0.23, 0.14 with the level-(L−1) state replicated in the centre child; whether this persists in the infinite-volume limit is undecided |

**Level 7.** Cost measured and extrapolated (dim 4 194 304, nnz ≈ 37 M, H ≈ 0.8 GB, 0.38 s per matvec, gap to the second pair ≈ 5e-6): LOBPCG 12–49 h, Chebyshev-filtered subspace iteration 6–12 h at 4–6 GB. The run was launched at 17:42 UTC with checkpoints and a 14 h budget (`audit/phase5b_d_level7.py`, validated at levels 4 and 5 against the stored values and the certified level-4 bound) and **stopped at 18:01 UTC on the user's instruction after pass 1** ($\theta_1=8.7981$, residual 2.4e-2, 93 block matvecs, 11.6 min; log `audit/results/phase5b_d_level7.log`). No level-7 eigenvalue or eigenvector is available; the asymptotic questions of this section stay open. Resume command and checkpoint design are in the script header.

## 5. Mathematics (Workstream E)

Deliverable: `deliverables/PHASE5B_E_MATHEMATICS.md` (ledger with hypotheses and status per statement). No new Lean kernel checks were produced in this phase; all new results are proofs outside Lean plus exact computational certificates.

**New rigorous bracket [P + X].**

$$\frac{72147403}{18000000}=4.008189056\;\le\;E_{\rm bulk}\;\le\;\frac{19748585252900893}{2251799811448142}=8.770133629330 .$$

Previous bracket: $3.2014583\le E_{\rm bulk}\le8.797011333$. Both ends rest on the framework's proved theorems (recognizability, repetitivity, the 72-type one-star closure, the quadratic-form identities), not on unique ergodicity.

- **Level-6 exact certificate [X]** (`audit/phase5b_e_level6_certificate.py`, result file and `audit/results/phase5b_e_fr30_level6_groundstate.npy`): the level-6 ground vector (LOBPCG, 2396 iterations, residual 2.2e-7, Kramers split 1.7e-12) rounded to $p=\mathrm{round}(2^{26}\psi)$; $\langle p,p\rangle=4503599622896284$, $\langle p,Hp\rangle=39497170505801786$, evaluated by two bit-identical exact routines (numpy int64 per-panel with chunked Python-int accumulation under an explicit overflow bound; pure-Python per-tile order), float sanity agreement 1.8e-15. The certificate lies 3e-10 above the float Rayleigh quotient; this replaces the floating-point value 8.77013 by an exact upper bound.
- **Radius-2 census and closure theorem [P + X]** (`audit/phase5b_e_radius2_bound.py`): the 2-star of a tile is the set of tiles owning a cube at Chebyshev distance ≤ 2 from a cube of the tile (215 positions). Lemma (parent radius): cubes at ℓ∞ distance ≤ r have parents within ⌈r/2⌉, so the r-star of a child is determined by the ⌈r/2⌉-star of its parent; radius 2 needs only the parent's 1-star. Theorem (closure): the set of legal 2-star types is Φ₂(V₁), the image of the 72 one-star types, and equals the forward orbit of any single legal 2-star; its size is **165**, and the complete 2-stars of T₅ (25 648), T₆ (232 560) and T₇ (1 976 560 of 2 097 152 tiles) are exactly these 165 types. The 3-block decomposition (each unit face lies in exactly 18 of the 3×3×3 cube blocks, so $\langle\psi,H\psi\rangle=\tfrac1{18}\sum_c k_c(\psi)$, checked exactly on T₃) gives $H\ge\tfrac1{18}\sum_a S_3(a)P_a$ with $S_3$ a function of the 2-star type; the 165×63 blocks reduce by rotation invariance to 162 signatures (dimension ≤ 20, $\lambda_{\min}\in[0.5868,1.7530]$, none flat), each certified positive definite above its rational $\mu_c$ by fraction-free Bareiss elimination over $\mathbb Z[i]$ in Python integers (600 randomized self-tests of the routine, including indefinite cases). Certified minimum over types: 4.008189056 (the float value 4.008197841 was C2's uncertified number). The 445 three-star types were also enumerated.
- **Exact constraints from the recursion [P + X]** (`audit/phase5b_e_recursion_correlations.py`, `audit/phase5b_e_ids_moments.py`): box objects (panel, plaquette, two parallel plaquettes sharing a panel, 2×2 rectangle of parallel edges, lattice vertex) satisfy their own affine recursions (parents of a box are a box; 49/108/366/266/66 types; verified coordinate-wise on T₂–T₄). Exact limits: adjacent parallel plaquettes have a joint class law that is **not** a product (ratios to the product of marginals 0.28–1.63; e.g. $P(-1,-1)=1/168$ against $f_{-1}^2=169/20736$); the 8-cube loop around a 2×2 square has class $\{-1\}$ with frequency 205/1344 and traceless with 497/672; a lattice vertex carries 0, 1, 2 or 4 (never 3, 5, 6) plaquettes of class $-1$ with frequencies 23/32, 59/448, 17/128, 15/896. The per-tile distribution of the number of $-1$ plaquettes among a tile's 48 inter-tile plaquettes is determined by the collared 72-type substitution Φ (column sums 8, characteristic polynomial $\lambda^{70}(\lambda-8)(\lambda-1)$, simple Perron eigenvalue): values 2, 4, 5, 6, 7, 8, 9 with frequencies 5/64, 3/8, 9/64, 3/32, 1/64, 13/64, 3/32, mean 11/2; the 157-type panel/plaquette recursion alone does not determine it. Exact IDS moments $\lim 8^{-m}\mathrm{Tr}(H_m^{\rm pin})^k=2,48,1296,37908,1169988$ for $k\le4$ (per state: mean 24, variance 72, skewness −0.088, kurtosis 1.846; trivial connection: variance 81).
- **What the recursion can and cannot say about the spectrum [P].** Every bounded-radius, Γ-invariant observable and every IDS moment is an exact rational via collared types (72/165/445 for radius 1/2/3). The substitution spectrum {8,4,2,1,0} depends only on poses: the trivial connection has the identical recursion, spectrum and frequencies, yet $E^{\rm triv}_{\rm bulk}=0$ while $E_{\rm bulk}\ge4.008$ here. There is no renormalization map on $\ell^2$ (S acts on counts), and the bottom of the spectrum is not fixed by finitely many moments. Nothing shows $E_{\rm bulk}$ rational or algebraic.

Caveats: the upper bound is exact but its tightness depends on the float solver; frequencies and moments are supertile-sequence limits, their identification with hull frequencies remains [C] as in the framework document; the box recursions are verified exactly for $m\le4$ and proved for all $m$ on paper. Three bugs found and fixed during the work (a zero-pivot shortcut in the Bareiss routine, a transposed einsum in the canonical form, and reporting lines) are documented in the ledger; all result files come from the corrected scripts. Tests: `tests/test_phase5b_e_results.py` (5 regression tests on the result files).

## 6. Physical realization and falsification protocol (Workstream F)

**Hamiltonian.** A two-orbital (spin-½) tight-binding model on the chair tiling: on-site energy 24 on every tile (hard-wall pinning on boundary tiles), hopping −C_ab on each shared unit panel with C_ab = (σ·M_aᵀn)(σ·M_bᵀn) ∈ Q₈ ⊂ SU(2), i.e. a non-abelian Peierls phase that is one of ±1, ±iσ_x, ±iσ_y, ±iσ_z; all hoppings have unit magnitude, so the model is a Q₈ synthetic gauge field on a fixed graph. Platforms where SU(2) link operators of this discrete kind are engineered: coupled photonic or microwave resonator arrays with polarization-dependent couplers (the two orbitals are two polarizations; ±1 and iσ_z are phase plates, iσ_x and iσ_y are polarization rotators), spin-dependent hopping in optical lattices with laser-assisted tunnelling, or transmon arrays with two modes per site. The chair tiling at level 4 has 4096 sites (8192 modes); level 3 has 512.

**Observable.** The lowest eigenfrequency of a finite, hard-wall-pinned patch (spectroscopically, the onset of the density of states measured by transmission or reflection into the lowest mode), compared between the FR30 frame field and a control frame field on the *same* graph with matched flux-class fractions. Prediction P-F1 **[E]**: at level 4 the FR30 patch lies 0.312 above the flux-matched substitution control (census index 2238, the highest-edge random control of Phase V-A: 8.9196 vs 8.6077 in units of the hopping), a difference that is 30 Kramers-pair spacings of the FR30 patch at that size. Prediction P-F2 **[E]**: the free (unpinned) patch is useless for this purpose, because its lowest mode is a surface state at 5.21 (boundary weight 0.93) for FR30 and 5.98 for the control; hard-wall pinning (on-site 24 on boundary tiles) is required.

**Required precision** (`audit/phase5b_physical.py`, `audit/results/phase5b_physical.json`, level 4, six realizations each):

| perturbation | FR30 shift (sd) | control shift (sd) |
|---|---|---|
| SU(2) link noise ε = 0.02 rad | +0.0007 (0.0017) | +0.0017 (0.0021) |
| ε = 0.05 | +0.0062 (0.0050) | +0.0116 (0.0034) |
| ε = 0.10 | +0.026 (0.010) | +0.050 (0.008) |
| ε = 0.20 | +0.115 (0.019) | +0.188 (0.012) |
| on-site disorder W = 0.5 | −0.012 (0.007) | −0.012 (0.005) |
| W = 1.0 | −0.034 (0.017) | −0.024 (0.022) |
| W = 2.0 | −0.146 (0.025) | −0.076 (0.024) |

The 0.31 separation survives link errors up to ε ≈ 0.1 rad and on-site disorder up to W ≈ 1 (4 % of the on-site energy). **Falsification protocol.** Build both patches at level 3 or 4 with the same couplers; measure the lowest pinned mode of each; the prediction fails if the FR30 mode is not higher than the control's by at least 0.2 hopping units at level 4 (0.3 at level 3: 9.378 vs 9.017), or if the ordering is reversed. Boundary and finite-size effects are part of the prediction (it is stated for the pinned finite patch, not for the infinite-volume edge). No Standard-Model, cosmological or gravitational consequence is claimed: none follows from this lattice Hamiltonian without an additional derivation, which does not exist here.

## 7. Ranked unresolved questions

1. **Is the edge excess a property of a family of fully self-similar rules, and which rule is maximal?** 23 of 2371 sampled decorations beat FR30 at level 3 and decoration 4757 beats it at level 4; the remaining 64 % of the census and the level-4 bottoms of the top level-3 decorations (indices 1387/4753/3692 at 9.956) were not computed. A complete census at level 3 (≈ 2 h) and level-4/5 runs for the top 30 would settle it.
2. **What non-local quantity predicts the flux-corrected residual?** Every bounded-radius statistic tried fails; candidates not yet tested are spectral-recursion quantities (the lowest eigenvalue of the level-1 block operator with the parent's boundary condition; transfer-matrix or renormalization data of the pinned patch), which the interventions suggest since the excess needs consistent arrangement across all levels.
3. **Does $D_2\approx1.9$ persist at level 7, and is the ground state asymptotically a new object at each level?** Needs the stopped level-7 run (6–15 h) or a cheaper surrogate (periodic approximants with legal seams do not exist).
4. **Can the bracket $[4.008, 8.770]$ be closed from below?** The radius-3 census (445 types) and a 4×4×4-block decomposition are the next certified step; the gap to the numerical edge (≈ 4.76) is dominated by discarding cross-block correlations.
5. **Which conjugacy-class correlation beyond radius 2 distinguishes FR30 and 4757 from the population?** Exact rational correlation limits exist now for radius-1 and radius-2 objects (§5); extending them to the predictors of question 2 and comparing FR30 with 4757 and with the `fine` interventions is the most direct route to a mechanism.

## 8. Run log, inventory, reproduction

**Stop record.** All runs killed at 18:01:48 UTC (census lanes PIDs 2035/2038, level-4 sample 3569, level-7 3739/3740); no Python process remained. Incomplete at stop: census 2371/6561, level-4 sample 128/401, level 7 at pass 1 of ≈ 30.

**Commits on `claude/phase5b-excess-mechanism`** (from `main` aa05095): 140a815 (preregistered protocol, before any census result) … 2aede8a (report; this hash-recording commit follows it) (final). 91 files added, 0 modified, 0 deleted relative to `main`.

**New code (audit/).** `phase5b_sweep.py` (census, level-4 sample, merge, preregistered analysis), `phase5b_controls.py` (hierarchy interventions), `phase5b_physical.py` (robustness), `phase5b_a_validation.py` (baseline reproduction), `phase5b_d_scaling.py` (independent scaling), `phase5b_d_level7.py` (checkpointed level-7 solver and exact certifier), `phase5b_e_level6_certificate.py`, `phase5b_e_radius2_bound.py`, `phase5b_e_recursion_correlations.py`, `phase5b_e_ids_moments.py`.

**Results (audit/results/phase5b_*).** `phase5b_sweep.json` (2371 census records + 128 level-4; seeds 20261022/20261023), `phase5b_sweep_census_shard{0,1}.jsonl`, `phase5b_sweep_level4_shard0.jsonl`, `phase5b_sweep_analysis.txt`, `phase5b_sweep_fit_L{3,4}.json`, `phase5b_controls.jsonl/.txt`, `phase5b_physical.json`, `phase5b_a_*` (baseline table and per-group data), `phase5b_d_*` (scaling tables, cost, per-system solves and weights, level-7 log and level-4/5 validations), `phase5b_e_*` (level-6 certificate and eigenvector, radius-2 bound and types, correlation and IDS-moment limits, star frequencies).

**Deliverables.** `deliverables/PHASE5B_REPORT.md` (this file), `deliverables/PHASE5B_E_MATHEMATICS.md`, `audit/results/phase5b_a_baseline_reproduction.md`.

**Tests** (`python3 -m unittest tests/<file>`): `test_phase5b_a_validation.py` 14, `test_phase5b_sweep.py` 9, `test_phase5b_d_scaling.py` 7, `test_phase5b_e_results.py` 5; all pass (run in this session). Phase V-A suites were not re-run in this phase.

**Reproduction commands** (repository root, `OMP_NUM_THREADS=1`, `python3 -u -I`):
```
python3 -u -I audit/phase5b_sweep.py census <shard> <nshards>   # level-3 bottoms + level-4 predictors (random order, resumable)
python3 -u -I audit/phase5b_sweep.py level4 <shard> <nshards>   # level-4 bottoms for the preregistered sample
python3 -u -I audit/phase5b_sweep.py merge && python3 -u -I audit/phase5b_sweep.py analyze
python3 -u -I audit/phase5b_controls.py run fr30 iid1 iid2 iid3 coarse1 coarse2 coarse3 fine1 fine2 fine3 shuffle1 shuffle2 shuffle3 flip1,0.05 flip2,0.05 flip1,0.2 dec2238 dec2159
python3 -u -I audit/phase5b_controls.py table
python3 -u -I audit/phase5b_physical.py 2238
python3 -u -I audit/phase5b_a_validation.py            # see its docstring for stages
python3 -u -I audit/phase5b_d_scaling.py cost | solve <system> <level> | analyze
python3 -u -I audit/phase5b_e_level6_certificate.py 6 3300
python3 -u -I audit/phase5b_e_radius2_bound.py 7
python3 -u -I audit/phase5b_e_recursion_correlations.py ; python3 -u -I audit/phase5b_e_ids_moments.py
OMP_NUM_THREADS=2 python3 -u -I audit/phase5b_d_level7.py run 7 [--resume]   # 6-15 h, 4-6 GB; then: certify 7
```
**Not done / blockers.** Census 64 % incomplete and level-4 sample 68 % incomplete (stopped on request); level 7 stopped at pass 1; no new Lean kernel checks (all new mathematics is paper proof plus exact certificates); the level-4 bottoms of the decorations above FR30 at level 3 were not computed; the `shuffle` intervention was corrected once (the first version permuted frames across positions and broke the tiling; only the corrected version's results are reported).
