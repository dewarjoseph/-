# Phase VIII — What selects the value of the FR30 spectral edge? Interface response, a renormalization fiber, and a self-similar selection chain

**Repository state.**
- Branch `claude/phase8-interface-recursion`, from main 585e05a, which contains Phases V-A to VII (PRs #6, #7 and #8 merged).
- Definitions are those of `deliverables/PHASE7_DEFINITIONS.md` unless stated otherwise.

**Labels.**

| label | meaning |
|---|---|
| [P] | proof written here or cited |
| [C] | certified computation: exact or rigorous error bound |
| [E] | floating-point evidence |
| [X] | exploratory |
| [U] | unresolved |

**The question this phase answers.** Phases VI–VII proved that the geometry *forces* a spectral effect: non-trivial curvature for every compatible frame field, a uniform gap, local rules at radius 1, and a localization theorem. They did not explain *why the effect takes the value FR30 exhibits*, E_* ≈ 8.764. Phase VIII is about that second question.

---

## 0. Result

**Outcome: B for the recursive state, C for the hierarchy question, not A.**
- **B.** The exact object carried between scales is the gauge class of the labelled surface response R_m(E), whose dimension grows like 4ᵐ. No fixed finite-dimensional subspace contains it (Prop. 8.1e).
  - Every scalar or bounded-radius summary tested fails by explicit counterexample (§7).
  - The information the earlier low-rank compressions lost is identified: the **environment-selected seam modes** (§3).
- **C.** No hierarchy-specific spectral law separate from local legality is supported. The control that could isolate one cannot exist (§6c).
- **Not A.** A fixed local fiber per copy works numerically at levels 5–6, with held-out errors in §4(e). At level 7 its error (d = 58) stalls near 0.006 while the level decrement shrinks fivefold. No closed law has a proven or rigorously bounded relation to the edge.

**Strongest theorem (Theorems 8.2–8.3, §5.2) [P], with a certified consequence [C].**
- *Hypotheses.*
  - H = 24 − A_U for the FR30 Clifford–Q₈ connection on the Chair44 hull.
  - The radius-1 local rules 𝒯₁ = Ω_FR30 (Phase VII Thm 6.2).
  - Minimality of Ω_FR30.
- *Statement.* For every 1-star type τ that is a Φ-self-loop, U_m(τ) = λ_min(H|σᵐ(τ)) has three properties:
  - it is a functional F_τ(R_m) of the level-m response;
  - it is non-increasing in m;
  - it converges to E_* from above.
  - So **E_* = lim_m F_τ(R_m)**: the edge is the limit of a monotone sequence of interface-response functionals along one self-similar configuration.
- *Selection [C, E].* Over all 72 legal configurations, the minimum is attained by the self-loop pair τ₅₉/τ₆₃ (x ↔ z mirror images) at m = 1, 2, 3. At m = 4, τ₃₅/τ₃₉, which have the same Φ-images as τ₅₉/τ₆₃, agree with it to 3·10⁻¹⁰, below solver accuracy.
- *Certified consequence.* **E_* ∈ [7.954292, 8.7642270381]**. The upper end is an exact rational Rayleigh quotient on σ⁵(τ₅₉), and improves V-E's level-7 bound.

**Strongest obstruction [P, by example].** Rules 937 and 938 have identical level-4 class counts, axis by axis, yet their bottoms differ by 0.278, 0.250 and 0.244 at levels 3, 4 and 5. So conjugacy-class frequencies are not a sufficient state. It is the only such collision among the 1097 class-count values of the full 6561-rule census.

**Artifacts.** The ledger `audit/results/phase8_ledger.json` lists every claim with its result file and test:
- `phase8_patch_bounds.json` (all 72 types, m ≤ 4);
- `phase8_chain_m5.json` (the exact certificate);
- `phase8_classpair.json` (the census search);
- `phase8_env_fiber.json` and `phase8_copy_rg.jsonl` (the fiber and the held-out copy-lattice edges);
- `certificates/Phase8Shadows.lean` (the Q₈ shadow characters, kernel-checked);
- `tests/test_phase8.py`.

**Remaining logical gap.** "Why 8.76" is reduced to the limit of one monotone sequence F_τ₅₉(R_m), but not to a closed characterisation:
- (i) selection of τ₅₉/τ₆₃ is proved for no m: it is computed for m ≤ 4;
- (ii) the chain's decrement ratio r ≈ 0.15–0.17 is measured, not derived;
- (iii) no finite-dimensional fixed-point problem whose edge is E_* has been found;
- (iv) the certified interval is still 0.81 wide.

The next computation (§11) targets (iii).

---

## 1. Baseline (one page)

**The target.**
- E_* := inf σ(H_Y), with H = 24 − A_U on ℓ²(Y) ⊗ ℂ² (bounded, self-adjoint, domain all of ℓ²) and Y any element of the FR30 hull Ω_FR30.
- On the infinite tiling Deg ≡ 24, so H = D_U†D_U.
- E_* does not depend on Y: Ω_FR30 is minimal, so trial vectors transport between hull elements.
- Its spectral *type* (absolutely continuous, singular continuous, or point) is unknown. "Band edge" is therefore not used.

**What "8.76" is.** 8.764911988 = E₇ = λ_min of the *pinned* level-7 supertile T₇ (2 097 152 tiles), a converged floating-point eigenvalue with residual 1.0·10⁻⁸.
- It is a finite-volume Dirichlet-type eigenvalue.
- Because T₇ is a compression of the hull operator, E_* ≤ E₇, certified as E_* ≤ 8.7649120247 by an exact integer Rayleigh quotient (V-E).
- It is **not** E_* itself. The V-E extrapolations give E_* ≈ 8.7631–8.7637, conditional on the decrement ratios. The selection chain of §5.3 gives the sharper conditional interval [8.76385, 8.76423]. Both rest on unproved ratio hypotheses.

| claim | status | source |
|---|---|---|
| E_* ∈ [7.954292, 8.7649120247] at the start of this phase; **[7.954292, 8.7642270381] after it** | [C] | Phase VII Thm 7.1 (lower); V-E certificate, then §5.3 (upper) |
| E_L = λ_min H_pin(T_L) is non-increasing and → E_* | [P] | V-E E6; Phase VII (compression plus covering) |
| exact child→parent Schur recursion (D0–D2) and the inertia correspondence (E1) | [P] | V-D, V-E; re-validated here |
| compression theorems: edge error ↔ uncaptured boundary weight (E3–E5) | [P] | V-E |
| no a-priori (child-derived) compression ≤ 10 % meets 0.05 at level 4 | [E] | V-E §3 |
| an environment-selected T₃-copy state (≈ 34/56 dimensions) saturates through level 7 | [E, X] | V-E §6.2 |
| forced curvature; uniform gap 41789/25000; local rules 𝒯₁ = Ω_FR30 | [P/C] | Phases VI–VII |
| FR30's excess over the flux model lives on the coarse seams | [E] | V-E §5 |
| what selects the value of E_*; what the minimal recursive state is | [U] at the start of this phase | this report |

---

## 2. The exact interface recursion

**Objects** (V-D/V-E notation).
- T_m is the pinned level-m supertile.
- S_m are its surface tiles (those with a missing panel neighbour); I_m is the rest.

**Surface response.** For E < λ_II(m) := λ_min H_{I_mI_m},

  R_m(E) = H_{S_mS_m} − E − H_{S_mI_m}(H_{I_mI_m} − E)⁻¹H_{I_mS_m},

a Hermitian matrix on ℂ^{2|S_m|}. All eight children of a parent have *the same* R_m(E) as a matrix in their own canonical tile order (Theorem D0: links depend only on relative frames).

So the state at scale m is **one matrix-valued function**; no spin conjugation is needed.

**The renormalization map 𝓡.**
- Glue eight copies: K_{m+1}(E) = ⊕_c Π_c R_m(E) Π_cᵀ − V_{m+1} on Σ = ∪_c S_m^{(c)}. Here V_{m+1} is the set of inter-child panel hoppings, and Π_c relabels child c's surface into the parent.
- Split Σ = S_{m+1} ⊔ J_{m+1}: the parent's outer surface and the inner seam tiles.
- Then R_{m+1}(E) = K[S,S] − K[S,J] K[J,J]⁻¹ K[J,S] =: 𝓡_E(R_m(E)).
- This is exact by quotient-formula transitivity (V-D Thm D2), and was validated at m = 1…4 to 7·10⁻¹⁵.

**Proposition 8.1 (structure of 𝓡) [P].** For E below the interior spectrum of T_{m+1}:

- **(a) Variational form.** x†R_m(E)x = min over ψ with ψ|_{S_m} = x of ⟨ψ, (H(T_m) − E)ψ⟩. R_m(E) is the energy of the best extension (a discrete Dirichlet-to-Neumann form).
- **(b) Loewner monotone and concave.** If R ⪯ R′, then 𝓡_E(R) ⪯ 𝓡_E(R′). The map R ↦ 𝓡_E(R) is concave.
  - *Proof.* By (a) applied to K, x†𝓡(R)x = min_y [x; y]†K(R)[x; y], and K(R) is affine in R. A minimum of affine functions is monotone and concave. ∎
  - *Consequence: comparison principle.* Responses bounded above or below at scale m propagate to bounds at every larger scale.
- **(c) Energy derivative.** dR_m/dE = −I − X†X ⪯ −I (V-E E1(iv)).
- **(d) Gauge covariance.** Under a tile-diagonal SU(2) gauge g, R_m ↦ g_S R_m g_S† and 𝓡 commutes with it (V-E E2). Kramers symmetry is preserved.
- **(e) Dimension.** |S_m| = 8, 53, 287, 1331, 5723, 23 723, 96 587 for m = 1…7. The successive ratios are 6.6, 5.4, 4.64, 4.30, 4.15, 4.07, tending to 4 (area). **The exact state space grows.** No finite-dimensional space is invariant under 𝓡 that contains the actual R_m for all m: dim S_m → ∞, and R_m(E) ≻ 0 for E < E_m has full rank.

**What the parent needs from the child.** Exactly R_m(E) on the *labelled* surface S_m (up to gauge).
- Its spectrum alone is not enough: conjugating R_m by a permutation of surface tiles that is not a geometric relabelling preserves every spectral invariant but changes the gluing, and hence the parent.
- The independent data are therefore the gauge-equivalence class of the labelled response. Interior Green functions, self-energies and pole residues are all functions of it: by the pole form R_m(E) = H_SS − E − Σ_j b_j b_j†/(l_j − E), poles and residues are recovered from R_m as a function of E.

---

## 3. Compression failure: what is missing

Every compressed representation below is tested on the same operator and the same edge (the pinned level-L bottom E_L, an upper bound on E_*). The error is E_W − E_L ≥ 0, a Ritz upper bound (Theorem E3), unless stated otherwise.

| # | representation | retained | discarded | evidence | verdict |
|---|---|---|---|---|---|
| 1 | scalar flux summaries (f₋₁, f_trl, Wilson density w) | conjugacy-class frequencies | arrangement, ordering, correlations | **counterexamples** (§7): rules 937 vs 938 have identical axis-resolved class counts, yet E₃/E₄/E₅ differ by 0.278/0.250/0.244. FR30 vs χ₁ have w = 0.5602 vs 0.5596 on the same graph and hierarchy, yet E₅ = 8.797 vs 7.700 (certified infinite-volume gap ≥ 0.32, Phase VII) | **insufficient** (proved by example) |
| 2 | bounded-radius gauge-invariant statistics (the 45 V-B census statistics) | local loops and correlations to radius ≈ 2 | seam arrangement beyond radius 2 | the 937/938 pair agrees on 28 of the 45. It differs in the other 17: the per-tile spread of classes, −1 clustering, class-pair correlations and the 2×1/2×2 loop fluxes. V-D: bounded radius explains 15 % of FR30's residual | **insufficient** |
| 3 | low-rank child response (k softest Kramers pairs of R_c) | the child's own soft spectrum | modes excited by the environment | V-E: calibrated RMSE 0.197 at 5.6 % of the boundary. Child modes capture 48–63 % of the deep local state at k = 20 | **insufficient** |
| 4 | face/hinge/corner bases, two-sided seam modes, patches | interface locality | in-seam structure | V-E: 0.25–0.26 at equal D, worse than child modes | **insufficient** |
| 4′ | all interface tiles (56 % of the boundary) | every seam degree of freedom | only the pinned outer wall | V-E: 0.017 RMSE | sufficient, but not a compression |
| 5 | **environment-selected fiber (new)**: U_env from the low states of the 72 legal 1-star patches σ³(τ), restricted to the central T₃ copy; no level ≥ 5 data | the response of a supertile to its legal 1-star environment | nothing systematic | captures **99.68 % / 99.79 %** of the level-6/7 copy restrictions at d = 58 (10 % of the T₃ surface), and 99.955 % at d = 114. Edge errors: E₅ +0.035 (d = 58), +0.005 (d = 114); E₄ +0.015 (d = 114), +0.0041 (d = 200); held-out E₆: +0.0085 (d = 58), +0.0021 (d = 114); held-out E₇: +0.0059 (d = 58), above E₆ | **sufficient to ≈ 0.002–0.006 at levels 5–7**, not uniformly in the level |
| 6 | exact labelled surface response R_m(E) | everything | — | exact (D2) | exact; dimension grows (§2e) |

**The decisive answer.** The discarded degrees of freedom that account for the unexplained parent response are the **environment-selected seam modes**: the components of a supertile's surface response that its *neighbours* excite. Its own soft spectrum does not supply them.
- *Quantitative.* Both U_env and the child-mode basis live in the same 574-dimensional T₃ surface space.
  - At d = 58, U_env misses 0.2–0.3 % of the deep edge state's local restriction (levels 7 and 6).
  - At d = 20 the child-intrinsic basis misses 37–52 %.
  - The missing class is therefore range(U_env) ⊖ range(child modes).
- *Why it is local.* By the Phase VII local-rules theorem the neighbourhood of a level-m supertile is one of 72 legal 1-star types. So this information is finite at each scale, and computable from 72 patch problems of 4 608–13 824 tiles.

---

## 4. Scale evolution

**(a) The exact map does not close on a finite space.** dim S_m grows like 4ᵐ (§2e). Outcome B holds for the *exact* state.

**(b) But the environment-selected fiber is nearly scale-invariant** [E]. The edge state's restrictions to the copies of T_k need the following dimensions at fixed accuracy (within one level):

| copy T_k | copy surface (dims) | levels used | d for 99 % | d for 99.9 % |
|---|---|---|---|---|
| T₂ | 106 | 4–7 | 14–20 | 27–34 |
| T₃ | 574 | 5–7 | 16–25 | 34–41 |
| T₄ | 2662 | 6–7 | 20 | 29–39 |

Levels with only 8 copies are excluded, because 16 snapshots limit the rank (`phase8_fiber.json`, which also lists them).

The copy surface grows ×25 from T₂ to T₄; the fiber at fixed accuracy does not.

**(c) Convergence across levels** requires the copies to be deep in the bulk (L − k ≥ 3):

| copy | transfer | capture at d = 32 | union of all levels, d for 99.9 % |
|---|---|---|---|
| T₂ | L5 → L6 | 0.998 | 38 |
| T₃ | L6 → L7 | 0.9926 | 56 |
| T₄ | L6 → L7 | 0.62 (not converged by level 7) | — |

The converged fiber grows mildly (38 → 56 from T₂ to T₃, while the surface grows ×5.4). Whether it stays bounded for T₄ and beyond is **[U]**: it needs level ≥ 8 data.

**(d) The fiber is constructive.** U_env is built from the 72 local environments alone. At d = 58 it captures 99.68 % and 99.79 % of the weight of the deep level-6/7 copy restrictions.
- As subspaces, U_env and the deep-trained 58-dimensional subspace agree in their leading directions: the median principal cosine is 0.992.
- They are not the same subspace: 20 of the 58 principal cosines are below 0.9, down to 0.04. These are directions in which the deep restrictions carry little weight.

**(e) The renormalized edge on the copy lattice** (block-sparse Galerkin with one fixed fiber in every copy; `audit/phase8_copy_rg.py`; validated against V-E closure5 to 10⁻⁵):

| L | copies | env d = 58 | env d = 114 | deep(6,7) d = 58 (in-sample at 6, 7) |
|---|---|---|---|---|
| 4 | 8 | +0.211 | +0.0151 | +0.449 |
| 5 | 64 | +0.0352 | +0.0050 | +0.0194 |
| 6 | 512 | +0.0085 | +0.0021 | +0.0011 |
| 7 | 4096 | +0.0059 | — | +0.00079 |

**Verdict on the brief's four options.**
- The exact map is closed only on a growing space.
- A truncation that works only down to a floor: a fixed fiber of dimension ≈ 58–114 per T₃ copy, with an envelope over a copy lattice whose size grows with the volume.
  - At d = 58 its held-out error is +0.035 (L5), +0.0085 (L6) and +0.0059 (L7). As fractions of the level decrement E_{L−1} − E_L that is 0.29, 0.32 and **1.13**.
  - At level 7 the d = 58 prediction, 8.7708, lies **above** E₆ = 8.7701: it does not even predict that the edge decreases. The fixed fiber's error stalls near 0.006 while the decrement shrinks fivefold.
  - At d = 114 the error is +0.0050 (L5) and +0.0021 (L6), 0.04–0.08 of the decrement. Level 7 at d = 114 was not computed (estimated at more than 10 h).
  - The error is one-sided (Ritz) and measured, not bounded. **It is not controlled uniformly in the level.**
- No fixed point of 𝓡 itself was sought: 𝓡 acts on spaces of growing dimension. A fixed point is sought instead along the selection chain (§5).

---

## 5. The spectral edge

### 5.1 What the edge states look like [E]

**Stored converged edge states** (levels 5, 6, 7) of the pinned supertiles (`phase8_geo.json`; the outer-wall weight and the pair splitting are from V-E's `phase5e_level7.json`):
- They are **bound transversally to the coarsest seams**. The weight at graph distance 0/1/2 from the depth-1 seams is 0.58/0.26/0.07 (L5), 0.57/0.26/0.06 (L6) and 0.51/0.24/0.06 (L7). This profile is level-independent, while the seams' tile fraction halves each level (0.171, 0.089, 0.046).
- They are **extended along the seams**: the radius of gyration divided by the box size is 0.26, 0.29, 0.28.
- They are **not boundary artefacts**: the weight on the outer wall at L7 is 10⁻⁶.

**The near-degenerate level-7 pairs** (splitting 3·10⁻⁶) sit on different mid-plane seams:
- pair 1 is symmetric between the x and z planes;
- pair 2 favours the y plane.

This matches one seam state per mid-plane.

**Effective dimension.** Transversal binding plus in-plane extension is consistent with D₂ ≈ 2 (V-A/V-E windows 1.9, 1.9, 1.5). The edge is approached by **effectively two-dimensional seam states**. Finite-volume evidence only: no infinite-volume localisation claim is made.

**Transverse tail.** Slab compressions at L5, with half-width w around the mid-planes, cost (`phase8_slab.json`):

| slabs | w = 6 | w = 8 | w = 12 |
|---|---|---|---|
| single plane | +0.082 | +0.036 | +0.011 |
| all three planes | +0.033 | +0.013 | +0.0045 |

**Near-edge density of states [E, U]** (`phase8_dos.json`). The question is whether the counting function near the edge has a stable scaling form. Here N_L(δ) = #{eigenvalues of H(T_L) ≤ E_L + δ}:

| δ | 0.005 | 0.01 | 0.02 | 0.05 | 0.1 | 0.2 |
|---|---|---|---|---|---|---|
| L4 (4 096 tiles) | 2 | 2 | 2 | 8 | 18 | 42 |
| L5 (32 768 tiles) | 10 | 24 | 48 | 72 | 78 | 278 |

- **The finite-volume spectrum near the edge comes in clusters.** At L5 there are:
  - 24 Kramers pairs within 0.0174 of E₅;
  - 12 more in [0.023, 0.040];
  - 3 at 0.063;
  - then a gap of 0.039 before the next band begins at 0.103.
  - These are mini-gaps of one finite supertile. They say nothing about gaps of the hull operator.
- **The three lowest pairs at each level are near-degenerate,** consistent with one state per mid-plane. Their splittings above the ground pair are 0.029/0.037 (L4), 0.0020/0.0034 (L5) and 3.1·10⁻⁶/4.6·10⁻⁶ (L7, V-E). They shrink by ×11–15 from L4 to L5 and by ×25–27 per level from L5 to L7, much faster than a 1/size² level spacing (×4 per level).
- **No scaling form is determined.**
  - Inside the first L5 cluster, the local counting exponent is 1.6 (δ 0.004–0.008) and 1.3 (0.008–0.016). V-A found 1.03–1.22 at L4.
  - A two-dimensional seam band predicts exponent 1 and, at fixed δ, a ×4 growth per level (area). A three-dimensional bulk edge predicts 3/2 and ×8 (volume).
  - The measured L5/L4 ratios are 9, 4.3 and 6.6 at δ = 0.05, 0.1 and 0.2. Two usable levels do not decide between them. The question stays **[U]**.

### 5.2 Theorems linking the recursion to the edge

**Theorem 8.2 (patch energies are functionals of the renormalized response) [P].**
- For a legal 1-star type τ and m ≥ 1, σᵐ(τ) is a union of |τ| level-m supertiles. Each has response R_m(E) in its own canonical order.
- The Schur reduction onto their surfaces (Theorem E1 for the partition into the |τ| copies) gives
  U_m(τ) := λ_min(H|σᵐ(τ)) = the root of λ_min[⊕_{t∈τ} Π_t R_m(E) Π_tᵀ − V_τ] = 0, with V_τ the inter-supertile hoppings fixed by τ's geometry.
- Hence U_m(τ) = F_τ(R_m) depends on the state R_m only, and **E_* = lim_m min_τ F_τ(R_m)** (by (c) below).

**Theorem 8.3 (selection chains) [P].** Let τ be a Φ-self-loop: the 1-star of child c of the central tile has type τ again. (FR30 has 9 such types; see `phase8_patch_bounds.json`.) Then:
- **(a)** σᵐ(τ) ⊂ σᵐ⁺¹(τ), so U_{m+1}(τ) ≤ U_m(τ).
  - *Proof.* σ(τ) contains the 1-star of child c, a copy of τ. Inflate m times and apply interlacing.
- **(b)** U_m(τ) ≥ E_*, by compression to a legal patch.
- **(c)** U_m(τ) → E_*.
  - *Proof.* The central supertiles nest, T_m ⊂ T_{m+1}, and σᵐ(τ) contains every tile within Chebyshev distance 2ᵐ of T_m. So the patches exhaust a tiling Y* all of whose patches are legal, and Y* is in the hull.
  - For a nested exhausting sequence, λ_min(H|P_m) ↓ inf σ(H_{Y*}). That limit equals E_* by minimality. ∎
- More generally, U_m(τ) → E_* for *every* τ, by repetitivity: σᵐ(τ) contains a ball of radius 2ᵐ. Without nesting, though, the sequence need not be monotone.

**Proposition 8.4 (poles and the edge) [P], with numbers [E].** The poles of R_k(E) are the interior Dirichlet eigenvalues l_j(k) of H_{I_kI_k}. R_k is analytic on (−∞, λ_II(k)), with λ_II(k) = l₁(k).
- **(a)** E_* ≤ U_k(τ) ≤ E_k ≤ λ_II(k), by interlacing: σᵏ(τ) contains a copy of T_k, and I_k ⊂ T_k.
  - So every edge quantity of this section is a zero of λ_min of a response on its pole-free branch.
  - At finite k, no pole or near-pole defines an edge.
- **(b)** λ_II(k) is non-increasing and converges to E_*.
  - Non-increasing: an interior tile of a child copy is interior in the parent, so I_k embeds in I_{k+1}.
  - Convergence: I_k contains balls of radius ∝ 2ᵏ (as in 8.3(c)).
- **(c)** The poles approach the edge fast (`phase8_poles.json`):
  - λ_II(k) − E_k = 6.66, 0.576, 0.0289, 0.0022 for k = 2, 3, 4, 5: about ×15 per level. This is consistent with the edge state's vanishing surface weight.
  - Measured from the certified upper bound, λ_II(k) − E_* ≥ 1.190, 0.184, 0.035 for k = 3, 4, 5.
- **(d)** Hence the edge of the infinite system is the accumulation point of the responses' first poles. A response of a large copy is evaluated near a pole at E ≈ E_*.
  - This is why the copy lattice of §4(e) uses T₃: E_* lies at least 1.19 below the first pole of R₃, and R₃ is smooth there.
  - For copies of T₅, the margin would be 0.035.

### 5.3 Edge selection [C, E]

U_m = min_τ U_m(τ) (`phase8_patch_bounds.json`):

| m | patch tiles | U_m | minimising types |
|---|---|---|---|
| 1 | 72–216 | 9.3484266 | 59, 63 |
| 2 | 576–1 728 | 8.8607858 | 59, 63 |
| 3 | 4 608–13 824 | 8.7795327 | 59, 63 (35, 39 at +1.3·10⁻⁷) |
| 4 | 36 864–110 592 | 8.7662711 | 39, 35, 59, 63 (agreeing to 3·10⁻¹⁰, below solver accuracy; the self-loop 27 at +4·10⁻⁶) |
| 5 | 884 736 (τ₅₉ only) | **8.7642270** (residual 5·10⁻¹²) | — |

**The minimiser is the same self-loop pair at every scale computed** (at m = 4 to within solver accuracy).
- Type 59 sits in slot 5, octant (1,0,0), and loops through child 5. Type 63 sits in slot 2, octant (0,0,1), and loops through child 2. They are mirror images under x ↔ z.
- The pair is closed under Φ through children 2 and 5.
- Φ(35) = Φ(59) and Φ(39) = Φ(63): the central tile's children have the same 1-star types. The gap between 35/39 and 59/63 shrinks from 9.1·10⁻⁴ (m = 1) to 8.8·10⁻⁵, 1.3·10⁻⁷ and 3·10⁻¹⁰ (m = 4), consistent with the difference being pushed outward by each inflation.

**The selected state** (`phase8_chainloc.json`). The lowest state of σᵐ(τ₅₉) straddles the face seam between the central supertile and one neighbour.
- The central supertile carries weight 0.34 at m = 2 and 0.28 at m = 3. That neighbour carries 0.23 and 0.21.
- It sits at a fixed relative position: the centre of mass is at (0.33, 0.13, 0.31) and then (0.30, 0.13, 0.29) of the supertile side.
- Its radius of gyration doubles per level (5.6 → 11.0), so the state is approximately self-similar.
- By contrast, the self-loop τ₂₆ (U₃ = 8.9037, 0.12 higher) centres its state inside the central supertile: centre of mass at the supertile's centre, central weight 0.57 and 0.46.

**Rate.**
- Along τ₅₉ the decrements are 0.48764, 0.081253, 0.0132617 and 0.002044, with ratios 0.1666, 0.1632 and 0.1541: nearly stable, drifting slowly down.
- A geometric tail at the last ratio gives E_* ≈ 8.76385. This is conditional: if every later ratio is ≤ 0.1541, then E_* ≥ 8.76385, by V-E's Theorem E7.
- V-E's extrapolation of the *pinned supertiles* is the same construction: a geometric tail at their last ratio, E₇ − d₇·0.1943/(1 − 0.1943) = 8.76365. Their ratios also drift (0.33, 0.27, 0.22, 0.19). It lies 2·10⁻⁴ lower [E].
  - At m = 4 the chain extrapolated to 8.76368, within 3·10⁻⁵ of V-E. The m = 5 decrement was smaller than that extrapolation assumed, and the agreement did not survive.
  - Both sequences' ratios are drifting down. Under that trend a tail at the last ratio overstates the remaining decrease, so both values are lower estimates, and the chain's is the sharper. They are not independent confirmations of a common value.
- The chain's ratio r ≈ 0.15–0.17 is its scale law, U_m − E_* ≈ C·rᵐ, with an effective exponent −log₂ r ≈ 2.6–2.7.

**Certified bounds.**
- **New certified upper bound: E_* ≤ 95969095435322528/10950092349041091 = 8.7642270381.** This is the exact rational Rayleigh quotient of the rounded U₅ eigenvector on σ⁵(τ₅₉), a legal patch of 884 736 tiles (`phase8_chain_m5.json`).
  - It improves V-E's level-7 bound 8.7649120247 by 6.85·10⁻⁴, using 42 % of T₇'s tiles and 29 minutes instead of 6.8 hours.
- Together with Phase VII: **E_* ∈ [7.954292, 8.7642270381]** (certified).
- Conditional on the chain ratios: E_* ∈ [8.76385, 8.76423].

**Answering the brief's questions.**
- *Is E_* bounded by a convergent sequence of interface-derived estimates?* Yes, from above: U_m(τ₅₉) = F_τ₅₉(R_m) decreases to E_* (Thm 8.2–8.3).
- *From below?* The Phase VII localization bound Λ_R gives |Λ_R − E_*| ≤ ε(R) ≤ K S₁/(R − r_c)². So the *two-sided* rate comes from localization (O(R⁻²)), and the upper side from the recursion.
- *An ε_R derived from the recursion alone?* Not obtained. The conditional rate needs the decrement ratio, which is not proved.

---

## 6. Matched controls

**(a) Seam binding at level 5** (same graph and operator; ground pair; `phase8_seamctl.json`):

| system | E₅ | weight on depth-1 seams (enrichment) | IPR·n | edge state |
|---|---|---|---|---|
| FR30 | 8.797 | 0.58 (3.4) | 20 | seam-bound, extended |
| rules 1387 / 2238 / 3697 | 9.393 / 8.494 / 9.122 | 0.59 / 0.56 / 0.36 | 22 / 36 / 8 | seam-bound |
| χ₁∘U_FR30 (Abelian) | 7.700 | 0.76 (4.5) | 126 | seam-bound, more compact |
| χ₂∘U_FR30 (Abelian) | 5.387 | 0.49 (2.8) | 7.6 | seam-bound, extended |
| Z₂ reflection | 3.455 | 0.41 (2.4) | 4.3 | extended, weak binding |
| trivial | 0.139 | 0.30 (1.8) | 3.3 | bulk |
| iid1 (random rule per parent) | 7.207 | 0.59 (3.4) | 185 | seam-bound, compact |
| coarse1 / fine1 / shuffle1 / flip 5 % | 7.24 / 8.17 / 7.02 / 8.03 | ≈ 0 – 0.02 | 340 – 584 | **localised on local defects** |

**(b) What the scrambling controls change** (`phase8_legality.json`). The fraction of tiles with an *illegal* 1-star at level 5:

| control | iid1 | coarse1 | shuffle1 | fine1 | flip 5 % | flip 20 % | FR30 |
|---|---|---|---|---|---|---|---|
| illegal 1-stars | 99.99 % | 100 % | 99.95 % | 86 % | 68 % | 98 % | 0 |

- These controls are not "same local statistics, different hierarchy". They change nearly every radius-1 configuration.
- The lower edges of coarse1, fine1, shuffle1 and flip come from **defect-localised states** (IPR·n 340–584) that legal tilings do not have. iid1's edge state is still seam-bound, but compact (IPR·n 185).

**(c) Impossibility of the requested matched control [P].** "Same legal local patches and frequencies, different long-range substitution correlations" does not exist:
- by Phase VII Theorem 6.2, every tiling whose 1-stars are all legal is in Ω_FR30;
- Ω_FR30 is uniquely ergodic (primitive substitution), so its patch frequencies are FR30's.

Long-range order and local configuration statistics are therefore not separately variable at radius ≥ 1.

**(d) Selection under the Abelian shadows** (`phase8_selection_controls.json`).
- χ₁'s minimiser is type 63, one of FR30's selecting types, at m = 1, 2, 3 (U₃ = 7.654402).
  - At m = 2, 3 its four lowest types are exactly FR30's set {35, 39, 59, 63}. At m = 1 the set is not separated: types 58, 39, 56 follow within 6·10⁻⁴.
  - The near-degenerate pairing differs: 63 ≡ 39 and 59 ≡ 35, against FR30's 59 ≡ 63 and 35 ≡ 39.
- χ₃, the x ↔ z mirror image of χ₁, has the same U_m (to 10⁻⁷), with minimiser 59 in place of 63.
- χ₂ selects a **different and unstable** set: {27, 34, 58, …} at m = 1, {0, 25, 1, 3, …} at m = 2, {56, 55, 57, 34, …} at m = 3. At m = 3 its four lowest types lie within 3·10⁻⁶.

The edge-selecting configuration is therefore **connection-dependent**, not fixed by the geometry and hierarchy alone.

**(e) What survives as hierarchy-specific.**
- Nothing beyond local legality. The extended seam-bound edge goes with a legal (self-similar) local structure: four of the five scrambled controls lose it to defect-localised states, and the fifth (iid1) keeps a compact seam-bound state.
- The non-Abelian contribution, isolated against the hierarchy-preserving shadow χ₁, is certified ≥ 0.32 in infinite volume (Phase VII).
- A "hierarchy-specific spectral law" separate from local legality is not supported, and by (c) it cannot be isolated by any control of the requested kind.

**(f) Coverage of the brief's control list.**
- Trivial links, reflection-only Abelian links, and randomized decorations: rows of (a).
- Q₈ links with matched local flux statistics: rules 937/938 (§7). Same graph, same hierarchy, identical class counts, different edges.
- Legal-patch-preserving controls: impossible, by (c).
- **Periodic controls: not run.** Level-k supertiles on a periodic lattice (V-A §5.1 item 4) have illegal seams by construction. Like the scrambling controls of (b), they change radius-1 configurations, so they could not isolate the hierarchy either.

---

## 7. Minimal sufficient state

| candidate state | sufficient for the parent edge? | evidence |
|---|---|---|
| (f₋₁, f_trl), Wilson density | **no**, explicit counterexamples | rules 937/938: identical axis-resolved class counts, ΔE = 0.278/0.250/0.244 (L3/4/5), reproduced in `tests/test_phase8.py`. FR30 vs χ₁: Wilson density within 0.1 % (0.5602 vs 0.5596 at level 4, Phase VII-B; their class frequencies differ), ΔE₅ = 1.10 |
| + depth enrichments, hierarchical variances (28 statistics) | **no** | 937/938 agree on all 28 |
| + per-tile class spread, −1 clustering, class-pair correlations, 2×1 and 2×2 loops (the other 17) | not refuted | these are exactly the statistics in which 937/938 differ |
| child soft spectrum (k pairs per child) | **no** (only to 0.2 at 5.6 %) | V-D, V-E |
| environment-selected fiber (d per copy) × envelope on the copy lattice | **to a measured error at levels 5–7**: 0.005 / 0.0021 at d = 114 (L5 / L6); 0.0059 at d = 58 (L7), where it stalls | §3, §4 |
| exact labelled response R_m(E) | **yes, exactly** | D2 |

**How rare the counterexample is** (`phase8_classpair.json`, the full census of 6561 rules).
- The level-4 class-count vector (n₊, n₋, {n_i, n_j, n_k}) takes 1097 values: 1087 are shared by 6 rules, 9 by 3 rules and one by 12 rules.
- Within every group but the last, all rules have the same level-3 bottom (to 10⁻⁷).
- The 12-rule group, which contains 937/938, splits into two families of 6 rules with different spectra: E₃ = 8.4910 vs 8.2134, E₄ = 8.0357 vs 7.7855, E₅ = 7.9728 vs 7.7285.
- So in the census the class counts fail to determine the edge exactly once, where two families with different spectra share their counts. This proves insufficiency. It does not show that the counts predict poorly across the census.

**Exact-closure statement.**
- **[P] No fixed subspace.** R_m(E) ≻ 0 for E < E_m, so its rank is 2|S_m|, which grows like 4ᵐ. No fixed finite-dimensional *subspace* contains the actual responses at every scale.
- **Not excluded.** A finite-*parameter* family of growing matrices reproducing R_m for every m is not excluded by this argument. What is measured instead [E]:
  - the information that the parent edge actually uses needs a *volume-growing* envelope over a fixed per-copy fiber of dimension ≈ 58–114 (§3–§4);
  - every scalar or bounded-radius summary tested is refuted by explicit counterexample (rows 1–2 of the table above).

---

## 8. How geometry, curvature and spectrum fit together

| ingredient | survives elimination of the interior? | role for the edge |
|---|---|---|
| local plaquette curvature (forced, Phase VII Thm 4.2) | partly: it fixes the class frequencies | **necessary but not sufficient** (the 937/938 counterexample) |
| gauge classes of boundary data | yes: R_m ↦ g_S R_m g_S† (E2) | the state is the gauge class of the labelled response |
| non-Abelian ordering | yes: holonomy *orderings* along boundary-connected paths enter R_m | FR30 vs χ₁: Wilson density within 0.1 %, same hierarchy, certified gap ≥ 0.32. 937/938: identical class counts, differing 2×1/2×2 loops and flux correlations, ΔE ≈ 0.25 |
| long-range substitution correlations | only through local legality (𝒯₁ = Ω) | they select *which* seam configuration hosts the lowest state (types 59/63) |
| spectral consequence | — | seam-bound, in-plane-extended edge states. Their energy at scale m is F_τ(R_m), minimised by a self-similar configuration |

---

## 9. Deliverables

**1. Exact recursion.** §2 (Prop. 8.1) and Theorem 8.2. Code: `audit/phase5d_schur.py` (V-D), tested in `tests/test_phase8.py`.

**2. Compression failure.** §3: the missing class is the environment-selected seam modes. Explicit counterexamples (§7): 937/938 for class-frequency states, and FR30 vs χ₁ for the Wilson density.

**3. Gauge-covariant state.** The gauge class of the labelled response R_m (exact). Its controlled truncation is a fixed fiber U ⊂ ℂ^{2|S_k|} per copy (one subspace in the copies' common substitution frame, Kramers-complete), transforming as U ↦ g_S U under gauge.

**4. Scale evolution.**
- The exact state grows (area law).
- The fiber is nearly scale-invariant (§4b), convergent at depth ≥ 3 (§4c) and locally constructible (§4d).

**5. Spectral edge.**
- Theorems 8.2–8.3: E_* = lim min_τ F_τ(R_m).
- The selection chain gives monotone, certified upper bounds.
- The seam-bound edge-state structure is §5.1.

**6. Matched controls.** §6:
- the scrambling controls are 68–100 % illegal at radius 1;
- the requested control is impossible;
- the shadows show that selection is connection-dependent.

**7. Reproduction.** See the commands below. The JSON outputs are listed in the ledger, and `tests/test_phase8.py` holds the tests.

**8. Corrected paper claim.**
> For the FR30 Clifford–Q₈ connection on the three-dimensional chair hierarchy, the bottom of the spectrum E_* (certified in [7.954, 8.7642]) is approached, in every finite supertile computed, by states bound to supertile seams and extended along them. For m ≤ 4, the lowest patch energy over the 72 legal local configurations is attained (at m = 4 to within solver accuracy) at one self-similar configuration of the hierarchy. Along any self-similar configuration the patch energies decrease monotonically to E_*; this is proved. The m = 5 member of the selected chain gives the certified upper bound.
>
> Exactly, the information carried between scales is the labelled surface response, a growing object. At levels 5–6 a fixed local fiber of ≈ 114 dimensions per level-3 copy, computable from the 72 legal environments alone, reproduces the supertile edge from above to within 0.005. At d = 58 the error stalls near 0.006 by level 7, so no accuracy uniform in the level is claimed.
>
> Plaquette-class frequencies do not determine the spectrum. No hierarchy-specific spectral law separate from local legality is established.

**9. Next experiment.** §11.

## 10. Errata to earlier phases

- **V-B/V-E controls** (`iid`, `coarse`, `fine`, `shuffle`, `flip`).
  - V-E §5 said that they "separate hierarchy from local statistics". At radius 1 they do not: 68–100 % of their tiles have illegal 1-stars.
  - Their spectral differences mix long-range order with changed local configurations. Statements attributing them to "the coarse hierarchical arrangement" (V-E §4.2, §5) are therefore **not causal**.
- **V-E's "saturating local state"** was open as to construction. A fiber built from the 72 legal radius-1 environments alone captures the same weight of the deep states (99.7–99.8 % at d = 58). So the information is available from the *radius-1* environment, not only "at depth". The two subspaces agree in their leading directions but not in all of them (§4d).

## 11. Remaining gaps and next decisive computation

**Remaining gaps.**
- That types {35, 39, 59, 63} minimise U_m for *all* m is not proved (all 72 types are computed for m ≤ 4).
- The fiber's boundedness for copies of T₄ and beyond is unverified.
- No recursion-only two-sided rate is derived.
- The spectral type at E_* is unknown, and no scaling form of the near-edge density of states is established (§5.1).

**Next decisive computation.** The **fixed point of the selection chain**.
- Along τ₅₉, σᵐ(τ₅₉) ⊂ σᵐ⁺¹(τ₅₉). Compute the restriction of the chain's ground state to the embedded copy (the "chain response") for m = 3, 4, 5 in the environment fiber, and test whether its normalised form converges, i.e. a fixed point of the chain map.
- If it does, E_* is the edge of a finite-dimensional fixed-point problem, and the convergence ratio of U_m is that map's leading eigenvalue. This is the first place where "why 8.76" could become a computable fixed-point characterisation rather than a limit.

## Reproduction

```bash
python -u -I audit/phase8_env_fiber.py 8
```
```bash
python -u -I audit/phase8_patch_bounds.py 4 6
```
```bash
python -u -I audit/phase8_selection_controls.py
```
```bash
python -u -I audit/phase8_chain5.py 5 59
```
```bash
python -u -I audit/phase8_copy_rg.py <L> <d> env|deep67
```
```bash
python -u -I audit/phase8_diagnostics.py geo fiber seamctl slab chainloc legality classpair poles dos
```
```bash
python -u -I audit/phase8_ledger.py
```
```bash
python -m pytest -q tests/test_phase8.py
```
```bash
lean certificates/Phase8Shadows.lean
```

Running times on the machine used here (24 threads, shared between concurrent runs):
- env_fiber ≈ 30 min; patch_bounds through m = 4 ≈ 1.7 h; selection_controls ≈ 42 min; chain5 ≈ 29 min;
- copy_rg ≈ 5 s (L5), 3 min (L6, d = 58), 1.7 h (L7, deep(6,7)) and 3.6 h (L7, env);
- diagnostics ≈ 6 min without `poles dos`, ≈ 23 min for those two.

Data dependencies:
- The level-4 to level-6 V-E eigenvectors are tracked under `audit/results/`. The level-7 one (`phase5e_fr30_level7_lowest4.npy`, 268 MB) is git-ignored, and is regenerated by V-E's level-7 run (≈ 6.8 h).
- Without it, the level-7 parts of env_fiber, `geo` and `fiber` cannot run.
- copy_rg reads both fibers from the tracked cache `phase8_fibers_k3.npz`, so it runs from a fresh clone.
