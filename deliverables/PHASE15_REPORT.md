# Phase XV — Boundary weight of the low-energy states on the top-level interface (rule 1387)

**Status labels.**
- [P] proved;
- [C] computed exactly or to rounding level;
- [E] floating-point evidence;
- [X] conjecture or extrapolation;
- [F] falsified.

**Scope.** Finite pinned and free supertiles of one rule (1387), levels L = 2–5. Gluing (geometric) error and localisation (epistemic) error are kept apart: §§2–5 concern gluing only; localisation enters only in §6.

**Artifacts.**

| role | file |
|---|---|
| protocol (frozen before any value) | `audit/results/phase15_preregistration_boundary_weight.json`, commit d8adbb1, sha256 `30e706f0…6a6e6a` (LF line ends) |
| driver | `audit/phase15_boundary_weight.py` |
| data | `audit/results/phase15_boundary_weight.json` |
| companion, **not preregistered** | `audit/phase15_neumann_weight.py` → `audit/results/phase15_neumann_weight.json` |
| tests | `tests/test_phase15.py` |

---

## 1. Question

> Do the low-energy states of the pinned operator H = 24 − A_U on T_L avoid the interface Γ_L that T_{L+1} introduces between its eight copies of T_L (weight ∝ R⁻³, Dirichlet-like), or are they spread (∝ R⁻¹)?

Definitions (protocol, verbatim in substance):
- T_{L+1} = `phase11_chair.supertile(dec, L+1)` in natural order; tile i lies in copy c = ⌊i / 8^L⌋.
- **Γ_L** = panels (a, b, k) of `phase11_chair.Patch.panels` with copy(a) ≠ copy(b). Top level only, not recursive.
- **A (primary).** ψ_k = eigenvectors of the copy block of H, normalised, extended by zero. w_L = ⟨ψ_k|P_Γ|ψ_k⟩ (P_Γ: tiles of the copy incident to Γ_L); g_L = Σ_{(a,b)∈Γ_L} |ψ_a − U_ab ψ_b|².
- **B (secondary).** φ_k = eigenvectors of H on T_{L+1}; w^B, g^B and the coupling c^B = ⟨φ_k|A_Γ|φ_k⟩.
- Primary statistic: exponent p_w of w_L ∝ 2^{−p_w L} (R ∝ 2^L), k = 0, maximum over the 8 copies. PASS p_w ≥ 2.5, FAIL p_w ≤ 1.5.

## 2. Exact facts used (all [P], each also checked [C])

**2.1 Γ_L is a surface.** |Γ_L| = 48 · 4^L exactly, L = 1–5 (`phase15_boundary_weight.json`, `Gamma_counts`; `test_gamma_is_a_surface_live`).

| L | 1 | 2 | 3 | 4 | 5 |
|---|---|---|---|---|---|
| \|Γ_L\| | 192 | 768 | 3 072 | 12 288 | 49 152 |
| tiles of T_{L+1} | 64 | 512 | 4 096 | 32 768 | 262 144 |
| tiles incident to Γ_L | — | 269 | 1 277 | 5 597 | 23 453 |

The fraction |Γ_L| / (panels of T_{L+1}) falls by 2 per level: the R⁻¹ law of the brief.

**2.2 Every copy block is H(T_L).** In natural tile order the pinned operator on each copy is entrywise the matrix of T_L (difference 0.0, L = 1–5; `copy_blocks_equal_H_T_L`). Proof: a copy is T_L moved by h_c, a signed permutation; row k of h_c G is ±(row k′ of G), and the two signs in U = (σ·row_k G_a)(σ·row_k G_b) cancel. So one eigenproblem serves all copies, and λ(copy) = λ_min H(T_L).

**2.3 Kramers pairing.** H commutes with J = iσ_y ∘ conj, J² = −1 (Q₈ ⊂ SU(2); already recorded in `deliverables/PHASE5D_NONLOCAL_SPECTRAL_RECURSION.md`). Every eigenvalue is doubly degenerate, and the tile density |ψ_a|² is the same for every vector of a Kramers pair, because ψ_a ⊥ (Jψ)_a in ℂ² with equal norms. So ψ₀, ψ₁ are one pair and their w, g coincide; ψ₂, ψ₃ are the next pair. Per-vector values are basis-independent (`test_kramers_pairing_live`).

**2.4 The one-step bracketing identity.** The pinned diagonal is 24 for every patch, so

  H(T_{L+1}) = ⊕_{c=0}^{7} H(T_L) − A_Γ  (exactly),

with A_Γ the hopping across Γ_L. Hence, with φ₀ the ground state of T_{L+1} and N_Γ = diag(number of Γ-panels at a):

  λ_L − ⟨φ₀|A_Γ|φ₀⟩ ≤ λ_{L+1} ≤ λ_L,  and ⟨φ₀|A_Γ|φ₀⟩ ≤ ⟨φ₀|N_Γ|φ₀⟩.

The right side: embed a copy ground state (⟨A_Γ⟩ = 0 on it; its Rayleigh quotient in T_{L+1} equals λ_L to 10⁻¹⁴, `rayleigh_in_T_L+1_minus_lambda`). The left side: ⟨φ₀|⊕H(T_L)|φ₀⟩ ≥ λ_L. The last inequality is 2 Re⟨x, Uy⟩ ≤ |x|² + |y|².

**2.5 For observable A, g is w reweighted.** ψ vanishes off its copy, so g = Σ_a n_Γ(a)|ψ_a|² and w ≤ g ≤ n_max w. The exponents of g and w coincide up to the drift of the mean panel count. This was frozen in the protocol (derived prediction 2) before any value.

## 3. Results, observable A (primary) [E]

k = 0 (equal to k = 1, §2.3); k = 2 is the second Kramers level. "max" is over the 8 copies.

| L | λ_L = λ_min H(T_L) | w_max (k = 0) | w_mean (k = 0) | g_max (k = 0) | w_max (k = 2) | g_max (k = 2) |
|---|---|---|---|---|---|---|
| 2 | 11.5871606 | 6.666·10⁻¹ | 2.877·10⁻¹ | 3.422 | 7.688·10⁻¹ | 4.093 |
| 3 | 9.9559188 | 7.357·10⁻² | 3.006·10⁻² | 3.070·10⁻¹ | 1.080·10⁻¹ | 4.439·10⁻¹ |
| 4 | 9.5168661 | 5.980·10⁻³ | 1.907·10⁻³ | 2.402·10⁻² | 7.275·10⁻³ | 2.918·10⁻² |
| 5 | 9.3928285 | 3.900·10⁻⁴ | 1.294·10⁻⁴ | 1.560·10⁻³ | 3.511·10⁻⁴ | 1.405·10⁻³ |

- λ_L agrees with the B-solve of T_L at the level below to 2·10⁻¹⁵ and lies below the stored exact Y_L (`cross_check_A_vs_B`, `check_against_stored_Y`).
- The centre copy (c = 0) carries the largest weight at every L, 2.7–4.6 times that of an octant copy (`copies[*].states[0].w`).

**Fits** (log₂ w = c − pL, L = 2–5; error = jackknife over the four leave-one-out slopes, and the largest leave-one-out deviation):

| statistic | p | jackknife SE | largest LOO deviation | local slopes (2→3, 3→4, 4→5) |
|---|---|---|---|---|
| **w, k = 0, max over copies (primary)** | **3.58** | **0.23** | 0.20 | 3.18, 3.62, 3.94 |
| w, k = 0, mean over copies | 3.73 | 0.20 | 0.20 | 3.26, 3.98, 3.88 |
| w, k = 2, max | 3.72 | 0.48 | 0.41 | 2.83, 3.89, 4.37 |
| w, 3-dimensional subspace (protocol), max | 3.63 | 0.32 | 0.28 | 3.04, 3.73, 4.09 |
| g, k = 0, max | 3.70 | 0.14 | 0.12 | 3.48, 3.68, 3.94 |
| g, k = 0, mean | 3.79 | 0.13 | 0.13 | 3.46, 3.97, 3.87 |
| g, k = 2, max | 3.85 | 0.36 | 0.31 | 3.21, 3.93, 4.38 |

**Verdict on the preregistered thresholds: PASS, p_w = 3.58 ± 0.23 ≥ 2.5 (Dirichlet-like).**

Reading:
- The prediction "p_g = 5" of the brief fails, as frozen derived prediction 2 said it would: p_g = 3.70 ± 0.14 against p_w = 3.58 ± 0.23, equal within error. Read on the brief's scale (5 Dirichlet, 3 uniform), 3.7 would wrongly suggest a near-uniform state; §2.5 is why that scale does not apply to observable A. On the lattice, the Dirichlet-like state falls to zero within one step, so its first-layer amplitude *is* the jump across Γ. There is no extra R⁻² from a gradient.
- The local slopes are 3.18, 3.62, 3.94. They rise past 3, while the Dirichlet box gives 3 + O(R⁻²). The depth profile shows where the weight goes: at L = 5 (copy 0, k = 0), the layers d = 0, …, 6 from Γ carry 0.0004, 0.0026, 0.0072, 0.025, 0.049, 0.076, 0.196, and 0.64 lies deeper. A slope above 3 is not explained by one box of side R. It is consistent with states that concentrate in a sub-region of the copy [X]; four levels cannot separate that from a pre-asymptotic approach to 3.
- Depth profile: the weight on the layers at graph distance d = 0, 1, 2, … from Γ inside the copy is recorded per state (`layer_weight`).

## 4. Results, observable B and the bracketing identity [E]

| L | λ_L | λ_{L+1} | drop λ_L − λ_{L+1} | c^B = ⟨φ₀\|A_Γ\|φ₀⟩ | ⟨φ₀\|N_Γ\|φ₀⟩ | w^B | g^B | drop / c^B |
|---|---|---|---|---|---|---|---|---|
| 2 | 11.5871606 | 9.9559188 | 1.631 | 3.555 | 6.057 | 0.877 | 2.502 | 0.459 |
| 3 | 9.9559188 | 9.5168661 | 0.4391 | 2.575 | 3.900 | 0.712 | 1.325 | 0.171 |
| 4 | 9.5168661 | 9.3928285 | 0.1240 | 2.080 | 3.073 | 0.590 | 0.994 | 0.060 |
| 5 | 9.3928285 | 9.3679502 | 0.02488 | 1.732 | 2.578 | 0.519 | 0.846 | 0.014 |

Exponents (same fit): drop 1.99 ± 0.14 (the R⁻² of the Y-ladder); c^B 0.34 ± 0.06; w^B 0.25 ± 0.04; g^B 0.51 ± 0.21. λ₆ = 9.3679501555 (ARPACK, residual 7·10⁻¹¹) lies below the stored Y₆ = 9.3679501571.

- **Derived prediction 3 (p_w(B) ≈ 1) is [F]**: the measured 0.25 ± 0.04 is slower. The tiles incident to Γ_L are 52 %, 31 %, 17 %, 9 % of T_{L+1} (L = 2–5), so a uniform state would give p = 1. The glued ground state concentrates on the interface region more strongly at each level.

- The bracketing identity holds at every level (`bracketing.holds`).
- The glued ground state is **not** small on Γ_L. Its weight on the incident tiles (w^B ≈ 0.6–0.9) is well above their share of tiles, because Γ_L bisects T_{L+1} and the pinned outer boundary pushes the state inward (derived prediction 3).
- The coupling c^B decays slowly (fit in the data file). The true one-step drop λ_L − λ_{L+1} decays like 4^{−L} (it reproduces the stored Y_L differences of `phase12_extrapolation.json` to 10⁻⁹). So the one-step lower estimate λ_{L+1} ≥ λ_L − c^B loses a factor 70 (c^B / drop = 1.732 / 0.0249) at L = 5, and the factor worsens with L.

## 5. Companion: the free (Neumann) copy states [E, not preregistered]

The lower-bound side of bracketing uses the free operator F = Deg − A_U on each piece, not the pinned one (`deliverables/PHASE10_REPORT.md`, Theorem X.2: F_k ≤ E_\*). On any chair tiling partitioned into level-L supertiles S, because Deg ≡ 24 there,

  ⟨ψ, (24 − A_U)ψ⟩ = Σ_S ⟨ψ_S, F_S ψ_S⟩ + Σ_{panels across the partition} |ψ_a − U_ab ψ_b|² ≥ Σ_S ⟨ψ_S, F_S ψ_S⟩.

The same weights for the lowest states of F on a copy:

| L | λ_min F(T_L) | w on Γ-incident tiles, max over copies (k = 0) | w on the whole surface (deg < 24) | surface share of tiles (uniform state) |
|---|---|---|---|---|
| 2 | 5.3003 | 0.959 | 0.969 | 0.828 |
| 3 | 5.6532 | 0.959 | 0.963 | 0.561 |
| 4 | 5.7299 | 0.948 | 0.961 | 0.325 |
| 5 | 5.7734 | 0.941 | 0.960 | 0.175 |

- **The free states sit on the interface.** 94–96 % of their weight is on the tiles incident to Γ_L, at every L. The exponent is p = 0.010 ± 0.003 (`fit_w_Gamma_max_k0`): no decay. A uniform state would put 0.83 at L = 2 and 0.17 at L = 5 of its weight on the surface layer.
- λ_min F saturates at 5.77 against E_\*(1387) ≥ 9.1104981. This reproduces the obstruction of `deliverables/PHASE10_REPORT.md` (lines 501, 608, 820: "F_k saturates … because free supertiles carry surface states"; class 1387 near 5.7).

## 6. The inequality that would be needed, and where it fails

A hierarchical lower bound must control, for every ψ below the floor and every piece,

  ⟨ψ|P_Γ|ψ⟩ ≤ A(R) ⟨ψ|(F − λ_N)|ψ⟩ + B(R) ‖ψ‖²,  λ_N = λ_min F,

with A(R)·(pinned penalty) + B(R) = o(R⁻²) so that the pinned penalty 24 − Deg lost on Γ can be restored at a gluing cost below the localisation rate.
- **B is the hard one.** Take ψ = the free ground state: ⟨ψ|(F − λ_N)|ψ⟩ = 0, so B(R) ≥ ⟨ψ|P_Γ|ψ⟩ = 0.94–0.96 for L = 2–5 (§5) [E]. B does not decay. This is the Phase X surface-state obstruction, now measured on Γ_L itself.
- A is a Poincaré-type constant and is not the obstruction: the pinned states give p_w ≈ 3.6 (§3), better than R⁻².
- **The measured exponent does not rescue Neumann bracketing.** p_w concerns pinned states, which enter only the upper side, where the gluing error is already exactly zero (§2.4, right inequality). The lower side is carried by free states, whose weight on Γ does not decay (§5).
- **What it does bear on** [X]. The exact Schur reduction onto the interface (`deliverables/PHASE5D_NONLOCAL_SPECTRAL_RECURSION.md`, Theorems D1–D2) eliminates the copy interiors with Dirichlet data. There the pinned modes enter through their coupling to Γ divided by their distance to the energy. With w ∝ R^{−p_w} and Y_L − E ∝ R⁻² (Aitken q ≈ 1/4), the lowest-mode term scales like R^{2 − p_w}. That is small exactly when p_w > 2, which the measurement supports at L ≤ 5. The uncontrolled quantity is then the bottom of the Schur complement on the infinite interface network, not a surface density of states. No estimate on it exists in the repo.

## 7. What this does not show

- No statement about E_\* follows: every number here is a finite-supertile quantity for one rule [E].
- Four levels fit a power law only locally; the local slopes are given, and the leave-one-out spread is the stated error.
- The certified frontier is unchanged.

## 8. Handoff tasks A–D (with p_w in hand)

- **A (rank).** The A1–A5 list of the handoff brief is not in the repo, in the brief supplied with this phase, or in the parallel clone, so its items are not ranked. They are not reconstructed, since that would invent them. Ranked instead are the five routes that are on file (`PHASE12_DECISION_MEMO.md`, "Why this, and not another"; this report), on the brief's scale: (i) certified for the infinite hull, (ii) certifiable with on-file methods, (iii) needs the rate.

  | route on file | class | reason |
  |---|---|---|
  | radius-24 certificate of 539311 (excludes 1389) | **(i)** | passed, 39 117 balls, E_\*(539311) ≥ 9.2083494 [C] (`PHASE12_REPORT.md` §14.3) |
  | radius-28 certificate of 539311 (excludes 539291) | **(ii)** | same method, μ above Y₇(539291) = 9.2483895; about 70 000 balls, 60 h on 4 cores [X cost] |
  | Y₈ upper bounds (16.8·10⁶ tiles) | **(ii)**, no frontier change | exact Rayleigh quotients, but upper side only, and 8× the memory of Y₇ |
  | IMS certificate separating 1387 and 539311 | **(iii)** | needs R ≈ 67–91 (R ≈ 46–62 with an adapted localisation) at the R⁻² rate (§14.3) |
  | hierarchical lower bound (Schur complement on Γ, §6) | **(iii)** | p_w = 3.58 ± 0.23 > 2 keeps it open [E]; the bottom of the Schur complement on the interface network has no estimate |

- **B (one-step bracketing).** Upper side: λ_{L+1} ≤ λ_L with zero gluing error [P] (§2.4). Lower side: E_\* ≥ λ_min F(T_L) [P] (Theorem X.2, `PHASE10_REPORT.md`). It fails by O(1): F saturates at 5.77 against E_\*(1387) ≥ 9.1104981, because the free states put 94–96 % of their weight on Γ_L (§5). The measured p_w = 3.58 ± 0.23 belongs to the pinned states and does not rescue the Neumann side (§6). It bears only on the Schur-on-Γ route, as an [X] condition p_w > 2.
- **C (preregistration).** Done before any value: `phase15_preregistration_boundary_weight.json`, commit d8adbb1.
- **D.** The strongest certified statement about the hull today is unchanged by this phase. Over all 1 679 616 frame rules the maximiser of E_\* is 1387, 539311 or 539291, and E_\*(539311) ≥ 9.2083494 [C] (`PHASE12_DECISION_MEMO.md`). This phase adds three exact facts: |Γ_L| = 48·4^L, H(T_{L+1}) = ⊕₈ H(T_L) − A_Γ, and the Kramers pairing of every level [P, C]. It adds one measurement: the pinned low-energy states avoid the future interface like R^{−3.6±0.2}, while the free ones sit on it [E]. The single computation that most changes the certified picture is still the preregistered radius-28 certificate of 539311 (about 70 000 balls and 60 h on 4 cores, `PHASE12_DECISION_MEMO.md`), which would exclude 539291. No hierarchical certificate can be stated until the Schur complement on Γ has a bottom estimate (§6).
