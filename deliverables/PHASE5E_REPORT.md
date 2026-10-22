# Phase V-E — Toward a renormalization theory of the FR30/Chair44 spectral edge: report

- **Branch.** `claude/phase5e-renormalization`, from the merged V-D head af8a365.
- **Protocol.** Frozen in f7db7e9 (`deliverables/PHASE5E_PROTOCOL.md`, `audit/results/phase5e_protocol.json`) before any evaluation-set value was computed.
- **Level-7 predictions.** Frozen in a781ad8 while the solver was at pass 1.
- **Status tags.** **[P]** proved (proofs in §2); **[E]** numerical, with the stated errors; **[X]** exploratory (not pre-registered, or added after the freeze); **[C]** conjecture. Earlier reports are not modified.

## 0. Result

**The conjecture is not supported in any tested form.** No gauge-invariant effective boundary state of dimension ≤ 10 % of the exact boundary operator predicts the level-4 edge to the frozen accuracy.

| primary configuration (D ≤ 459 = 10 % of dim S) | calibrated RMSE (C2 needs ≤ 0.05) | held-out CV-R², flux + E_W (C4 needs > 0.9216) | FR30 residual explained (C6 ≥ 0.5) | intervention directions, raw / residual sign (C5: 17/17, 16/16) | verdict |
|---|---|---|---|---|---|
| child(16), D = 256 | 0.197 | **0.9253** ± 0.0005 | **0.646** | **17/17**, 13/16 | FAIL (C2, C4 via C2, C5, C7) |
| face(4), D = 256 | 0.263 | 0.8796 | 0.422 | 14/17, 13/16 | FAIL |
| iface2(8), D = 256 | 0.264 | 0.8805 | 0.519 | 14/17, 12/16 | FAIL |
| fec(2), D = 290 | 0.260 | 0.8821 | 0.477 | 14/17, 13/16 | FAIL |
| patch2(4), D = 424 | 0.237 | 0.8968 | 0.427 | 14/17, 13/16 | FAIL |
| adaptive(229), D = 458 (trained on training folds only) | 0.176 | **0.9308** ± 0.0004 | 0.564 | **17/17**, 11/16 | FAIL (C2, C4 via C2, C5, C7) |
| *reference, not a compression:* `interface`, D = 2554 (56 %) | 0.017 | 0.9993 | 0.980 | 17/17, 16/16 | fails C1 only |

Gauge invariance (C3) holds for every family: max \|ΔE_W\| = 9.8×10⁻¹³ over 16 systems.

What the evidence supports:

1. **Proved theorems [P] (§2).**
   - *E1: exact Schur–inertia correspondence on the whole resolvent set of H_II.* It covers poles, multiplicity, the kernel isomorphism, Loewner monotonicity and concavity.
   - *E2: gauge classes.* It states which boundary quantities are invariant, which covariant, which basis-dependent, and why splitting a Kramers pair breaks invariance.
   - *E3: the edge error of any compression equals the Ritz defect up to a slope factor.*
   - *E4: a two-sided bound by the uncaptured boundary weight 1 − c.* The scales are μ₂ ≥ min(λ₃, λ_II) − E₀ and μ_max ≤ 48 − E₀.
   - *E5: an Eckart–Young lower bound for universal (copy-independent) subspaces.*
   - *E6: monotone edge.* *E7: conditional rate.*
   - *E0: the panel multigraph is identical for all 6561 decorations.*
   - *Four finite identities kernel-checked in Lean.*
   - *Numerical check.* E3 and E4 hold on all 6606 (system, basis) pairs.
2. **The best compression is useful but not a theory [E].**
   - E_W of child(16), a single number from a 256-dimensional state (5.6 %), is a better held-out predictor (CV-R² 0.925) than any V-D descriptor model without target information (M4: 0.917, 15 features).
   - It gets all 17 intervention directions right and explains 65 % of FR30's flux residual.
   - Its absolute accuracy (calibrated RMSE 0.20) is four times worse than required.
   - It fails exactly on the controls that keep FR30's finest scale and randomise the coarse arrangement (`fine1–3`). The missing information is the coarse hierarchical arrangement.
3. **The obstruction is quantified (H3) [E].**
   - Every a-priori family's error is nearly flat in D. Calibrated RMSE falls only from 0.23 to 0.17 between D = 64 and D = 512.
   - Uncaptured weight stays ≥ 17 % at D = 512.
   - The low spectrum of the supertile response obeys an *area law*: the eigenvalue count in a fixed window grows ×4.5–4.8 per level, exactly as the surface does (×4.64).
   - The support of the boundary ground pair tracks the interface area.
   - The only accurate reduction found removes the pinned outer boundary: interface tiles, a 1.8× compression. It is exact to 0.035 RMS and explains 98 % of FR30's residual. **So FR30's excess lives entirely in the seam region**, but not in any low-dimensional set of seam variables.
   - *Where on the seams [X].* The exact, gauge-invariant depth decomposition of E₀ places FR30's flux residual (+0.767) at the coarse seams: +0.90, +0.57 and +0.39 at depths 0–2, partly offset by −1.10 at the finest bonds. FR30's bond efficiencies at depths 0–2 are the lowest of all 264 classes (§5).
4. **The one positive structure is environment-selected, not child-intrinsic [E, X: exploratory, FR30, post-freeze].**
   - *Saturation.* The restrictions of the FR30 ground state to all copies of T₃ (8, 64, 512 and 4096 copies at levels 4–7) span a local state space that **saturates**: the cumulative dimension for 99.9 % is 12, 43, 55 and 56 out of 574.
   - *It is not the child's own low spectrum.* Low modes of R₃(E) capture only 48–63 % of it at k = 20, at any energy.
   - *It predicts a held-out level.* Trained on levels 6–7 only and used as the per-copy state of level 5 (64 copies), it gives **E_W − E₅ = +0.045 at 7.3 % and +0.019 at 10.1 %** of the boundary dimension.
   - *Scope of that success.* It meets the C1 and C2 bars in this one held-out-level test.
   - *Where it fails.* At level 4, where every copy touches the pinned wall, the same subspace is poor (0.45 at 10 %).
   - *What fails pre-registered.* The closure test trained on shallow levels (4–5 → 6 or 7) fails: 86 % < 99 %.
   - *What it supports.* An asymptotic, bulk renormalization state of about 40–60 variables per T₃ copy plausibly exists. It cannot be built from the child's spectrum, and it is not what the frozen level-4 criteria tested.
5. **Scale law [E].**
   - *Level 7.* E₇ = 8.7649120 (Ritz upper bound, residual 1.5×10⁻⁷; the 10⁻⁷ criterion on all four vectors was not reached by the cut-off).
   - *Frozen verdict.* r₇ = 0.194: by the frozen rule, the decrement ratio keeps falling (0.33 → 0.27 → 0.22 → 0.19). No single power law, L⁻² included, describes levels 4–7.
   - *Frozen envelope.* E₇ lies inside it. The geometric and ratio-trend predictions bracket it to within 7×10⁻⁴.
   - *Gap collapse.* The three lowest Kramers pairs lie within 5×10⁻⁶ of each other. D₂(6→7) ≈ 1.50, outside V-D's frozen critical window [1.8, 2.0]; this is caveated by unresolved eigenvectors.
   - *Boundary dependence.* The apparent D₂ ≈ 1.9 at levels 4–6 does not survive a Robin wall (≈ 1.1–1.2).
   - *Certificate.* The exact rational Rayleigh quotient of the level-7 vector **certifies 4.008189 ≤ E_∞ ≤ 8.7649120248**, improving V-B's certified upper bound 8.7701336.

The strongest negative statement supported is about the *tested families* and about *universal linear subspaces of the measured dimension at the tested levels* (E5). It is **not** a proof that every compression is impossible. Item 4 shows a compact state does exist asymptotically, selected by the environment rather than the child. Nonlinear states and non-subspace closures also remain open. §9 states the revised conjecture.

## 1. Evidence reproduced before any new computation

| item | check | result |
|---|---|---|
| census | 6561 decorations → symmetry classes (V-D key: level-3 bottom to 7 dp + level-4 class-count multiset) | 1098 classes: 1089 of size 6, 9 of size 3. FR30's class is {1386, 3690, 4752} |
| evaluation set | V-D `dataset()` equals the frozen protocol's `rule_indices` | identical, 264 classes with 264 distinct keys |
| controls | `phase5d_controls.jsonl` | 18 systems (fr30, iid1–3, coarse1–3, fine1–3, shuffle1–3, flip1/2 at 0.05, flip1 at 0.2, dec2238, dec2159) |
| target | level-4 bottoms re-derived here by shift-invert at 0 (H ≥ 0) and compared with the stored Y4 | max \|E₀ − Y4\| in §3 |
| level-3 FR30 bottom | dense, this machine | 9.378470210 (stored 9.378470210) |
| level-5 FR30 bottom | existing V-B ChebFSI solver through the new portable runner | 8.797011314651467 vs stored 8.797011314651474 (7×10⁻¹⁵) |
| geometry | Proposition E0: the panel multigraph is the same for all decorations | verified for FR30 and decorations 0, 950, 3697 and 6560 at level 3 |

**Assumption carried over from V-D.** The "symmetry class" key is empirical (spectrum plus class counts), not a proved orbit of the decoration symmetry group. It is used unchanged.

**Development set.** Four decorations, one per class outside the 264 (seed 20261026): 950, 1583, 1787 and 3133. They were the only systems used to shape the protocol (§8).

## 2. Mathematics: proofs [P]

Notation is as in `PHASE5E_THEORETICAL_CONJECTURE.md` §1. Matrices are finite and Hermitian. ≤ is the Loewner order. In(X) = (n₊, n₋, n₀).

**Proposition E0 (one geometry for every decoration).**
- *Step 1.* The chair {0,1}³ \ {(1,1,1)} is invariant under all six axis permutations (Lean: `chair_axis_permutation_invariant`).
- *Step 2.* Fix an octant v. The admissible frames there are D_{s(v)} π with π of parity (−1)^{|v|}, i.e. a coset π₀C₃ with C₃ the cyclic permutations. Changing π₀ to π₀c right-multiplies the child frame by c ∈ C₃.
- *Step 3.* Write G = G₀c for the changed frame. Then G·4w = G₀·4(cw): the child's own children are relabelled among the octant positions, as a set. Because c D_s c⁻¹ = D_{cs}, the grandchild that lands at a given position carries the sign matrix of that position. Its cube set therefore depends only on the position, by step 1. Induction on depth completes the proof.
- *Checked.* Cube sets and panel lists agree for FR30 and decorations 0, 950, 3697 and 6560 at level 3 (test). ∎

**Theorem E1 (correspondence on the full resolvent set).**
- *(i)–(iii).* Let E ∉ spec H_II and X = (H_II − E)⁻¹H_IS. Then
  H − E = Lᴴ diag(K(E), H_II − E) L,  with  L = [[1, 0], [X, 1]],
  a congruence by an invertible matrix (rows ordered S, I). Sylvester's law of inertia gives (ii), and determinants give (i). From L, ψ ∈ ker(H − E) if and only if Lψ = (ψ_S, ψ_I + Xψ_S) ∈ ker diag(K, H_II − E). Since H_II − E is invertible, this means ψ_I = −Xψ_S and Kψ_S = 0. That is (iii).
- *(iv).* d/dE (H_II − E)⁻¹ = (H_II − E)⁻². Hence K′ = −1 − H_SI(H_II − E)⁻²H_IS = −1 − XᴴX and K″ = −2H_SI(H_II − E)⁻³H_IS. For E < λ_II, (H_II − E)⁻³ > 0, so K″ ≤ 0. Integrating K′ ≤ −1 gives K(E′) ≤ K(E) − (E′ − E). Weyl monotonicity gives κ_j(E′) ≤ κ_j(E) − (E′ − E). κ₁(E) = min_{‖x‖=1} ⟨x, K(E)x⟩ is a minimum of concave functions, hence concave.
- *(v).* Let v be a unit ground vector of H_II with w := H_SI v ≠ 0, and take φ_ε = (εw, v). Then ⟨φ_ε, Hφ_ε⟩ = ε²⟨w, H_SS w⟩ + 2ε‖w‖² + λ_II, while ‖φ_ε‖² = 1 + ε²‖w‖². For small ε < 0 the Rayleigh quotient is below λ_II, so λ_min(H) < λ_II. On (−∞, λ_II), N_{H_II} = 0, so by (ii) N_H(E) = n₋(K(E)). The zeros of κ_j there are exactly the eigenvalues of H, with multiplicity by (iii), and κ₁ is strictly decreasing.
- *(vi).* Near a pole l, K(E) = −H_SIΠ_lH_IS/(l − E) + O(1). (ii) holds on every interval between poles. An eigenvector of H at E = l with ψ_S = 0 satisfies H_IIψ_I = lψ_I and H_SIψ_I = 0, and is invisible to K.
- *Checked.* Inertia at energies above λ_II (test). The kernel at E₀ is 2-dimensional (test). ∎

**Theorem E2 (gauge).**
- *Covariance.* G = ⊕U_a is tile-diagonal, so G = G_S ⊕ G_I and (GHGᴴ)_XY = G_X H_XY G_Yᴴ. Hence K ↦ G_S K G_Sᴴ, R_c ↦ G_{S_c} R_c G_{S_c}ᴴ, and spec H_II is invariant.
- *Covariant rules.* If a rule satisfies W(GHGᴴ) = G_S W(H), take bases with P′ = G_S P Q for some unitary Q. Then P′ᴴK′P′ = Qᴴ(PᴴKP)Q, so g_W, and with it E_W, is invariant.
  - *Tile coordinate subspaces.* These are invariant under G_S.
  - *Complete eigenspaces.* If X(GHGᴴ) = G X(H) Gᴴ, eigenspaces map to eigenspaces, so a union of complete eigenspaces is covariant. Principal submatrices on tile sets are covariant because G is tile-diagonal.
- *Kramers.* Q8 and SU(2) blocks commute with T (Lean: `kramers_commutes`; for SU(2), U(iσ_y)Ū = iσ_y). So T-invariant subspaces stay T-invariant, and Ritz matrices on them are quaternionic, hence Kramers-degenerate (test).
- *Non-example.* Three vectors (one and a half pairs) per child give a gauge-dependent E_W (test; deviation > 10⁻⁶). ∎

**Theorem E3 (edge error = Ritz defect).**
- *Lower bound g_W ≥ κ₁.* For any unit x ∈ ℂ^D, ⟨Px, KPx⟩ ≥ κ₁ (Cauchy interlacing).
- *Slope and concavity.* Apply E1(iv) to PᴴKP: (PᴴKP)′ = −PᴴP − (XP)ᴴXP ≤ −1, and the second derivative is ≤ 0.
- *Location of the root.* g_W(E₀) ≥ κ₁(E₀) = 0, so the root satisfies E_W ≥ E₀.
- *Secant bound.* The secant slope s = (g(E_W) − g(E₀))/(E_W − E₀) = −g(E₀)/(E_W − E₀) satisfies g′(E_W) ≤ s ≤ g′(E₀) ≤ −1, by concavity. This gives g(E₀)/|g′(E_W)| ≤ E_W − E₀ ≤ g(E₀).
- *Newton.* For a concave decreasing g, the tangent lies above the graph. A Newton step from a point with g > 0 therefore lands at or to the right of the root. A chord between bracket points lies below the graph, so the chord root lands at or to its left. Both bracket ends move every iteration (the solver in `phase5e_rg.Reduced.root`). ∎

**Theorem E4 (two-sided capture bound).**
- *Setup.* Let the ground level be one Kramers pair, Π₀ = span{ψ̂, Tψ̂} = ker K(E₀), with ψ̂ the unit S-part. Let W be T-invariant with projector Q = PPᴴ. Then [Q, T] = 0.
- *Capture is the same for both vectors of the pair.* ‖QTψ̂‖ = ‖TQψ̂‖ = ‖Qψ̂‖. Also ⟨ψ̂, QTψ̂⟩ = ⟨Qψ̂, TQψ̂⟩ = 0, because ⟨y, Ty⟩ = 0 when T² = −1. So PᴴΠ₀P has the single eigenvalue c = ‖Pᴴψ̂‖², counted twice.
- *Lower bound.* Let x ∈ W be the unit Ritz vector. Then ⟨x, K(E₀)x⟩ = ⟨x⊥, Kx⊥⟩ ≥ μ₂‖x⊥‖², where x⊥ = (1 − Π₀)x. Also ‖Π₀x‖² ≤ c, so ‖x⊥‖² ≥ 1 − c.
- *Upper bound.* Write ψ̂ = u + s with u = Qψ̂ and ‖u‖² = c. Since Kψ̂ = 0, ⟨u, Ku⟩ = ⟨s, Ks⟩ ≤ μ_max(1 − c), so g_W(E₀) ≤ ⟨u, Ku⟩/c ≤ μ_max(1 − c)/c.
- *μ_max.* μ_max ≤ λ_max(H_SS) − E₀ ≤ 48 − E₀, because −H_SI(H_II − E₀)⁻¹H_IS ≤ 0.
- *μ₂.* Let E* = min(λ₃(H), λ_II). For E ∈ (E₀, E*), N_H(E) = 2, so κ₃(E) ≥ 0. By E1(iv), κ₃(E₀) ≥ κ₃(E) + (E − E₀). Letting E → E* gives μ₂ = κ₃(E₀) ≥ E* − E₀. ∎

**Theorem E5 (Eckart–Young bound for universal subspaces).**
- *Setup.* Use the partition of E1 with S′ = ⋃ (surfaces of all depth-(L−k) copies of T_k). The interiors are disjoint, so H_{I′I′} is block-diagonal and E1–E4 apply verbatim.
- *Bound on the uncaptured weight.* For W = ⊕_j U,
  ‖(1 − Q_W)ψ_{S′}‖² = Σ_j ‖(1 − P_U)ψ|_j‖² = ‖(1 − P_U)X‖_F²·‖ψ_{S′}‖²/‖X‖_F² ≥ τ_d·‖ψ_{S′}‖²,
  by the Eckart–Young–Mirsky theorem. Here X is the matrix of restrictions (columns ψ|_j and (Tψ)|_j, normalised).
- *Consequence.* E4 then gives g_W(E₀) ≥ μ₂′τ_d. ∎

**Theorem E6 (monotone edge).**
- *Monotonicity.* H(T_{m+1}) = ⊕_c H_pin(T_m) − V (Theorem D0). Let x be a ground vector of child c's block, extended by zero. Then ⟨x, Hx⟩ = E_m − ⟨x, Vx⟩ = E_m, because V couples different children. So E_{m+1} ≤ E_m.
- *Strictness.* If Vx ≠ 0, take y = Vx (supported on other children). Then ⟨x + εy, H(x + εy)⟩ = E_m − 2ε‖Vx‖² + O(ε²) < E_m(1 + ε²‖y‖²) for small ε > 0.
- *Limit.* A decreasing sequence bounded below by 0 converges. ∎

**Theorem E7 (conditional rate).**
- If d_j ≤ ρ d_{j−1} for all j > m, then E_m − E_∞ = Σ_{j>m} d_j ≤ d_m Σ_{i≥1} ρⁱ = d_m ρ/(1 − ρ). ∎

**Lean [P, kernel-checked].** `certificates/Phase5ESymmetry.lean` contains `kramers_commutes`, `axis_factor_hermitian_unitary`, `link_in_Q8` and `chair_axis_permutation_invariant`. Compile log: `audit/results/phase5e_lean_compile.txt` (Lean 4.35.0). Axioms: none, none, propext, and propext + Quot.sound respectively. These are four finite algebraic facts. The analytic theorems E1–E7 are *not* formalized.

## 3. Compressions of the boundary response at level 4 [E]

**Data.**
- *Systems.* 264 rule classes, 18 controls and 4 development rules. Files: `audit/results/phase5e_L4_shard*.jsonl`, the summary `phase5e_results.{json,csv,txt}`, and the figures `deliverables/figures/phase5e_error_vs_dimension.*` and `phase5e_uncaptured_vs_dimension.*`.
- *Target.* The bottoms were re-derived here; they differ from the stored Y4 by at most 2.1×10⁻¹³.
- *Error definitions.* E_W is parameter-free and an upper bound (E3). "Raw" is E_W − E₀. "Calibrated" subtracts the training-fold mean of (E_W − E₀), using V-D's repetition-0 10-fold split, out of fold.

### 3.1 All configurations

| configuration | D | D / dim S | raw mean | raw RMSE | raw max | calibrated RMSE | calibrated max | p95 | capture c (median) | ρ_Spearman(E_W, Y4) | s / system |
|---|---|---|---|---|---|---|---|---|---|---|---|
| child(1) | 16 | 0.003 | 0.994 | 1.029 | 1.740 | 0.269 | 0.756 | 0.520 | 0.175 | 0.905 | 2.8 |
| child(4) | 64 | 0.014 | 0.910 | 0.938 | 1.494 | 0.230 | 0.591 | 0.433 | 0.408 | 0.925 | 2.1 |
| child(16) | 256 | 0.056 | 0.786 | 0.810 | 1.364 | **0.197** | 0.572 | 0.359 | 0.712 | 0.941 | 2.8 |
| child(32) | 512 | 0.111 | 0.681 | 0.702 | 1.207 | 0.172 | 0.521 | 0.302 | 0.827 | 0.951 | 6.1 |
| face(1) | 64 | 0.014 | 1.323 | 1.353 | 2.101 | 0.284 | 0.775 | 0.562 | 0.213 | 0.851 | 0.2 |
| face(4) | 256 | 0.056 | 1.157 | 1.187 | 1.997 | 0.263 | 0.835 | 0.518 | 0.451 | 0.873 | 0.9 |
| face(8) | 512 | 0.111 | 1.013 | 1.044 | 1.762 | 0.252 | 0.757 | 0.469 | 0.566 | 0.882 | 4.6 |
| iface2(1) | 32 | 0.007 | 0.937 | 0.974 | 1.705 | 0.266 | 0.765 | 0.518 | 0.195 | 0.872 | 0.2 |
| iface2(8) | 256 | 0.056 | 0.878 | 0.916 | 1.657 | 0.264 | 0.777 | 0.499 | 0.470 | 0.876 | 1.0 |
| iface2(16) | 512 | 0.111 | 0.830 | 0.868 | 1.636 | 0.257 | 0.804 | 0.495 | 0.586 | 0.880 | 4.7 |
| fec(1) | 160 | 0.035 | 1.315 | 1.344 | 2.094 | 0.281 | 0.777 | 0.558 | 0.419 | 0.854 | 0.4 |
| fec(2) | 290 | 0.063 | 1.224 | 1.251 | 2.026 | 0.260 | 0.797 | 0.504 | 0.609 | 0.872 | 1.1 |
| fec(4) | 520 | 0.113 | 1.068 | 1.091 | 1.827 | 0.226 | 0.754 | 0.433 | 0.762 | 0.904 | 4.0 |
| patch2(1) | 106 | 0.023 | 1.315 | 1.346 | 2.129 | 0.287 | 0.813 | 0.553 | 0.410 | 0.853 | 0.2 |
| patch2(4) | 424 | 0.092 | 1.123 | 1.147 | 1.936 | 0.237 | 0.814 | 0.460 | 0.723 | 0.896 | 2.6 |
| patch3(1) | 538 | 0.117 | 1.104 | 1.130 | 1.783 | 0.242 | 0.687 | 0.491 | 0.783 | 0.893 | 4.6 |
| adaptive(64) | 128 | 0.028 | 0.994 | 1.033 | 1.845 | 0.281 | 0.854 | 0.521 | 0.273 | 0.845 | 0.5 |
| adaptive(128) | 256 | 0.056 | 0.780 | 0.818 | 1.504 | 0.251 | 0.737 | 0.467 | 0.455 | 0.881 | 1.0 |
| adaptive(229) | 458 | 0.100 | 0.513 | 0.541 | 1.134 | **0.176** | 0.627 | 0.317 | 0.654 | 0.946 | 2.9 |
| adaptive(512) | 1024 | 0.223 | 0.187 | 0.204 | 0.739 | 0.083 | 0.554 | 0.165 | 0.907 | 0.988 | 140 |
| oracle(229) (uses target; not admissible) | 458 | 0.100 | 0.212 | 0.254 | 0.925 | 0.140 | 0.710 | 0.251 | 0.896 | 0.969 | 2.3 |
| `interface` | 2554 | 0.556 | 0.030 | 0.035 | 0.116 | **0.017** | 0.087 | 0.035 | 0.994 | 0.999 | 320 |
| `exact` (validation subset) | 4592 | 1 | 0 (≤ 10⁻¹²) | | | | | | 1 | | 50–200 |

**Matched dimensions.** Calibrated RMSE, log-interpolated in D:

| family | D = 64 | D = 128 | D = 256 | D = 459 | D = 512 |
|---|---|---|---|---|---|
| child | 0.230 | 0.217 | 0.197 | 0.176 | 0.172 |
| face | 0.284 | 0.272 | 0.263 | 0.253 | 0.252 |
| iface2 | 0.265 | 0.264 | 0.264 | 0.258 | 0.257 |
| fec | — | — | 0.265 | 0.233 | 0.227 |
| patch2 | — | 0.282 | 0.261 | — | — |
| adaptive | — | 0.281 | 0.251 | 0.175 | 0.163 |

**Reading.**
- *Accuracy improves only slowly with D.* Every a-priori family improves its calibrated error by less than 25 % over an eightfold increase in D.
- *Training-only tile selection is the only family that steepens.* `adaptive` reaches 0.175 at the 10 % cap, tying the best a-priori family, and 0.083 at D = 1024 (22 %). Even the oracle ceiling at the cap, which ranks tiles by the system's own ground state, gives only 0.140. *No choice of 229 tiles reaches C2.*
- *Face-type bases are worse than child modes at equal D.* This holds for one-sided faces, two-sided seams, the face/hinge/corner hierarchy and patches. Locality on faces is the wrong coordinate system for the *state* (§6.1).
- *Raw errors are large and positive (0.7–1.3).* That is the one-sided Ritz bias. Rank correlations with Y4 of 0.87–0.95 show that a large part of the inter-rule variation survives compression. The remaining error is still four or more times the tolerance.

### 3.2 Runtime and memory

- *Cost per energy evaluation.* For a child-local basis of dimension D = Σ d_c, building M_W(E) costs O(Σ_c |I_c| d_c²) with the pole representation, and the eigenproblem costs O(D³). Memory is O(Σ_c |I_c| d_c + D²).
- *Exact boundary operator.* It needs O(|S|²) memory (4592² complex, 0.34 GB) and O(|S|³) per evaluation.
- *Measured single-system timings (shared machine, 18 lanes).* Under 7 s for every configuration with D ≤ 512, about 320 s for `interface` (D = 2554), and 50–200 s for `exact`. Roots need 10–21 evaluations (mean), because many roots sit near the pole at λ_II.

### 3.3 Theorem checks and gauge [E]

- *E3.* E₀ ≤ E_W ≤ E₀ + g_W(E₀) holds for all 6606 (system, basis) pairs at level 4. The median of (E_W − E₀)/g_W(E₀) is 0.55: the edge error is about half the Ritz defect.
- *E4.* The upper bound (48 − E₀)(1 − c)/c and the lower bound min(gap, λ_II − E₀)(1 − c) hold for every pair.
- *Gauge (C3).* Each system was run with an independent random SU(2) matrix on every tile: 12 systems at level 3 (all families, plus `exact`) and 4 at level 4. The largest change in any E_W is 9.8×10⁻¹³.

### 3.4 Stability across levels (C7) [E]

Mean relative edge error (E_W − E₀)/E₀ at fixed family parameter, hence fixed D, over the 8 sweep systems (`phase5e_levels_*.jsonl`, figure `phase5e_error_vs_level.*`):

| configuration | L = 2 | L = 3 | L = 4 | L = 5 |
|---|---|---|---|---|
| child(16) | 0 (exact: D ≥ dim) | 0.097 | 0.104 | not completed |
| face(4) | 0.448 | 0.308 | 0.129 | not completed |
| iface2(8) | 0.448 | 0.302 | 0.092 | not completed |
| fec(2) | 0.049 | 0.145 | 0.141 | not completed |
| patch2(4) | 0.049 | 0.073 | 0.129 | not completed |
| patch3(1) | 0.049 | 0.022 | 0.132 | not completed |
| child(64) | 0 | 0 | 0.070 | not completed |
| `interface` | 0.049 | 0.022 | 0.003 | — |

- *Level 5 did not finish.* The four reference systems spent 2.5 h at level 5 under contention and were stopped at 03:55 to free memory for the level-7 certificate. The four development systems were stopped earlier, for memory. So C7(a) is evaluated from level 3 to 4 only.
- *Level 3 → 4.* child(16), fec(2), face(4) and iface2(8) do not grow beyond ×1.5; patch2(4) (×1.8) and patch3(1) (×6) do. The face-type errors *fall* with level, because at fixed D their faces are resolved better relative to the interior.
- *C7 fails anyway.* C7(b), the 95th-percentile calibrated error ≤ 0.10, fails for every family (0.32–0.52). That decides C7 independently of level 5.

### 3.5 Support of the boundary ground pair [E]

Tiles holding 99 % and 99.9 % of ψ_S, and the outer-boundary weight:

| system | L2 (53 interface tiles) | L3 (269) | L4 (1277) | L5 |
|---|---|---|---|---|
| FR30 | 58 / 64, outer 7.7 % | 268 / 367, 4.0 % | 860 / 1376, 0.41 % | 3071 / 4349 (5597 interface tiles), outer 0.05 % |
| 1387 | 56 / 63, 3.0 % | 253 / 357, 2.4 % | 840 / 1385, 0.48 % | — |
| 3697 | 59 / 63, 3.9 % | 262 / 348, 4.1 % | 870 / 1372, 0.42 % | — |
| 2238 | 54 / 62, 2.8 % | 267 / 356, 3.5 % | 1036 / 1604, 0.90 % | — |
| 950 (dev) | 57 / 62, 4.9 % | 238 / 333, 2.5 % | 559 / 920, 0.08 % | — |
| 1583 (dev) | 58 / 63, 7.5 % | 237 / 333, 2.9 % | 380 / 777, 0.20 % | — |
| 1787 (dev) | 53 / 62, 4.4 % | 237 / 334, 2.1 % | 458 / 910, 0.57 % | — |
| 3133 (dev) | 55 / 61, 5.2 % | 218 / 322, 1.7 % | 712 / 1186, 0.50 % | — |

- *The support grows with the interface.* The tiles for 99.9 % grow ×5.2–5.8 from L2 to L3 and ×2.3–4.5 from L3 to L4, while the interface grows ×5.1 and ×4.7. From L4 to L5 (FR30, from the stored level-5 vector) the 99.9 % count grows ×3.2 and the interface ×4.4. This confirms prediction P2.
- *The outer boundary drops out.* The pinned boundary's weight falls below 1 % by level 4, confirming P3. The `interface` error (0.030 mean) is consistent with that.
- *Within S at level 4,* faces carry 44–58 % of the weight, hinges 7–29 % and corners up to 21 %.

## 4. Held-out prediction, interventions and FR30 [E]

### 4.1 Held-out prediction

- *Procedure.* This is V-D's procedure, unchanged: rule-level 10-fold CV, 20 repetitions, folds from `default_rng(20261024 + r)`, and ridge α chosen by inner 5-fold CV. M7:*family* = flux (f_trl, f_m1) + E_W of the family's primary configuration: a single compressed state variable. M0, M2, M4 and M6 were refitted in the same loop.
- *Reproduction check.* M0 and M2 reproduce V-D's frozen numbers exactly; M4 and M6 agree to within 0.0005.

| model | CV-R² | CV-RMSE | flux-residual variance explained |
|---|---|---|---|
| M0 flux only | 0.7986 ± 0.0011 | 0.2727 | 0 |
| M2 + Y3 (previous-level edge) | 0.8900 ± 0.0008 | 0.2015 | 0.454 |
| M4 + c1 + 12 gluing penalties (V-D) | 0.9169 ± 0.0021 | 0.1751 | 0.588 |
| **M7:child (+ E_W of child(16), one variable)** | **0.9253 ± 0.0005** | **0.1661** | **0.629** |
| M7:patch2 | 0.8968 ± 0.0007 | 0.1952 | 0.488 |
| M7:fec | 0.8821 ± 0.0009 | 0.2086 | 0.415 |
| M7:iface2 | 0.8805 ± 0.0008 | 0.2100 | 0.407 |
| M7:face | 0.8796 ± 0.0009 | 0.2108 | 0.402 |
| M7:adaptive (training-only tile selection, D = 458) | **0.9308 ± 0.0004** | **0.1598** | **0.657** |
| M6 + λ_min K(E) at 3 energies (V-D exact-reformulation control) | 0.9711 ± 0.0016 | 0.1032 | 0.857 |
| M7:interface (reference, D = 56 %) | 0.9993 ± 0.0000 | 0.0166 | 0.996 |

- *child(16) beats V-D's best target-free model.* M7:child exceeds M4 and M2 by more than 2 sd: 0.9253 > 0.9216. It does so with one compressed variable instead of 15 descriptors.
- *C4 still fails.* C4 also requires a calibrated parameter-free RMSE below 0.1747, and child(16) has 0.197.
- *The other a-priori families do worse than the previous-level edge (M2).* M7:adaptive (CV-R² 0.931) is the best compressed predictor. It fails C2 (calibrated RMSE 0.176) and C5 (11/16 residual signs).

### 4.2 Interventions

The 18 V-D controls were never trained on. "Raw direction" is the sign of E_W(control) − E_W(FR30) against Y4(control) − Y4(FR30); every true difference is ≤ −0.31. "Residual sign" is the sign of the M7-predicted flux residual against the actual one, for the 16 controls with |actual| ≥ 0.05.

| model | raw direction | residual sign | corr(predicted, actual residual) | mean \|error\| |
|---|---|---|---|---|
| M7:child | **17/17** | 13/16 | **0.838** | 0.134 |
| M7:fec | 14/17 | 13/16 | 0.615 | 0.190 |
| M7:patch2 | 14/17 | 13/16 | 0.555 | 0.201 |
| M7:face | 14/17 | 13/16 | 0.539 | 0.206 |
| M7:iface2 | 14/17 | 12/16 | 0.520 | 0.213 |
| M7:adaptive | 17/17 | 11/16 | 0.753 | 0.168 |
| (V-D M4, for comparison) | — | — | 0.55 | 0.27 |
| M7:interface (reference) | 17/17 | 16/16 | 0.999 | 0.013 |

**Where child(16) fails.** Its three residual-sign errors are `fine1`, `fine2` and `fine3`.

| control | actual residual | predicted residual | ΔY4 vs FR30 | ΔE_W vs FR30 |
|---|---|---|---|---|
| fine1 | −0.139 | +0.117 | −0.624 | −0.256 |
| fine2 | −0.157 | +0.106 | −0.639 | −0.268 |
| fine3 | −0.229 | +0.098 | −0.695 | −0.262 |

- *What these controls are.* They keep FR30's rule at the last inflation step, the finest scale, and randomise every coarser step.
- *What the compression sees.* It recovers only about 40 % of the edge drop that the coarse randomisation causes. It sees the fine-scale structure and misses the coarse arrangement.
- *The opposite controls are fine.* Every control that keeps the coarse FR30 arrangement and randomises the finest scale (`coarse1–3`) has the correct sign and a small error.

### 4.3 FR30

- *Leave-FR30-out explained fraction of its flux residual (+0.773).* M7:child 0.646, M7:adaptive 0.564, M7:iface2 0.519, M7:fec 0.477, M7:patch2 0.427, M7:face 0.422. For comparison: V-D M4 0.416, M2 0.543, M6 0.900, `interface` 0.980.
- *FR30's calibrated parameter-free error* for child(16) is −0.045. That is within C6's 0.10, so child(16) passes C6. It is the only family that does.
- *FR30 is not anomalous for the compression.* Its child(16) error lies at the 44th percentile, so the compression is no worse for FR30 than for a typical rule. For the face-type families FR30's error is at the 6th–16th percentile: these bases do *relatively better* on FR30 than on typical rules, yet still explain less than half of its residual.

## 5. What distinguishes FR30 (Section V of the brief)

The successful-candidate questions of the brief assume that a compressed state passed. None did, so the answers below come from the exact solution, through gauge-invariant decompositions, and from the best (failed) compression. They are labelled accordingly.

- **Which quantities distinguish FR30?** [E, X: exploratory energy budget]
  - *The decomposition.* E₀ = 24 + Σ_bonds Re⟨ψ_a, −C_ab ψ_b⟩ is exact and gauge-invariant. It splits into seam bonds (between depth-1 children) and intra-child bonds. Define the bond efficiency η = −(bond energy)/(2Σ|ψ_a||ψ_b|): η = 1 means no frustration of the hopping.
  - *FR30 is the most frustrated rule.* Its ground pair has the **lowest** efficiencies among the 264 classes in both categories: seam η = 0.713 and intra η = 0.689, both at the 1st percentile.
  - *Correlations with Y4.* Across rules, corr(η_intra, Y4) = −0.76 and corr(η_seam, Y4) = −0.33.
  - *Depth-resolved split of the flux residual* [X] (`phase5e_results.json` → `depth_budget_exploratory`).
    - *Method.* Group every panel by the depth d of its two tiles' lowest common ancestor: d = 0 for the top seams between depth-1 children, d = 3 for siblings inside a level-1 supertile. Then E₀ = 24 + Σ_d B_d exactly. Regress each B_d on the same flux variables. The residuals add up to the residual of Y4 (checked to 9×10⁻¹⁴).
    - *FR30.* Its residual is +0.767 = **+0.900 (d = 0) + 0.572 (d = 1) + 0.392 (d = 2)** − 1.097 (d = 3). Its bond efficiencies at d = 0, 1, 2 are the lowest of all 264 classes (percentiles 1, 1, 0); at d = 3 it sits at the 22nd percentile.
    - *Across rules.* The top seams carry most of the residual variance: shares d0 +0.90, d1 −0.31, d2 −0.02, d3 +0.43.
    - *Controls.* The `fine` controls keep FR30's finest step. They reverse the sign of the coarse-seam contributions (d0 −0.57 to −0.94) and gain at d = 2. `dec2238`, the control rule with the second-largest residual (+0.45), gets it from d = 0 (+1.20) as well.
    - *Reading.* FR30's excess sits in the frustration of its coarse seams. It is partly compensated at the finest bonds.
- **Why do other rules beat FR30 on the raw edge?** [E]
  - *More flux.* The five rules with higher Y4 (1387, 3693, 1391 = the class of 3697/4757, 1144 and 3718; Y4 = 9.08–9.52) have higher traceless flux: f_trl = 0.431–0.456, against FR30's 0.401. Their flux-predicted edges are accordingly higher, 8.66–8.93 against 8.15.
  - *Smaller residuals.* Their residuals are +0.24 to +0.69. FR30's is +0.767, the largest of all 264 classes.
  - *The excess is frustration per bond, not more flux.* FR30 converts less flux into edge than they do and more frustration per bond (above).
- **Why does FR30 keep a large residual after flux correction?**
  - *The residual lives on the seams.* Dropping everything except the interface tiles reproduces 98 % of it, and the outer boundary contributes nothing.
  - *It needs the coarse arrangement.* The child(16) compression explains 65 % of it and fails on precisely the controls that destroy the coarse arrangement (§4.2).
  - *Bounded-radius statistics cannot see it.* The residual is a property of how the coarse arrangement of children frustrates the seam states. A depth-resolved decomposition (above) locates it across depths, so the scale at which the frustration sits is measured, not assumed.
- **Why do local structural predictors fail?** The relevant object is the seam ground state. Its effective dimension grows with the seam area (§6.3), and it responds to arrangement at coarse depths. V-B's 30 bounded-radius predictors (M1) explain 41 % of the residual variance; the depth decomposition shows how much sits beyond their radius.
- **Does the effective state predict interventions blind?**
  - *Directions, yes.* child(16)'s compressed root gets all 17 raw intervention directions right with no training on controls.
  - *Residuals, partly.* It gets 13 of 16 residual signs. The 3 failures are diagnostic (§4.2).
- **Gauge and symmetry invariance.**
  - *Every quantity used is gauge-invariant (E2).* This includes E_W, c, η and the tile densities. The measured gauge deviation is ≤ 10⁻¹².
  - *Symmetry-equivalent representations.* The 3 members of FR30's class {1386, 3690, 4752} have identical bottoms by the V-D class key. The V-D class key is empirical. Only one representative per class was computed, so equality of E_W within a class is **not** verified here.
- **Aperiodic hierarchy versus simpler explanations.**
  - *Contact degree, graph topology and boundary geometry are excluded.* By E0 they are identical across all rules and controls.
  - *Local flux density:* the M0 residual is by construction flux-corrected.
  - *Finite size:* the residual is defined at a fixed level, and the compression results are stable from level 3 to 4 (§3.4).
  - *The interventions separate hierarchy from local statistics.* `shuffle` keeps FR30's local rotation multiset but has residuals −0.18 to −0.59. `iid` destroys self-similarity (−0.20 to −0.29). `flip` at 5 % keeps most of the excess (+0.16 to +0.21), and at 20 % loses it.
  - *Not matched:* periodic approximants of the same chair geometry at level 4 are not in the control set. V-A's periodic controls use a different geometry. This confound is not removed here.

## 6. The three mechanisms

### 6.1 H1: interface-localized renormalization

**The operator is local; the state is not.**

- **Locality of the child response [E].** `audit/results/phase5e_locality.json` covers level 4: four rules, all 8 children, and all 304 pairs of face/hinge/corner groups per rule.
  - The blocks R_c(E_REF)[A, B] between different groups are small. Their norm relative to √(‖R_AA‖‖R_BB‖) has a median of 0.014–0.019 and a maximum of 0.27, the maximum occurring for adjacent groups.
  - They are not low-rank. At relative tolerance 10⁻³, their numerical rank is two thirds of the smaller block dimension (median).
- **Face-localized states fail [E].** One-sided face modes, two-sided seam modes and face+hinge+corner modes all keep large edge errors at D ≤ 10 % (§3). Their median capture of the boundary ground pair stays at 0.57–0.76 at D ≈ 512, against 0.83 for child(32).
- **Why.** The ground pair is supported on the seams: S holds 64–90 % of the weight, and the outer boundary < 1.5 %. *Along* the seams it is not smooth in the covariant sense. Hinges and corners alone carry 7–40 % of the S-weight, and 99.9 % of it needs 370–1383 tiles.
- **Verdict.** H1 survives as a statement about the *operator*: the child response is nearly block-diagonal over faces. It fails as a statement about *state variables*.

### 6.2 H2: hierarchical renormalization

Figure: `deliverables/figures/phase5e_closure.{png,pdf}`. Panel (a) is within-level capture, (b) the transfers between levels, (c) the edge error with the universal state.

1. **Fixed-D level sweep (frozen) [E].** At fixed family parameter, so at fixed D, the relative error stays bounded from level 3 to 4 for child, face, iface2 and fec. Level 5 did not finish (§3.4). Bounded is not small: about 10 % relative error at level 4.
2. **Pre-registered closure test [E] — fails.**
   - *Setup.* FR30, the level-3 supertile surface (574 dimensions), with snapshots from every copy of T₃ in the ground pairs at levels 4, 5 and 6.
   - *Within a level the snapshots are strongly compressible.* 99 % of the weight lies in d = 10, 25 and 20 dimensions at levels 4, 5 and 6, and 99.9 % in 12, 38 and 41.
   - *Across levels they do not transfer at the pre-registered size.* Training on levels 4–5 captures 86.0 % of level 6 at d = 57, against the 99 % mark, and 95.2 % at d = 114.
3. **Saturation at level 7 [E, X] (`phase5e_closure.json`; level-7 vector from the pass-19 checkpoint, §7).** The T₃ surface restrictions at levels 4, 5, 6 and 7 come from 8, 64, 512 and 4096 copies.
   - *The union of their spans saturates.* The cumulative dimension for 99 / 99.9 % is 10 / 12 (level 4), 28 / 43 (levels 4–5), 34 / 55 (levels 4–6) and **34 / 56 (levels 4–7)**.
   - *Within level 7 alone,* 16 / 34 dimensions hold 99 / 99.9 %.
   - *Exploratory transfers onto level 7.* Training on level 6 captures 99.87 % of level 7 at d = 57 and 99.990 % at d = 114. Training on levels 4–6 captures 99.81 % at d = 57; on levels 5–6, 99.85 %.
   - *The nested growth observed at levels 4–6 stops.* The local state space of a T₃ copy is effectively **≈ 34–56-dimensional out of 574** once the system is deep enough.
   - *The pre-registered transfer still fails at level 7 too.* Training on levels 4–5 captures 86.3 %.
4. **The universal state predicts a held-out level [E, X] (`phase5e_closure_level5.json`).**
   - *Setup.* E1 holds for any partition with block-diagonal interior. Level 5 is split into its 64 depth-2 copies of T₃ (dim S′ = 36736). Every copy gets the same d-dimensional subspace, trained on the ground pairs of levels 6 and 7 only.
   - *Result.* E_W − E₅ = +0.084 at d = 34 (D/dim S′ = 5.9 %), **+0.045 at d = 42 (7.3 %)** and **+0.019 at d = 58 (10.1 %)**.
   - *What that means.* A compact, gauge-covariant (E2: a fixed subspace in the copies' common substitution frame), training-free-at-the-target state meets C2's accuracy at C1's compression, for an unseen level.
   - *Other training sets:* `phase5e_closure_level5.json` lists every row (levels 6, 7, 4, 4+6+7, and level 5 itself as the in-level reference).
   - *The same subspace fails at level 4.* Used as the 8 children there: 0.45 at d = 58 and 0.053 at d = 114. Trained on level 5: 0.14 at d = 58 and 0.037 at d = 114. (Training on level 4 itself is tautological: its 16 snapshots *are* the answer, error 10⁻¹³.)
   - *Why level 4 fails.* At level 4 every copy touches the pinned outer wall. At levels ≥ 5 most copies are interior. The compact state space describes *bulk* copies. The boundary copies need extra states, and their share vanishes as 1 − (fraction of copies touching the outer surface) → 1.
   - *Scope.* FR30 only. One target level. Post-freeze. The level-7 training vector is not converged to 10⁻⁷ (§7).
5. **E5 bound.** Any d-dimensional universal subspace leaves uncaptured weight ≥ τ_d of each level's snapshot matrix. Here τ_57 ≤ 2×10⁻⁴ at every level. The bound therefore does **not** exclude a ≈ 57-dimensional universal state, and items 3–4 suggest one exists asymptotically. What fails at levels ≤ 5 is the *transfer from shallow to deep levels*, which E5 does not address.

### 6.3 H3: broadly distributed response

- **Crowding follows an area law [E] (`phase5e_cluster.json`).** The number of eigenvalues of the supertile surface response R_m(E_REF) within w of its bottom:

  | m | surface tiles | FR30, w = 1 / 2 / 4 | 3697 | 1387 | 2238 (w = 2) |
  |---|---|---|---|---|---|
  | 1 | 8 | 2 / 2 / 2 | 2 | 2 | 2 |
  | 2 | 53 | 6 / 12 / 16 | 10 | 10 | 8 |
  | 3 | 287 | 34 / 64 / 98 | 54 | 66 | 54 |
  | 4 | 1331 | 158 / 290 / 472 | 252 | 304 | 248 |

  - *Growth matches the surface.* From m = 3 to 4 the count within w = 2 grows ×4.5 (FR30), ×4.7 (3697), ×4.6 (1387) and ×4.6 (2238), while the surface grows ×4.64.
  - *Constant density.* About 0.12 eigenvalues per surface tile lie within w = 1 and about 0.2 within w = 2, for every rule.
- **Mechanism (heuristic, not a theorem).** The inter-child coupling has norm O(1) on every seam tile. A Feshbach reduction onto the child modes below a cut w is controlled only if w exceeds the coupling scale. The number of child modes that must be kept is therefore N_m(w = O(1)) ∝ |surface|, which grows like 4^m.
- **Consistent with the support.** The tile support of ψ_S grows (§3.5), the capture curves are flat (§3.2), and the theorem checks hold.
- **Verdict.** H3 holds for every *a-priori* compression: the low spectrum of the *child response* crowds by an area law. The *environment-selected* local states of §6.2 do not crowd: they saturate at ≈ 34–56 per copy. The obstruction is therefore to building the RG state from the child's own spectrum, not to the existence of a compact state.

## 7. Scale law (Section VI of the brief)

### 7.1 What the substitution structure motivates

- **Rate needs extra input.** The edge is monotone (E6) and bounded below (certified 4.008). A rate requires more.
- **Dirichlet-type ansatz.** If the low-energy physics were a continuum band edge with quadratic dispersion, the pinned wall would give E_m − E_∞ ∝ L_m⁻², with L_m = 2^{m+1}, i.e. a decrement ratio of 1/4. V-C's k = 4 dispersion test motivates this ansatz.
- **Log-periodic corrections.** These are generic for substitution-invariant operators: discrete scale invariance gives a ratio r_m that oscillates around a mean. With five decrements they are unidentifiable.
- **Frozen beforehand.** Commit a781ad8 fixed the five models and the decision rule on r₇ before the level-7 solve converged (§0).

### 7.2 Level 7 [E]

Figure: `deliverables/figures/phase5e_fr30_scaling.{png,pdf}`.

**The run.**
- *Solver.* The existing V-B solver, run through the portable runner (validated at level 5 to 7×10⁻¹⁵).
- *Size.* Dimension 4 194 304; 37.6 M non-zeros.
- *Progress.* 20 Chebyshev-filtered passes, 3413 block matvecs, about 6 h of wall time on a shared machine.
- *State at the reporting cut-off.* Pass 20 reached residual 9.3×10⁻⁸ on the lowest vector and 2–7×10⁻⁷ on the other three. The 10⁻⁷ criterion on all four was not yet met. Unless §0 says otherwise, the values below are the Rayleigh–Ritz values of the pass-19 checkpoint (`audit/phase5e_level7_extract.py`, `audit/results/phase5e_level7.json`, `"converged": false`).

| quantity | value |
|---|---|
| E₇ (Ritz value; an upper bound up to rounding) | **8.764911988** (residual 1.45×10⁻⁷) |
| lowest pairs | 8.7649120, 8.7649151, 8.7649166, 8.7649796 |
| d₇ = E₆ − E₇ | 0.0052216 |
| decrement ratio r₇ = d₇/d₆ | **0.1943** |
| frozen decision rule (a781ad8) | r₇ ≤ 0.20 → **"the decrement ratio keeps falling: no single power law describes levels 4..7"** |
| frozen envelope [8.7605, 8.7655] | E₇ inside |
| frozen predictions − E₇ | G3 −6.7×10⁻⁴; D2 (L⁻²) −1.50×10⁻³; D48 −1.03×10⁻³; PL −4.40×10⁻³; ratio-trend +6.2×10⁻⁴ |
| certified upper bound (exact integer Rayleigh quotient of the level-7 vector rounded at scale 2²⁴; `audit/results/phase5e_level7_certified.json`) | **λ_min(H₇) ≤ 2467103543526498/281474992168387 = 8.7649120248** |

**Reading of the frozen test.**
- *The ratios keep falling.* The decrement ratios are 0.328, 0.267, 0.219 and 0.194, so the effective exponent p_m = −log₂ r_m rises: 1.61, 1.90, 2.19, 2.36.
- *L⁻² is ruled out on these levels.* Every pure power law, the Dirichlet L⁻² included, under-predicts E₇.
- *The two closest frozen predictions bracket E₇.* The geometric three-point fit lies below it and the ratio-trend extrapolation above it. Both miss by < 7×10⁻⁴.
- *Refits including level 7 (not predictions).*
  - Geometric (5, 6, 7): E_∞ = 8.76365, p = 2.36.
  - Power law (levels 4–7): E_∞ = 8.76313, p = 2.21, rms 1.8×10⁻⁴.
  - With five decrements, log-periodic modulation and a crossover cannot be told apart.
- *Conditional limit (E7).* If r_m ≤ 0.1943 for all m ≥ 8, then 8.76365 ≤ E_∞ ≤ 8.76491.
- *Unconditional certified bracket [P + exact arithmetic].* By E6, E_∞ ≤ E₇. With V-B's certified lower bound, **4.008189 ≤ E_∞ ≤ 8.7649120248**. This improves V-B's upper bound 8.7701336 by 5.2×10⁻³ and is independent of convergence: it is the exact Rayleigh quotient of an explicit vector.

**Spectral clustering at level 7.**
- *The low pairs crowd.* The three lowest Kramers pairs lie within 4.6×10⁻⁶ of each other. The distance from the first to the second pair is 0.211 (L3), 0.029 (L4), 0.0020 (L5) and 3.1×10⁻⁶ (L7): it shrinks by far more than the factor 1/4 of a band edge.
- *The eigenvectors are not resolved.* With residuals of 10⁻⁷–10⁻⁶ against splittings of about 3×10⁻⁶, the angle bound residual/gap is up to about 0.3 rad. Individual low eigenvectors at level 7 are therefore **not** resolved, and the eigenstate statistics below inherit that uncertainty.
- *The eigenvalue is robust.* The cluster lies inside the Ritz block, so E₇ itself is not affected.


### 7.3 Eigenstates

- **Pinned ground pair [E] (stored V-A/V-B values, recomputed V-B).** IPR·n is 6.424, 9.146, 19.930 and 42.789 at levels 3–6. With IPR ∝ n^{−D₂/3}, the window values of D₂ are 2.49 (3→4), 1.88 (4→5) and 1.90 (5→6).
- **Level 7, with the caveat above.** IPR·n = 121.1, so D₂(6→7) = **1.50**. Against V-D's frozen eigenstate predictions:
  - D₂ in [1.80, 2.00]: **outside**. The value sits at V-D's own "toward localization" threshold, 1.5.
  - Depth-1 interface weight < 0.57: **0.507, holds**.
  - Enrichment > 10: **11.1, holds**.
  - Overlap with the level-6 state replicated in the centre child < 0.14: **0.0038, holds**.

  The near-degeneracy and the falling D₂ point *away* from the critical-state reading, toward several nearly degenerate, spatially separated low states. Given the 0.3-rad uncertainty, this is suggestive only.
- **Boundary condition [E] (V-B `phase5b_d_scaling.txt`, re-read here).** The same windows give:
  - Robin (t = 0.5) boundary: 1.23 (3→4) and 1.13 (4→5);
  - free boundary: ≈ 0.0 and 0.24, a surface-localized band;
  - trivial connection (no flux): 2.65 and 2.82, extended.

  The value D₂ ≈ 1.9 is therefore specific to the pinned wall. It does **not** survive a change of boundary condition at these sizes. A boundary- or finite-size origin of the apparent criticality is not excluded. No infinite-volume phase is inferred.
- **Support across levels and defects [E].** §3.5 gives the tile support of ψ_S and the outer-boundary weight per level for the 8 sweep systems. Level-4 IPR·n for FR30 and the flip controls is in `phase5e_L4_shard*.jsonl` (`support.ipr_n`).

## 8. Deviations, failed attempts and numerical limitations

**Before the freeze (development set only).**
1. *Root finder.*
   - Plain Newton from E_REF stepped into the pole at λ_II and took about 35 iterations.
   - A first bracketed variant stalled next to the pole and returned the bracket midpoint (7.968 for several bases of rule 950). This was a bug, caught because identical values appeared for different bases.
   - The final solver alternates Newton from the left with chords and bisects whenever a step leaves the bracket. It was validated against bisection to 10⁻⁹ (test).
2. *Ground state.* Shift-invert targeted near λ_II returned an eigenvalue that was not the lowest. It now targets 0, which is valid because H ≥ 0.
3. *Kramers partner.* ARPACK sometimes returns one copy of a doublet. The partner is now built as Tψ.
4. *Grid.* `face(32)` was removed (D = 2016, 140 s per system). The two-sided seam family `iface2` was added. Both changes were made on development rules only.

**After the freeze (compute-only; no evaluation result had been seen).**
5. *Level-4 grid capped at D ≲ 600.* The configurations child(64), face(16), fec(8, 16), patch2(8), patch3(2) and iface2(32) were dropped for the 282 evaluation systems at level 4. The full grid is kept for the development rules, for level 3 and for the level sweep.
   - *Reason.* The first launch ran at about 15 minutes per system under contention. It was stopped before any level-4 evaluation system had completed (0 records).
   - *What else changed.* The pole term was also restricted to each child's active columns. The results are identical; the cost per system fell from about 400 s to about 51 s.
   - *What it does not affect.* No primary configuration (§4 of the protocol) and no criterion depends on the dropped members, since all of them have D > 459.
6. *Level 5 of the level sweep.* The ground state uses LOBPCG (tolerance 10⁻⁹) instead of shift-invert, to avoid a sparse LU of dimension 65536. `iface2` blocks are formed without building the full K(E_REF) (7 GB at level 5). The `interface` reference is omitted at level 5, as the protocol states.

**After the level-4 stage (exploratory additions and incidents; nothing here changes a frozen definition or criterion).**
7. *Adaptive stage.*
   - The first launch failed on a name-type bug: rule names were read back as numeric strings. It was fixed and relaunched; no results were lost.
   - The relaunch was itself stopped once more to restrict the non-admissible `oracle` to the primary size m = 229, to save time. The frozen `adaptive` grid is complete.
8. *Level sweep at level 5.* The four development systems were stopped for memory (eight concurrent level-5 lanes exceeded RAM). The four reference systems were stopped after 2.5 h at level 5. C7 is therefore decided by its part (b) (§3.4).
9. *Closure (H2).* The pre-registered test is train 4–5 → test 6. Everything else in §6.2 is **exploratory**:
   - the transfers involving levels 6 and 7, and the cumulative-dimension check;
   - the level-4 edges with the universal subspace;
   - the level-5 multi-copy edge test.

   That last test required generalizing `System` to deeper partitions (copies of T_{L−d}) and keeping block-diagonal P sparse. Both changes are validated by the unchanged test suite (12 core tests re-run).
10. *Level 7.*
   - **Not converged** to the 10⁻⁷ criterion on all four vectors by the reporting cut-off. Values come from the pass-19 checkpoint (`audit/phase5e_level7_extract.py`). The solver kept running; a converged run would overwrite `phase5e_level7.json`.
   - The exact certificate is computed from the extracted vector, so it is valid regardless of convergence.
   - V-B's `certify()` writes a `phase5b_d_…` file name. That new, untracked file was renamed `phase5e_level7_certified.json`, and the runner now refuses to overwrite any existing V-B certificate.
11. *Crowding diagnostic.* The first run was stopped for memory after FR30 m = 1–4. It was re-run in full later; that run is the source of `phase5e_cluster.json`.

**Numerical limitations.**
- *Precision.* The Newton/chord tolerance is 10⁻¹²; eigensolver accuracy is about 10⁻¹³‖M‖; stored Y4 residuals are ≤ 10⁻⁷, so the eigenvalue error is ≤ 10⁻¹⁰. All of these are negligible next to the effects measured (≥ 10⁻²).
- *Window.* An E_W with no root below λ_II is recorded as "no admissible edge" and set to λ_II for regressions (E3 convention).
- *Level-7 tolerance.* Level 7 converges slowly because its second Kramers pair lies only a few 10⁻⁶ above the first. The eigenvalue is reported with its residual, and the Ritz value is an upper bound.
- *Platform.* Everything ran on Windows. The `resource` module is replaced by a stub, so the V-B solver's RSS column reads 0 except in the level-7 runner, which uses psutil.

## 9. Conclusions, by status

### Proved [P]

- **E0.** One panel multigraph for all decorations; decorations differ only in the Q8 connection.
- **E1.** The exact Schur reduction characterises the spectrum through inertia on all of ℝ \ spec H_II.
  - Roots ↔ eigenvalues, with multiplicity.
  - Kernel isomorphism.
  - Pole crossings.
  - Strict location of the edge below λ_II.
  - Loewner monotonicity and concavity.
- **E2.** The exact gauge classes of boundary quantities, and the criterion for gauge-invariant compression: a covariant subspace with complete Kramers multiplets.
- **E3–E4.** The edge error of every gauge-covariant, Kramers-complete compression is pinned between μ₂(1 − c)/|g′| and μ_max(1 − c)/c. This makes the uncaptured boundary weight the exact currency of compression.
- **E5.** An Eckart–Young lower bound for universal subspaces.
- **E6–E7.** The monotone edge, and the conditional rate.
- **Certified bracket.** E6 plus the exact integer Rayleigh quotient of the level-7 vector, with V-B's certified lower bound, give 4.008189 ≤ E_∞ ≤ 8.7649120248. The upper end is new.
- **Lean.** Four finite algebraic facts, kernel-checked.

### Computational observations [E]

1. **No a-priori compression meets the bar.** The families are child modes, one- and two-sided face modes, face/hinge/corner and depth-2/3 patches. At ≤ 10 % of the boundary dimension, none reaches calibrated RMSE ≤ 0.05; the best is 0.17–0.20. Training-only tile selection reaches 0.176 at the cap. Even the target-ranked oracle reaches only 0.140.
2. **The best compression is a real but insufficient predictor.** child(16) beats V-D's target-free descriptors out of sample, gets every intervention direction right, and explains 65 % of FR30's residual. It fails on accuracy and on the three `fine` controls.
3. **Only removing the pinned outer boundary is accurate.** Interface tiles reproduce the edge to 0.035 RMS and FR30's residual to 98 %. FR30's excess is a seam phenomenon.
4. **The obstruction has an area law.** Low-spectrum crowding of the supertile response is ∝ surface. The support of the boundary ground pair tracks the interface area. Capture curves are flat in D.
5. **An environment-selected local state saturates and predicts a held-out level [X].** The T₃-copy local state space is about 34 / 56-dimensional (99 / 99.9 %) and is unchanged from levels 4–6 to 4–7. Trained on levels 6–7, it predicts E₅ to 0.019 at 10 % of the boundary dimension. It fails at level 4, where every copy is boundary-dominated. The pre-registered shallow-to-deep closure test fails.
6. **Scale.** E₇ = 8.7649120, r₇ = 0.194. By the frozen rule no single power law describes levels 4–7. The effective exponent rises 1.6 → 2.4. Conditionally, E_∞ ∈ [8.76365, 8.76491]. The three lowest pairs at level 7 lie within 5×10⁻⁶.
7. **Apparent criticality depends on the boundary condition.** D₂ ≈ 1.9 for the pinned wall, but ≈ 1.1–1.2 with Robin walls at the same sizes.

### Conjectures [C]

- **Revised conjecture (area-law boundary response).** For FR30/Chair44, consider the number of degrees of freedom any gauge-covariant linear compression of the level-m boundary response needs to predict E_m to fixed accuracy ε. That number grows like the interface area, ∝ 4^m. Equivalently, N_m(w) := #{eigenvalues of R_m(E) within w of its bottom} = ρ(w)·|surf_m|(1 + o(1)), and a Feshbach-controlled closure needs w ≳ ‖V‖ = O(1).
  - *Status.* Supported at m ≤ 4 (crowding) and m ≤ 5 (support).
  - *What would refute it.* A saturating snapshot dimension at levels ≥ 7.
- **Local-state conjecture (the surviving form of H2).** The T₃-copy snapshot subspaces of the level-L ground state are nested and converge as L → ∞ to a fixed subspace U_∞ of dimension d_∞ ≪ 574. If true, an RG with a fixed per-copy state space exists asymptotically, but its dimension is set by the environment, not by the child's low spectrum.
  - *Status.* Saturation at d ≈ 34–56 holds through level 7. The held-out-level prediction at level 5 meets 0.05 at 7.3 % compression. FR30 only; level-7 vector not fully converged.
- **The FR30 anomaly is a coarse-arrangement frustration of the seam states.**
  - *Evidence.* FR30 has the lowest bond efficiencies of all 264 classes. The compression fails exactly when the coarse arrangement is randomised. The interface-only model is exact.
  - *Status.* Not a proved mechanism. It is a localisation of the effect with a falsifiable consequence: any descriptor blind to depth-1/depth-2 arrangement must fail on `fine1–3`.

### What is not claimed

- No infinite-volume phase.
- No emergent continuum theory.
- No statement about physics beyond this operator.

The negative result concerns the tested families and universal linear subspaces at the tested levels. It does not exclude nonlinear or energy-dependent closures.

### The single most informative next experiment

**Measure the crowding law and the local-state saturation at levels 5–7, without diagonalising R_m.**
- *Crowding by inertia.* By E1 applied with a surface shift, n₋(R_m(E) − w) = n₋(H − E − wΠ_S) − n₋(H_II − E). The crowding count N_m(w) is therefore obtainable from sparse LDLᵀ inertia of matrices of the original sparsity at m = 5, 6, 7.
- *Saturation.* The level-7 ground pair (this phase) gives the T₃ snapshot dimension at a fourth level.
- *Decision.* N_m(1)/|surf_m| constant through m = 7 together with a non-saturating snapshot dimension refutes any finite-dimensional linear RG for this edge. A saturating snapshot dimension with a bounded crowding density supports the local-state conjecture.

## 10. Reproduction

**Environment.**
- *Hardware.* Windows 11 Home 10.0.26200, 24 cores, 32 GB RAM.
- *Software.* Python 3.12.10, numpy 2.5.2, scipy 1.18.1, matplotlib, Lean 4.35.0 (core, no Mathlib).
- *Threads.* Every stage ran single-threaded per lane (`OMP_NUM_THREADS=OPENBLAS_NUM_THREADS=1`), except the level-7 solver (4 threads).

**Seeds.**
- V-D folds: `default_rng(20261024 + r)`.
- Development rules: 20261026.
- Gauge test: seed 11 (stage) and seeds 5 and 3 (tests).
- Level-7 solver: seed 7, as in V-B.

**Commands** (repository root; Windows `python`, `python3` elsewhere; the `resource` stub makes every script portable):

```
python -u -I audit/phase5e_scaling.py freeze                      # level-7 predictions (committed a781ad8 before convergence)
python -u -I audit/phase5e_level7_runner.py run 7 [--resume]      # existing V-B solver, portable wrapper; checkpoints in .ckpt_phase5e_level7/
python -u -I audit/phase5e_scaling.py evaluate                    # score the frozen predictions; eigenstate checks
python -u -I audit/phase5e_run.py level4 <shard> 16               # 286 level-4 systems (16 lanes; resumable)
python -u -I audit/phase5e_run.py level3 <shard> 2                # 264 classes at level 3
python -u -I audit/phase5e_run.py levels <system>                 # level sweep L = 2..5 (fr30 1387 3697 2238 950 1583 1787 3133)
python -u -I audit/phase5e_run.py adaptive <shard> 16             # training-only tile selection + depth-resolved budget (after level4)
python -u -I audit/phase5e_run.py gauge                           # random SU(2) gauge test, all families
python -u -I audit/phase5e_run.py closure                         # H2 closure test (FR30 levels 4-7)
python -u -I audit/phase5e_run.py closure_rule <system>           # per-rule closure diagnostic (exploratory)
python -u -I audit/phase5e_run.py cluster fr30 3697 1387 2238     # low-spectrum crowding of R_m (m = 1..4)
python -u -I audit/phase5e_run.py locality                        # face-to-face blocks of R_c (operator locality)
python -u -I audit/phase5e_analyze.py                             # frozen criteria -> audit/results/phase5e_results.{json,csv,txt}
python -u -I audit/phase5e_figures.py                             # deliverables/figures/phase5e_*.{png,pdf}
python -m unittest tests/test_phase5e.py                          # 15 tests
lean certificates/Phase5ESymmetry.lean                            # 4 kernel-checked finite identities
```

**Runtimes (shared machine).**
- *Level 4.* Launched 22:42. 282 evaluation systems were done by about 01:30 (16 lanes; 51 s per system alone, 5–6× longer under full load). The 4 development rules carry the full grid and finished at 02:30.
- *Level 3.* 264 classes in 2 h 10 min over 2 lanes.
- *Gauge.* 2 h 33 min, 1 lane.
- *Level sweep.* Levels 2–4 in 10–20 min per system. Level 5 was not completed (stopped after 2.5 h; §3.4).
- *Adaptive.* 282 systems in about 55 min over 16 lanes.
- *Level 7.* Started 21:49. Pass 19 (used here) at 03:31, pass 20 at 03:52; 4 threads, about 6 h. Extraction took 73 s and the exact certificate 39 s.
- *Peak memory.* About 4 GB per level-5 sweep lane, 3.9 GB for level 7, and 0.6–1.3 GB per level-4 lane.

**Logs.** Session scratchpad `p5e/*.log` and `level7.out`. The level-7 solver also logs to `audit/results/phase5e_level7.log`.

**Commits.**
- a781ad8: frozen level-7 predictions and runner.
- f7db7e9: frozen protocol and implementation.
- f180964: theory, tests, Lean and analysis code.
- the final commits of this branch: results, report and memo.

**Files.**
- *New code.* `audit/phase5e_{rg,run,analyze,figures,scaling,level7_runner}.py`.
- *Tests.* `tests/test_phase5e.py`.
- *Lean.* `certificates/Phase5ESymmetry.lean`.
- *Results.* `audit/results/phase5e_*`. The level-7 lowest-4 vector (268 MB) and the checkpoints are not committed; their location and checksum are in the level-7 JSON.
- *Previous reports, V-B/V-D code and frozen results.* Not modified.
