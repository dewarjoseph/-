# Phase V-E — a renormalization question for the FR30/Chair44 boundary response

Status tags: **[P]** proved here (the proof is in this file or in `PHASE5E_REPORT.md` §2); **[V]** proved in an earlier phase and re-checked; **[E]** numerical; **[C]** conjecture. This file was written before the evaluation runs. Only the conjecture's status line (§4) and the pointers to results are filled in afterwards; they are marked *(post-run)*.

## 1. The mathematical object

### 1.1 Geometry, decoration, connection

- **Tiles.** A level-m supertile T_m consists of 8^m chairs. A chair is 7 unit cubes: the 2×2×2 block minus one octant. Tile a has a pose (G_a, t_a) with G_a ∈ SO(3, ℤ), a signed permutation matrix of determinant 1. Poses come from iterating the eight child maps of a decoration (`independent_clifford_q8_audit.tiles_at_level`).
- **Decoration.** A decoration assigns a permutation to the centre child and to each of the 7 octant children, with parity (−1)^{|v|}. That gives 3^8 = 6561 decorations, and FR30 is one of them.
- **Panel multigraph.** Two tiles are joined by one edge per shared unit panel f. Each panel carries its normal axis n_f ∈ {e₁, e₂, e₃}. Multiplicities are allowed. Every tile has at most 24 panels, and exactly 24 in the bulk.
- **Proposition E0 [P] (the graph does not depend on the decoration).**
  - *Statement.* The three permutations of a given parity form a coset of the chair's stabilizer, the cyclic group C₃ of axis permutations about the body diagonal.
  - *Proof.* Changing a child's choice inside its coset right-multiplies its frame by an element of C₃. That element permutes the octant positions of the grandchildren by the same axis permutation, and it maps each sign matrix D_{s(v)} to D_{s(cv)}. By induction on depth, the set of cube sets {cubes(a)}, and hence the panel multigraph with its normals, is the same for every decoration. Only the frame field a ↦ M_a := G_a, and the labelling of tiles by index, depend on the decoration. ∎
  - *Check.* Tested in `tests/test_phase5e.py`. This is the precise sense in which the 6561 rules and all V-B controls share one geometry and differ only in their connection.
- **Clifford Q8 connection [V].** C_ab^{(f)} = (σ·M_aᵀn_f)(σ·M_bᵀn_f). Write u_a(n) := σ·M_aᵀn. It equals ±σ_{π_a(n)}, which is Hermitian and unitary, so C_ab^{(f)} = u_a(n_f) u_b(n_f)†. Along any one axis the connection is pure gauge. Curvature appears only around loops that use panels of different normals. Plaquette holonomies lie in Q8 and fall into the classes +1, −1 and traceless (±iσ_k). The flux fractions f_{−1} and f_trl are V-B's flux variables.

### 1.2 Hilbert space and operator

- **Definition.** ℋ = ℓ²(tiles) ⊗ ℂ². (Aψ)_a = Σ_{f=(a,b)} C_ab^{(f)} ψ_b, with C_ba = C_ab†. H := H_pin = 24·1 − A (diagonal 24 on every tile, including the boundary).
- **Properties [V].**
  - *Hermitian, spec H ⊂ [0, 48].* By the Schur test, ‖A‖ ≤ 24, because every tile has ≤ 24 unitary links.
  - *Pinned.* Boundary tiles keep diagonal 24 while having fewer than 24 neighbours. This is a Dirichlet-type wall.
- **Quaternionic structure [P].** Every 2×2 block of H is a real linear combination of 1, iσ₁, iσ₂, iσ₃, that is, a real quaternion. The antiunitary T = (1 ⊗ iσ_y)K satisfies T² = −1 and commutes with H. Hence every eigenvalue has even multiplicity (Kramers). Every Schur complement and every principal submatrix on a set of tiles inherits the structure.
- **Spectral quantity.** E_m := λ_min(H(T_m)), the pinned edge. Y3 and Y4 are E_3 and E_4 for each decoration.

### 1.3 Gauge transformations

- **Gauge group.** 𝒢 = ∏_tiles SU(2) acts by H ↦ GHG†, with G = ⊕_a U_a. Changes of Q8 frame are the subgroup U_a ∈ Q8. A global frame rotation acts the same way.
- **SU(2) preserves the structure.** Since SU(2) is the group of unit quaternions, U(iσ_y)Ū = iσ_y, so [T, G] = 0. The gauge action therefore preserves the quaternionic structure.

| class | objects |
|---|---|
| **invariant** | spec H; spec K(E) and spec R_c(E); spectra of their principal submatrices on any tile set; λ_II; Ritz values of K(E) on a *covariant* subspace (Thm E2); pair-summed tile densities p_a = Σ_{pair}\|ψ_a\|²; traces of Wilson loops (the Q8 holonomy classes); bond efficiencies \|⟨ψ_a, C_ab ψ_b⟩\| / (\|ψ_a\|\|ψ_b\|) and the bond energies Re⟨ψ_a, C_ab ψ_b⟩ |
| **covariant** | H, K(E), R_c(E), X(E) = (H_II − E)⁻¹H_IS; Kramers-complete eigenspaces; coordinate subspaces ℓ²(T) ⊗ ℂ² for tile sets T |
| **basis-dependent** | individual vectors inside a Kramers pair; matrix entries and spinor phases; any truncation that splits a degenerate eigenspace (V-D measured a 0.09 gauge deviation for such a truncation) |

### 1.4 Hierarchy, decoration and induced operator are three different things

1. The **substitution hierarchy** is the tree of depth-k subtrees. It is geometric and the same for all decorations (E0).
2. The **decoration** is the frame field, a Q8 connection on the fixed multigraph.
3. The **induced operator** is H.

- **Theorem D0 [V].** H(T_m) = ⊕_c H_pin(child c) − V, and for a substitution rule each block equals H_pin(T_{m−1}) in local tile order, because links depend only on M_aᵀn.
- **Scope.** For the controls (iid, coarse, fine, shuffle, flip) the children differ, so D0's "identical blocks" fails. The decomposition itself still holds.

### 1.5 Schur reduction (V-D), stated on its full domain

- **Partition.** S = surface tiles of the eight depth-1 children, I = interiors. H_II = ⊕_c H_{I_cI_c}, λ_II := λ_min H_II.
- **Definitions.**
  - R_c(E) = H_{S_cS_c} − E − H_{S_cI_c}(H_{I_cI_c} − E)⁻¹H_{I_cS_c}.
  - K(E) = ⊕_c R_c(E) + Off, where Off = −V_SS is the inter-child block.
- **Pole representation (used for all computations here).** Write H_{I_cI_c} = Q_c diag(l_cj) Q_c† and B_c = Q_c†H_{I_cS_c}. Then R_c(E) = H_{S_cS_c} − E − Σ_j b_cj b_cj† / (l_cj − E), where b_cj† is the j-th row of B_c. K(E) is a rational Hermitian function of E with poles only at spec H_II. Compressed models then cost O(d²·|I_c|) per energy.

**Theorem E1 [P] (spectral correspondence, poles, inertia, multiplicity).** For E ∉ spec H_II:

- (i) det(H − E) = det(H_II − E) · det K(E).
- (ii) In(H − E) = In(H_II − E) + In K(E) (Haynsworth). Hence N_H(E) = N_{H_II}(E) + n₋(K(E)), where N counts eigenvalues below E.
- (iii) ψ ↦ ψ_S is an isomorphism ker(H − E) → ker K(E). Its inverse is w ↦ (w, −(H_II − E)⁻¹H_IS w). Multiplicities, and with them Kramers pairs, correspond.
- (iv) On (−∞, λ_II), K′(E) = −1 − X†X ≤ −1 and K″(E) = −2H_SI(H_II − E)⁻³H_IS ≤ 0. So K(E′) ≤ K(E) − (E′ − E) for E < E′ in the Loewner order. Every ordered eigenvalue branch κ_j is strictly decreasing with slope ≤ −1, and κ₁ = λ_min K is concave.
- (v) If H_SI v ≠ 0 for some ground vector v of H_II, then λ_min(H) < λ_II. In that case λ_min(H) is the unique zero of κ₁ on (−∞, λ_II). Every eigenvalue of H below λ_II is a zero of some κ_j, with matching multiplicity.
- (vi) Across a pole l ∈ spec H_II, the branches attached to range(H_SI Π_l H_IS) run to −∞ as E ↑ l and return from +∞. N_{H_II} jumps by mult(l), so (ii) stays exact on every interval between poles. Eigenvectors of H at an energy E ∈ spec H_II with ψ_S = 0 are invisible to K.
- *Consequence.* The fixed-energy spectrum of K(E) is **not** the spectrum of H. Only its inertia and its zeros carry spectral information.

### 1.6 Compressions

- **Definition.** For a subspace W ⊂ ℂ^S with orthonormal basis P, let g_W(E) := λ_min(P†K(E)P), and let E_W be its root on (−∞, λ_II). E_W := λ_II if there is no root ("no admissible edge").
- **Theorem E3 [P] (edge error equals the Ritz defect).**
  - g_W ≥ κ₁ (Cauchy), and g_W is decreasing with slope ≤ −1 and concave.
  - Hence E_0 ≤ E_W and g_W(E_0) / |g_W′(E_W)| ≤ E_W − E_0 ≤ g_W(E_0).
  - Newton's method from either side of the root, inside a bracket, converges monotonically from the right.
- **Theorem E4 [P] (two-sided capture bound).** Assume W is T-invariant and the ground level of H is one Kramers pair. Define:
  - c := ‖P†ψ̂_S‖², the same for every unit ψ̂ in the ground pair's S-part;
  - μ₂ := the smallest positive eigenvalue of K(E_0);
  - μ_max := λ_max K(E_0) ≤ 48 − E_0.

  Then μ₂(1 − c) ≤ g_W(E_0) ≤ μ_max(1 − c)/c, and μ₂ ≥ min(λ₃(H), λ_II) − E_0, where λ₃(H) is the next distinct eigenvalue of H.
  - *Meaning.* The edge error of every gauge-covariant compression is bounded on both sides by the uncaptured boundary weight 1 − c. The scales are the boundary gap and the boundary bandwidth.
- **Theorem E5 [P] (Eckart–Young bound for universal subspaces).**
  - *Setup.* Use the same d-dimensional U ⊂ ℂ^{surf(T_k)} in every copy of T_k inside T_L. This is the partition of E1 at depth L − k.
  - *Statement.* 1 − c ≥ τ_d := Σ_{i>d} σ_i² / Σ_i σ_i², where σ_i are the singular values of the snapshot matrix of restrictions of the ground pair to all copies. By E4, g_W(E_0) ≥ μ₂ τ_d.
  - *Scope.* This rules out every universal compression of dimension d at that level, not only the families tested.
- **Theorem E6 [P] (monotone edge).**
  - *Statement.* For every substitution rule, E_{m+1} ≤ E_m. The inequality is strict when Vx ≠ 0 for a child ground vector x. Hence E_∞ = lim E_m exists.
  - *Certified bracket [V].* E_∞ ∈ [4.008189, 8.7701336].
- **Theorem E7 [P] (conditional rate).** If the decrement ratios satisfy r_m = d_m / d_{m−1} ≤ ρ < 1 for all m > m₀, then E_m − ρ d_m / (1 − ρ) ≤ E_∞ ≤ E_m.

## 2. The conjecture, as posed and as tested

**Conjecture GIASR (as posed) [C].** There are gauge-invariant effective states X_m, of dimension bounded independently of m (or at least o(dim S_m)), and a map X_{m+1} = 𝓡(X_m; θ_m), such that E_m = 𝓕(X_m) + ε_m with ε_m small, uniformly across levels and across held-out admissible decorations.

**Non-tautology condition.** X_m may not be K_m(E) or R_m(E) itself, nor any repackaging of the full problem. The kernel of K(E_0), a 2-dimensional subspace, compresses the answer perfectly but uses the answer. Admissible states must be defined *before* the parent is solved:

- (a) **child-local and context-free:** computed from a child's own response and geometry, without knowing how it is glued;
- (b) **geometric:** coordinate subspaces of tile sets fixed by geometry;
- (c) **trained:** chosen on training rules only and applied unchanged to held-out ones.

**Operational form tested here.** For each family 𝔉 of admissible covariant subspaces W_m with dim W_m = D (fixed across m at fixed family parameter, §3), test whether the compressed root E_{W_m} predicts E_m:

- with the accuracy required by the frozen criteria (`PHASE5E_PROTOCOL.md` C1–C8),
- out of sample,
- under interventions,
- and stably across levels.

By E3 and E4 this is the same question as whether W_m captures the boundary ground pair up to 1 − c ≲ ε / μ_max.

*Two different negative results.* "The proposed compressions failed" is a statement about the tested families. "Every compression of dimension d fails" needs a lower bound. E5 supplies one, for universal subspaces, through the snapshot spectrum.

## 3. Three mechanisms

The table gives each hypothesis's assumptions, its derived prediction, the experiment that separates it from the alternatives, the result that would count against it, and what a failure would and would not imply.

| | **H1 interface-localized renormalization** | **H2 hierarchical renormalization** | **H3 non-compressible / distributed response** |
|---|---|---|---|
| assumptions | the parent's low boundary mode lives on child–child seams and is smooth along each face at the scale of the face (the face's covariant low modes span it) | seams alone are insufficient, but face + hinge + corner + patch variables at a few scales close approximately; equivalently, one universal child subspace serves every context | the parent edge depends on a growing number of lattice-scale degrees of freedom on the seams (flux-frustrated texture), and the low spectrum of R_m clusters with a count that grows with the surface |
| derivation / prediction | if ψ_S restricted to face F lies in span{k lowest modes of R_c[F,F] or of the two-sided seam operator}, then c → 1 and, by E4, E_W → E_0 at D = 2k·#faces, fixed in m (the face count is level-independent) | at fixed D the error stays bounded or decreases with m; the snapshot singular values of the T₃ surface restrictions decay fast and a subspace trained at levels 4–5 transfers to level 6 | the uncaptured weight 1 − c at fixed D grows, or does not shrink, with m; the tile support of ψ_S (tiles for 99.9 %) grows like the interface area (∝ 4^m); τ_d stays large for d ≪ 2·\|surf\|; eigenvalue counts of R_m(E_REF) in fixed windows grow like 4^m |
| distinguishing experiment | face(k), iface2(k) vs child(k) at matched D; the level sweep at fixed k | fec, patch2, patch3 at matched D; the level sweep; the H2 closure test (train L4–5, test L6) | capture curves c(D) and E4 bounds; tile support vs m; snapshot SVD; R_m clustering counts |
| counts against | face bases at D ≤ 10 % with large error or low capture; error growing with m at fixed k | hierarchical bases no better than face bases; out-of-level transfer of the universal subspace failing | any admissible basis with D ≤ 10 % meeting C2; snapshot spectrum decaying fast |
| what failure allows one to infer | only that *these* face bases are wrong coordinates; locality of the *operator* (decay of R_c between faces) may still hold | only that the tested hierarchy fails; E5 extends this to *all* universal subspaces of the measured dimension | it would not rule out nonlinear or nonlocal compressions outside the covariant-subspace class |

## 4. Falsifiable predictions recorded before the runs

- **P1 (from V-D and the development rules).** No child-local low-mode family reaches calibrated RMSE ≤ 0.05 at D ≤ 459. If any does, H3 is refuted at level 4.
- **P2 (H3).** The tiles holding 99.9 % of ψ_S grow by a factor of about 3–4 per level from level 3 to level 5 (the interface area). A factor of about 1 would mean bounded support and would favour H1/H2.
- **P3 (geometry of the support).** The pinned outer boundary carries < 1 % of ψ_S at level 4, so dropping it (`interface`) costs < 0.05 in E_W.
- **P4 (scaling).** The level-7 edge E₇ lies in the frozen envelope [8.7605, 8.7655]. The decrement ratio r₇ decides between the L⁻² law and its alternatives (rules in a781ad8).

*(post-run)* **Outcome.** Full results are in `PHASE5E_REPORT.md`.

- **P1 holds.** No family meets C1–C8. The best, child(16), has calibrated RMSE 0.197 at D = 256. As a single feature it is still a better held-out predictor than V-D's descriptors.
- **P2 holds.** The 99.9 % support tracks the interface area, and the low-spectrum crowding of R_m follows an area law.
- **P3 holds.** The outer boundary carries < 1 % at level 4, and `interface` is accurate to 0.035 RMS.
- **H1.** It survives for the *operator* (R_c is nearly block-diagonal over faces). It fails for *states*.
- **H2.** The pre-registered closure test fails: 86 % < 99 %. The within-level snapshot subspaces are low-dimensional and nested (exploratory).
- **H3.** Supported for every a-priori compression.
- **P4.** See the report's §7.
- **Revised conjecture.** In the report's §9.

## 5. Theorem targets (status after the run in the report)

1. Gauge covariance and invariance classes: E2 [P].
2. Recursion correctness, including poles, inertia and multiplicity: E1 [P].
3. Approximation bounds for truncated interface spaces: E3, E4 [P].
4. Recursive closure of a finite variable set: tested numerically (H2 closure test). E5 gives the lower bound.
5. Spectral scaling: E6 [P] and E7 [P, conditional]. Level 7 tests the conditional hypothesis.
6. Non-compression: E5 with measured τ_d [P + E]. It rules out universal subspaces of dimension d at the tested levels, and nothing beyond that.
