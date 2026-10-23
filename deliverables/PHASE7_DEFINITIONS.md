# Phase VII — canonical definitions

Every number in `PHASE7_REPORT.md` refers to one of the objects below, with the code that implements it. Two computations are compared only if they use the same definitions.

## 1. Geometry: the Chair44 complex and its substitution

### Cubes and chairs
- Unit cubes are indexed by q ∈ ℤ³; cube q is q + [0,1]³.
- The base chair is the set of cubes u ∈ U3 = {0,1}³ \ {(1,1,1)}, i.e. a 2×2×2 block missing the (+,+,+) corner.
- Its centroid is (13/14)(1,1,1). The largest distance from the centroid to a point of the chair is r_c = √619/14 ≈ 1.77712.

### Tiles (poses)
- A tile is a pose (G, T): G is a signed permutation matrix (the *frame*) and T ∈ ℤ³.
- Its cubes are (G(2u+1) + 2T − 1)/2 for u ∈ U3 (`phase7_local.cubes_of_poses`, `independent_clifford_q8_audit.tiles_at_level`).
- The missing corner points in direction G(1,1,1).
- The tile's centroid is x = T + (13/14)·G(1,1,1).

### Substitution σ
- A decoration d assigns a permutation π_v to each of the 7 octants v ∈ U3, and π_0 to the centre.
- **Children of the tile (G, T):**
  - the centre child, pose (G·P(π_0), 2T + G(1,1,1));
  - one child per octant v, pose (G·D_{s(v)}P(π_v), 2T + 4G·v), where s(v) = 1 − 2v and D_s = diag(s).
- Code: `phase7_local.make_ops`, `gen_poses`.
- The children tile the doubled parent exactly (`check_tiling`).
- **FR30** is the decoration `independent_clifford_q8_audit.FR30`. The **reflection-only (Z₂) substitution** has π ≡ id (`phase7_abelian_check.REFLECTION_ONLY`).
- **The geometry does not depend on the decoration.** The set of chairs in σᴸ(tile) is identical for all decorations (asserted in `phase7b_controls.py`); only the frames, and with them the tile labels, differ.
- **Supertile T_L.** The level-L supertile is σᴸ(identity tile at 0): 8ᴸ tiles inside [0, 2^{L+1})³.

### Tilings and hull
- A *tiling* Y is a set of tiles with disjoint cube sets covering ℤ³.
- A finite patch is *legal* if it occurs, up to translation and a global proper rotation, in some σᵏ(t).
- **Hull Ω_FR30.** The tilings all of whose finite patches are legal.
- **Primitivity.** The 24×24 frame-substitution matrix M satisfies M² > 0 (`phase7b_local_rules.py`, check P). So Ω_FR30 is minimal: every legal patch occurs in every Y ∈ Ω_FR30.

## 2. Stars and the legality predicate

- **R-star of a tile t.** The tiles owning a cube at Chebyshev distance ≤ R from a cube of t. The offsets are `phase7_local.Lr(R)`: [−R, R+1]³ minus the cube (R+1, R+1, R+1), in t's frame.
- **Type of a star.** The set of relative poses {(G_tᵀG_b, G_tᵀ(T_b − T_t))} of its tiles, encoded by `phase7_local.encode`.
  - The type is invariant under global translations and global rotations of the tiling.
  - The centre tile appears with relative pose (I, 0).
- **V_R.** The set of types of R-stars of tiles of hull elements. A tiling Y is **R-legal** iff every R-star type of Y lies in V_R.
- **𝒯_R.** The set of R-legal tilings with proper frames.
- **Construction and validation of V_R.**
  - V₁ is the forward Φ-orbit of one legal 1-star.
  - V₂ = Φ₂(V₁), V₃ = Φ₃(V₂), V₄ = Φ₄(V₂), where Φ_r maps a parent star to the r-stars of its 8 children computed inside the inflated parent star (`phase7_local.Phi_r`).
  - Every application asserts that the child's r-star is complete inside σ(parent's ⌈r/2⌉-star). This is the closure lemma, verified instance by instance.
- **Completeness of V₁.** The proof is in the report, §6.1.

## 3. Frames, compatibility, links

### Compatible frames
- A frame M for a tile whose geometric parent has frame G_p and which sits at octant v is **geometry-compatible** iff G_pᵀM ∈ D_{s(v)}·S₃, with all 6 permutation matrices allowed.
- For the centre child the condition is G_pᵀM ∈ S₃.
- The frame is **proper** iff det M = 1. At level 1 there are 3⁸ = 6561 proper and 6⁸ = 1 679 616 compatible choices in total.

### Pauli matrices and Q₈
- Pauli matrices σ₁, σ₂, σ₃.
- Q₈ = {±1, ±q₁, ±q₂, ±q₃} with q_k = −iσ_k, so q₁q₂ = q₃ and q_k² = −1.
- Table index 2u + s: u ∈ {0: 1, 1: q₁, 2: q₂, 3: q₃}, sign bit s (`phase7_adversarial.MAT`, `MUL`, `INVQ`).

### Link
For tiles a, b sharing a panel f with unit normal n_f (from a to b), the link is

  U_f(a→b) = (σ·M_aᵀn_f)(σ·M_bᵀn_f) ∈ Q₈.

- **Reverse crossing.** U_f(b→a) = U_f(a→b)⁻¹ = U_f(a→b)†, since (σ·u)² = 1. The formula does not depend on the sign of n_f.
- **Implementations.**
  - Pauli identity: `phase7_adversarial.link_q`.
  - Explicit 2×2 matrices: `independent_clifford_q8_audit.clifford_link`, `phase7_local.LINKGI`.
  - The implementations are asserted equal.

### Gauge transformations
- **Law.** For g: tiles → SU(2), set ψ_a ↦ g_aψ_a and U_f(a→b) ↦ g_a U_f(a→b) g_b⁻¹.
- **Effect on holonomy.** Holonomies W(γ) = Π U along a closed walk γ based at a are conjugated, W ↦ g_a W g_a⁻¹. Their classes — W = 1, W = −1, tr W = 0 — are gauge-invariant.
- **Gauge equivalence.**
  - Two connections are gauge-equivalent iff, for a fixed spanning tree and root, their tree-gauge forms (the non-tree links after gauge-fixing the tree links to 1) agree up to one global conjugation at the root.
  - Equal tree-gauge keys ⇒ gauge-equivalent. This is the only direction used.
- **Pure gauge.** The connection is pure gauge iff every holonomy is 1.

## 4. Curvature

- **Two-cycle.** A pair of tiles sharing panels with two different normals e_k, e_l. Its holonomy is W = U(a→b via k)·U(b→a via l), and m denotes the third axis.
- **Plaquette.** A lattice-edge plaquette is the 4-cycle of the four cubes around a lattice edge, crossed in cyclic order, whenever these cubes have at least two different owners. Crossings between cubes of the same tile contribute 1 (`phase5a_flux_vs_edge.plaquettes`, `phase7b_controls.plaquette_flux`).
- **Flux statistics.** f_m1 is the fraction of plaquettes with W = −1, and f_trl the fraction with tr W = 0 (the Phase V-B/V-D definition).

## 5. Operators

For a finite or infinite set of tiles 𝒫 ⊂ Y:

| object | definition |
|---|---|
| D_U | the covariant difference ℓ²(𝒫) ⊗ ℂ² → ℓ²(panels inside 𝒫) ⊗ ℂ², (D_Uψ)_f = ψ_a − U_f(a→b)ψ_b |
| free (Neumann) operator | H_U = D_U†D_U = Deg − A_U, with Deg_a = number of panels of a inside 𝒫 and (A_U)_{ab} = Σ_{panels a–b} U_f(a→b) |
| pinned operator | H_pin = 24 − A_U = H_U + diag(24 − Deg) |
| infinite-volume operator | on a tiling Y, Deg ≡ 24, so H_Y := 24 − A_U = H_U on ℓ²(Y) ⊗ ℂ². It is bounded (‖A_U‖ ≤ 24) and self-adjoint, with domain all of ℓ² |
| compression | for a finite patch K ⊂ Y, H_pin(K) is exactly the compression P_K H_Y P_K. Hence λ_min(H_pin(K)) ≥ inf σ(H_Y) (Rayleigh quotients of vectors supported in K) |
| gauge invariance | under the unitary 𝒢 = ⊕_a g_a, H ↦ 𝒢H𝒢†, so every spectrum and every λ_min above is gauge invariant (test `test_gauge_invariance_of_spectrum`) |

## 6. Spectral quantities

| symbol | definition | logical role |
|---|---|---|
| E(Y) | inf σ(H_Y) on the infinite tiling Y | the floor of one tiling |
| **E_FR30** | E(Y) for Y ∈ Ω_FR30. The value does not depend on Y: by minimality any finitely supported trial vector on Y has a copy, with the same Rayleigh quotient, on every Y′ ∈ Ω_FR30 | **the infinite-volume FR30 floor** |
| E_Z₂, E_trivial, E(χ∘U) | the same quantity for the reflection-only hull, trivial links, and FR30's Abelian shadows | same normalisation |
| E_inf(R) | inf over Y ∈ 𝒯_R of E(Y) | ≤ E_FR30 |
| Y_L(d) | λ_min(H_pin(T_L)) for decoration d | **upper** bound on the hull floor (compression) |
| λ_min of a level-1 block | λ_min of the free H_U on the 8 tiles / 48 panels of a level-1 supertile, for one frame choice | input to Theorem F |
| B_R | block lower bound (Phase V-B method): cube blocks of side R+1, weight 1/(R(R+1)²), min over V_R | certified **lower** bound on E_inf(R) |
| D_R | min over legal balls B_t = {a : \|x_a − x_t\| < R} of λ_min(H_Y\|_{B_t}) | each term is ≥ E_FR30, so D_R is an **upper** bound on E_FR30. What is certified is a lower bound d_R ≤ D_R |
| Λ_R | min over legal balls of λ_min((24 − Ã_ρ)\|_{B_t}), with ρ = R − 311/175 and Ã_ab = A_ab / c(\|x_a − x_b\|/ρ) | certified **lower** bound on E_inf(R) (Theorem 7.1) |
| c(η) | ∫χ_y(a)χ_y(b)dy for the Dirichlet ball ground state: [π(1 − η/2) sin πη + 1 − cos πη]/(π²η), with 0 < η ≤ 1 | exact overlap |
| ε(ρ) | max over legal 1-stars of Σ over the 24 panels f of (1/c(\|h_f\|/ρ) − 1) | localization cost: Λ_R ≥ D_R − ε, and D_R ≤ E_FR30 + ε |
| S₁ | max over legal 1-stars of Σ_f \|h_f\|² = 4734/49 | ε(ρ) ≤ K·S₁/ρ² |
| χ_k∘U | Abelian shadow: χ_k : Q₈ → {±1} is the character with kernel ⟨q_k⟩ (k = 1, 2, 3), applied link by link to U_FR30. It is gauge-covariant under Q₈-valued gauge transformations | matched Abelian control (same geometry and hierarchy) |
| w | Wilson action density, the plaquette mean of 1 − ½Re tr W, which equals f_trl + 2·f_m1 | flux magnitude |
| r_L | (Y_{L−1} − Y_L)/(Y_{L−2} − Y_{L−1}) | finite-size approach ratio (pre-registered in `phase7b_scaling.py`) |

**Notation used in the Phase VII report before VII-B, and its replacement.**
- "L_R" was used both for the block bound (now **B_R**) and for the IMS bound (now **Λ_R**).
- "min λ_min((24−A)|ball), certified" is **D_R**. Its certificate is a *lower* bound on D_R.
- "L2" in the decoration sweep is **B₂(rule)**.
