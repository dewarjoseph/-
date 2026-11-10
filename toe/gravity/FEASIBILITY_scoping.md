# Feasibility scoping: dynamical substitution geometry via Regge / CDT

**Read-only scoping, gated; nothing here enters the ledger.**

The opening sections preserve the pre-T1 scoping snapshot. Their "nothing computed / no prereg"
status is historical; the later dated **T1 outcome** section and `results/T1_RESULTS.md`
record the subsequent frozen test and finite-level computations.

- **Author:** ToE Gravity, 31 Oct 2026, ~22:00 PT. Notion row: "Feasibility study: dynamical substitution geometry via Regge / CDT" (due 4 Nov).
- **Gate:** all dynamical work stays gated until the Phase 3 scaling gap closes (2I → SU(2); owner: Theory of Everything). Nothing here was computed. No prereg was frozen, no ledger entry was made, and nothing was written into toe/ or /workspace/toe-gauge.
- **Sources read (read-only):** the toe mirror `/workspace/qis-eth/mirror/toe` (README, SCORECARD, CORE, PROOF, TOE_ATTEMPT, `src/chair.py`, `src/gauge.py`, `src/g3_time.py`) and ToE Gauge Theory's notes (`/workspace/toe-gauge/B3_trajectory.md`, `G3H_results.md`). Nothing from the excluded Antigravity monograph lineage is used.
- **Labels (exactly one per claim):** [P] proved · [C] computed · [E] numerical/simulated evidence · [X] conjecture · [A] analogy · [F] falsified. "Repo [P]" means the label is the toe repo's, not mine. Every idea in this note is unproved. Unless a claim is attributed, it is [X] or [A].

---

## 0. One-paragraph summary

- **The geometry is fixed.** The substitution geometry is a cubical subdivision of flat ℝ³ by unit cubes, grouped into chairs. Every interior Regge deficit angle is 0 (repo [P], TOE_ATTEMPT §3.6).
- **The frames carry no metric.** The only rule-dependent data are the tile frames M_a, which are rotations of the cube, so M_aᵀM_a = I [P, elementary]. They act like orientation/"spin-connection" data, not metric data.
- **A metric therefore has to be added.** There are three honest places to put it:
  1. edge lengths or tile-wise metrics on the existing complex (fixed combinatorics);
  2. the substitution *hierarchy* itself, read as a fourth, scale-like direction, where it naturally carries constant negative curvature [X];
  3. an induced (Sakharov-type) effective action of the project's matter/gauge sector on a deformed geometry [X].
- **Sum over histories.** A CDT-style sum over substitution histories is the most ambitious route and the least feasible: inside the substitution class the geometry does not depend on the rule (repo [P], CORE §1).
- **Recommendation.** Do one gate-light geometric test first: the rigidity count of tile-wise Regge metrics (Route 1, test T1). Make Route 3 (induced gravity) the main physics target once Phase 3 closes. Keep Route 4 (hierarchy as a hyperbolic direction) as the high-risk, high-reward side track. Defer Route 2 (CDT).

---

## 1. What geometry the project actually has

### 1.1 The object (from the repo)

- **Tiles.** A tile is a chair: seven unit cubes, a 2×2×2 block minus one corner. Its pose is (G, T), with G a 3×3 signed permutation matrix (the *frame*) and T ∈ ℤ³ (repo [P], CORE §1; `src/chair.py`).
- **Substitution.** A frame rule d = (π₀,…,π₇) ∈ S₃⁸ fixes the frames of the eight children. Child c of (G, T) is (G h_c, 2T + G t_c).
  - The substitution is an exact similarity by a factor of 2.
  - T_L has 8ᴸ tiles and occupies [0, 2^{L+1})³ minus the upper octant (repo [P]).
- **The geometry does not depend on d; only the frames do** (repo [P], CORE §1.1).
  - Consequence [P, elementary]: the owner grid, the panel multigraph K(T_L) (24-regular), and the rigid-tile gauge complex of `gauge.py` are identical for FR30 and 1387.
  - ToE Gauge's G3H notes record this as "the whole sector is frame-blind" ([P] by construction, G3H_results.md).
- **Frame walk.** H = ⟨h₀,…,h₇⟩. Primitivity means Sᵏ = H for some k. FR30 and 1387 are primitive with k = 2 and |H| = 24 (repo [C], PROOF.md §6). 1 666 486 of the 6⁸ rules are primitive; 13 130 are imprimitive (periodic frame walk), including the frontier rules x539311 and x539291 (repo [C]).
  - Both rules have only proper frames, det = +1 (stated in B3_trajectory.md §3). So H is a subgroup of order 24 of the 24-element rotation group of the cube, hence **H = O ≅ S₄, the chiral octahedral group** [P, elementary deduction from the repo's [C] count].
  - Its spin double cover is the binary octahedral group 2O (order 48). Note that 2O, not 2I, is the double cover of the frame group; the Phase 3 intermediate group 2I does not contain 2O [P, elementary group theory].
- **Hull.** For primitive rules the ℤ³ hull is uniquely ergodic (repo [P], PROOF.md §6, via Solomyak 1997 `solomyak1997dynamics`).
- **Connection.** The frame (Pauli) connection is U_f(a→b) = (σ·u_a)(σ·u_b) ∈ Q₈, with u_a = M_aᵀe_k the frame row along the panel axis (repo [P]). The θ-family is U_θ = R_{u_a}(θ)R_{u_b}(θ)⁻¹.
  - Along θ_L = π·2⁻ᴸ (θ = κa with a = 2⁻ᴸ) the floor obeys G_L = 4ᴸ(λ(θ_L) − λ₁) → π²c_∞ (repo [E], B3).
  - c_L → ρ(d) for primitive rules (repo [P], PROOF.md Thm F).
  - Brackets: ρ(FR30) ∈ [13.232574, 15.465590] and ρ(1387) ∈ [14.161980, 16.390966] (repo [C]).
  - ToE Gauge has certified finite-L upper bounds on G_L through L = 5 ([C] in their sense: double precision with a rounding allowance), and L = 6 certificates are running under prereg (B3_trajectory.md).
- **Time direction.** The spacetime complex T_L × ℤ_Nt with rigid tiles has a positive self-adjoint transfer matrix (repo [P], G3 R0). Its strong-coupling spectrum matches the derivation (repo [E]).
  - The Kogut–Susskind Hamiltonian limit gives Δ(g) = 3g²/4 − 2√2/g² + O(g⁻⁶), independent of L and of the rule (ToE Gauge [P]/[C], G3H).
  - Space and time are treated differently, and there is no Lorentz invariance (repo [P] as a scope statement).
- **Gravity row (scorecard row 5)** is **missing**, with an obstruction recorded (repo [P]):
  - every interior lattice edge lies in exactly four unit cubes, so every deficit angle is 2π − 4·π/2 = 0 and the Regge action vanishes at every level;
  - "a dynamical geometry leaves the substitution class", because a generic edge-length change or re-triangulation destroys the legal-patch structure that K2–K10 use.
- **4D candidate.** A 4D chair C₄ has known face counts (80, 212, 210, 92, 15), χ = 1 (repo [C], CORE §3, geometric-unity notes). It carries no verified connection (repo, TOE_ATTEMPT §3.4).

### 1.2 Where metric degrees of freedom could live

| candidate carrier | what it is | can it carry a metric? | label |
|---|---|---|---|
| Frames M_a | rotations in O ⊂ SO(3) | No. M_aᵀM_a = I, so a "frame-induced metric" is the identity. Frames are orientation (local-rotation) data: the analogue of the spin-connection/Lorentz half of a first-order (Cartan) formulation, with the triad-length half missing | [P] for M_aᵀM_a = I; [A] for the Cartan reading |
| Frustration / Q₈ holonomy | non-integrability of the frame field | It is curvature of the *frame connection*, not of the metric (the metric is flat). The closest classical picture is a flat metric with a frame field whose induced connection is non-trivial, in the spirit of teleparallel/torsion formulations | [A] |
| Edge lengths of the unit-cube complex | the standard Regge variables, after subdividing cubes into simplices | Yes, but the cube complex is just a region of ℤ³; the tiling only labels cubes. Without a tile-tied constraint the substitution is inert | [P] for "the cubes are those of ℤ³" (owner grid, `chair.py`); [X] for "inert" |
| Tile-wise metric g_a (constant on each chair, tangential–tangential continuity across panels) | a "Regge metric" in the finite-element sense, on chair cells | Possibly. Whether such metrics have local degrees of freedom modulo discrete diffeomorphisms on T_L is the open count in test T1 | [X] |
| Deficit angles at tile vertices | — | In 3D Regge calculus curvature sits on edges (hinges), not vertices. The interior hinges are all flat (repo [P]). The non-trivial dihedral angles are only the re-entrant edges of the chair's missing corner and of T_L's missing octant (exterior angle 3π/2), i.e. boundary/extrinsic data | [P] elementary |
| Substitution level ℓ (scale) | each level is an exact ×2 similarity | Yes, as a scale direction. Placing a level-ℓ supertile at height z ∝ 2^ℓ in an upper half-space with metric (dx² + dz²)/z² makes every supertile cell of bounded size, so the hierarchy is a discrete model of hyperbolic 4-space with ℝ³ (the tiling) as its conformal boundary | [X] (the construction is standard in spirit, the "hyperbolic filling" of a metric space; no source verified here, so treat it as unsourced) |
| θ (or κ) promoted to a local field θ_a | the scaling trajectory parameter | A scalar (dilaton-like) field, not a metric. Its effective potential would be κ(x)²ρ(d) at leading order | [X] |

**Bottom line for (a).** The project has orientation data (frames, holonomy) and an exact scale hierarchy, but no metric data [P for "no metric data at fixed geometry", from the repo's definitions]. Any gravitational degree of freedom has to be *added*. The real question is whether the substitution can constrain or source it rather than sit inert under it [X].

### 1.3 Two structural facts every route must respect

1. **3D Einstein gravity has no local propagating degrees of freedom** [P; Deser, Jackiw, 't Hooft 1984]. So Regge calculus on the 3D hull alone cannot give gravity with gravitons. Any honest attempt needs 4D: the spacetime complex T_L × ℤ_Nt, the 4D chair C₄, or the 3D + scale "hierarchy space" of Route 4 [P for the counting statement; route choice X].
2. **Every limit found so far is free physics, and the hull has acted as an inert lattice** (repo, TOE_ATTEMPT §7; the label there is a summary of [E]/[P] results). Each route below therefore includes a *substitution-sensitivity* test: if the observable is rule-blind, the route reduces to standard quantum gravity on a cubic lattice and adds nothing to this programme [X].

---

## 2. Candidate routes

### Route 1: Regge action on the substitution complex, fixed combinatorics

**Idea.**
- Keep the combinatorics fixed by the substitution and let a metric vary.
- 1a: subdivide each unit cube (3D) or 4-cube (on T_L × ℤ_Nt) into Kuhn/Freudenthal simplices (6 per cube, 24 = 4! per 4-cube) and use Regge edge lengths. The diagonal of each cube can be chosen by the owning tile's frame, so that the triangulation, and hence the dynamics, depends on d [X].
- 1b: use tile-wise constant metrics g_a with tangential–tangential continuity across panels (Regge metrics in the finite-element sense of Christiansen 2011) [X].

**Literature anchors.**
- Regge 1961 (action and deficit angles).
- Cheeger, Müller, Schrader 1984: for smooth metrics, Regge curvature of piecewise-flat approximations converges in the sense of measures. This is a consistency result, per Christiansen's own summary.
- Christiansen 2011: the linearised 3D Regge action around flat space equals the curlᵀcurl quadratic form; linearised Regge eigenpairs converge to the continuum ones on tori.
- Barrett 1987 and Barrett–Williams 1988: geometry of classical Regge calculus; convergence of lattice solutions of linearised Regge calculus.
- Brewin–Gentle 2001, "On the convergence of Regge calculus to general relativity".
- Roček–Williams 1981 (quantum Regge calculus) and 1985 (3D Einstein gravity and Regge calculus).
- Hamber 2009 (review).
- Dittrich–Steinhaus 2012 (measure and triangulation independence).
- For each source, the claims used here are those stated in its title or abstract [P/E as stated by the authors]. Their applicability to chair complexes is [X].

**What would have to be shown.**
1. The linearised Regge Hessian on the (4D) substitution complex has kernel = discrete diffeomorphisms only, with no spurious zero or ghost modes beyond the known conformal-mode sign problem [X].
2. Its spectrum converges along the substitution levels (refinement by ×2) to linearised Einstein–Hilbert. Christiansen's result needs shape-regular meshes and periodic (torus) settings. Kuhn simplices are all congruent, so shape regularity is free [P, elementary]. The pinned, non-periodic T_L with a missing octant is not covered [X].
3. **Substitution sensitivity:** some low-lying observable differs between rules, e.g. between FR30 and 1387 [X]. Otherwise the route is lattice gravity on ℤ³ and the hull is inert.

**Main obstruction.**
- The substitution enters only through decorations of an ℤ³ cube complex.
- With uniform Kuhn subdivision, Route 1 is rule-blind by construction [P, elementary: the complex is then independent of d].
- With frame-chosen diagonals it is rule-dependent, but there is no reason the dependence survives the continuum limit. Frame fields homogenise (G2 Part B: "no gauge field survives", repo [E]) [X].
- The repo's G6 point also stands: varying edge lengths leaves the substitution class, so no certified hull result (K2–K10) constrains the dynamics.

**Falsifiable first tests (for a later prereg).**
- **T1 (rigidity count; gate-light, pure linear algebra).** On T_L, L = 1…4, for FR30 and 1387, compute the dimension D_L of the space of tile-wise constant symmetric metrics with tangential–tangential continuity across every panel, modulo linearised discrete diffeomorphisms.
  - The prereg must freeze both alternatives: H0 says D_L stays bounded (tile-wise metrics are rigid, so Route 1b collapses to 1a); H1 says D_L grows ∝ 8ᴸ (tile-level local degrees of freedom exist).
  - I do not have a confident prediction. A cube-by-cube heuristic suggests some tt-continuous piecewise-constant metrics depend on two coordinates [X], but tile-wise constancy adds constraints.
  - Either outcome decides whether a metric can be tied to *tiles* rather than to cubes.
- **T2 (frame-blindness of linearised 4D Regge).** On Kuhn-subdivided T_L × ℤ_Nt, compare uniform diagonals with frame-chosen diagonals.
  - Prediction [X]: after removing the 4·(#interior vertices) diffeomorphism zero modes, the lowest k nonzero eigenvalues of the Regge Hessian agree between FR30 and 1387 up to a relative difference that shrinks by at least ×2 per level.
  - If the difference does *not* shrink, the substitution survives as a gravitational effect: that is the interesting failure.

### Route 2: CDT-style sum over substitution histories

**Idea.**
- Causal dynamical triangulations (Ambjørn–Loll 1998; Ambjørn–Jurkiewicz–Loll 2001, 2004, 2005; review Ambjørn–Görlich–Jurkiewicz–Loll 2012; Ambjørn–Loll 2024) sum over causal triangulations with a distinguished foliation.
- They report an emergent 4D, de Sitter-like universe and a scale-dependent spectral dimension (≈ 4 at large scales, smaller at short scales) [E, as reported by those authors, from simulations].
- Two foliations are available here:
  - **2a, the existing time direction:** slices are legal patches of the hull and the transfer matrix is the G3 one (repo [P] for positivity).
  - **2b, the substitution level as time:** each step deflates (or inflates) by ×2, so spatial volume grows as 8^ℓ, which reads as an exponential (de Sitter-like) scale factor [A].
- Fluctuations would come from:
  - (i) random rule sequences per level (S-adic histories), which change only frames, not geometry (repo [P]: the geometry does not depend on d);
  - (ii) local inflation/deflation moves, replacing one supertile by its 8 children "at unit size" as in DT, where every building block counts as equilateral. Mixed levels then create combinatorial curvature defects [X].

**What would have to be shown.**
1. A well-defined move set on mixed-level chair configurations that is ergodic and keeps a causal foliation [X].
2. Positivity or reflection positivity of the resulting transfer matrix [X]. G3 R0 covers only the fixed-geometry Wilson theory.
3. A non-trivial phase with extended 4D geometry [X].

**Main obstruction.**
- Within the substitution class there is *no* metric fluctuation: all rules share one geometry (repo [P]), so 2a and 2b(i) are sums over frames (gauge-like data), not geometries [P, elementary consequence].
- 2b(ii) needs gluing a size-2 supertile face to unit chair faces. This is non-conforming (hanging nodes), so the configurations are not simplicial manifolds without further subdivision [X].
- And the repo's G6 point applies: a substitution tiling is a single, measure-zero point in a CDT ensemble (repo [P] as stated, TOE_ATTEMPT §3.6).

**Falsifiable first test.**
- **T3 (spectral-dimension pipeline control).** Measure the return probability P(σ) of the lazy random walk on the panel multigraph K(T_L) and on the spacetime complex T_L × ℤ_Nt (fixed geometry, no sum).
  - Prediction [X]: d_s(σ) = −2 d ln P/d ln σ lies within 5 % of 3 (resp. 4) over σ ∈ [16, 4^{L−1}], for both rules, with no short-distance dimensional reduction.
  - This is a *control* that is expected to hold; it validates the pipeline before any sum over histories is attempted. Spectral-dimension methodology: Ambjørn–Jurkiewicz–Loll 2005; Calcagni–Oriti–Thürigen 2014; for fractal graphs, Rammal–Toulouse 1983.
  - A failure would itself be informative: the chair contact geometry (two-link bundles, G3H) would then distort diffusion at the scales probed.

### Route 3: Induced (Sakharov) gravity from the project's matter/gauge sector

**Idea.**
- Sakharov (1967; reprinted in Gen. Rel. Grav. 32 (2000) 365) and Visser 2002 (modern perspective): Einstein–Hilbert terms arise in the one-loop effective action of matter on a curved background [A as applied here; the general mechanism is as stated by those authors].
- Here: put a metric perturbation g = δ + h on the chair complex as panel/hopping weights. The cubical Laplacian with diagonal metric has hopping ∝ 1/g_kk [P, elementary for diagonal metrics].
- Expand W[h] = ½ log det(H_{U,g}) or the heat trace Tr e^{−tH_{U,g}} to second order in h, for U = the frame connection, the θ-family on its trajectory, or the SU(2) Wilson ensemble.
- The coefficient of the curvature-like term gives an "induced 1/G" that depends on the mass κ²ρ(d) and on the cutoff [X].
- This is the one route where the project's actual content (frustration, ρ(d), C_pert, the two-link contact geometry) could feed gravity [X].

**What would have to be shown.**
1. The second-order response is local, converges along L, and separates into a covariant part (∝ ∫ R √g plus a cosmological term) and lattice-artefact (non-covariant) parts [X].
2. The covariant coefficient has the right sign [X].
3. It depends on d (substitution sensitivity) [X].

**Main obstruction.**
- Sakharov-type induced couplings are UV-dominated, so G_induced is set at the cutoff. That is the same "cutoff-scale" no-go the repo already met for the floor (repo [E]/[P]: the floor is a mass renormalisation, G2 Part A) [X that it recurs here].
- The 3D spatial hull gives at best 3D induced gravity, which is topological (§1.3). A 4D version needs a resolved time direction with a continuum limit, which does not exist yet (repo: row 4 missing).
- The lattice breaks diffeomorphisms, so non-covariant terms will compete [X].

**Falsifiable first test.**
- **T4.** On T_L (L = 2…5, both rules, frame connection on the spinor block), compute the second-order response of the hull-averaged heat trace to (i) a long-wavelength conformal weight perturbation and (ii) a pure-gauge perturbation (the lattice image of a smooth diffeomorphism). Predictions [X]:
  - (a) the response to (ii) vanishes to leading order in the wavelength (geometric consistency; failure falsifies the route at this order);
  - (b) the coefficient in (i) converges geometrically in L (difference ratios ≤ 0.75, mirroring B1);
  - (c) FR30 and 1387 differ by more than the numerical error.
- **This test is gated twice:** it needs the matter sector's continuum statement (B3) and, for the gauge-ensemble version, the SU(2) scaling statement.

### Route 4 (ambitious): the substitution hierarchy as a curved scale direction

**Idea.**
- Build the *inflation complex* I_L: cells are (supertile S of level ℓ ≤ L). Adjacency is parent–child plus same-level panel contact. Edge lengths come from the upper-half-space metric (dx² + dz²)/z² with z ∝ 2^ℓ.
- Every cell then has bounded hyperbolic size, and Regge deficit angles are generically non-zero. The hierarchy itself carries constant negative curvature, with the tiling as its conformal boundary [X].
- This turns the repo's "inert lattice" into the boundary of a curved bulk.
- Related, verified work:
  - Boyle–Dickens–Flicker 2020: boundaries of discrete holographic tensor networks naturally form "conformal quasicrystals", including a Penrose-related example;
  - Jahn–Zimborás–Eisert 2022: tensor-network models of AdS/qCFT;
  - Boyle–Steinhardt 2022: self-similar 1D quasilattices with invertible substitution rules;
  - Bahr–Dittrich 2009: improved and perfect actions in discrete gravity, i.e. coarse-graining of Regge actions, the natural analogue of deflation.
  - The link to all of these is [A].
- Separately, Amaral–Clawson–Irwin 2023 (arXiv preprint, no journal reference listed) define "quasicrystalline spin foams" constrained to quasicrystal geometries. It is the only work found that puts gravitational (spin-foam) dynamics on aperiodic tilings; I verified its existence, but its results are not used here [A].

**What would have to be shown.**
1. The Regge action of I_L, with z-dependent edge lengths, converges per unit hyperbolic volume to the Einstein–Hilbert density of H⁴ (a Cheeger–Müller–Schrader-type consistency on this specific complex) [X].
2. Fluctuations of the edge lengths around this background have a well-posed linearised theory [X].
3. The frames (a 2O-liftable O-field) give the bulk a non-trivial spin structure or connection that is not pure gauge [X].

**Main obstruction.**
- This is Euclidean AdS-type geometry, not Lorentzian 3+1 with the tiling *as* space.
- The boundary ℝ³ is the tiling, so the "space" of the bulk theory is a 4D scale-extended object, and the physical interpretation (holography versus cosmology) is unsettled [X].
- No literature found treats a 3D substitution tiling as a holographic boundary; Boyle–Dickens–Flicker treat 1D and a Penrose-related example [A].

**Falsifiable first test.**
- **T5.** For I_L with L = 2…5, FR30 geometry, assign hyperbolic edge lengths and Kuhn-subdivide each cell. Prediction [X]: the total Regge action divided by the total hyperbolic 4-volume converges, with ratio of successive differences ≤ 0.75, to the H⁴ value of the Einstein–Hilbert density (curvature −1 normalisation, fixed in the prereg before computing).
- **Rule-independence of T5** is predicted [P, elementary]: the geometry does not depend on d. So T5 tests only whether the hierarchy carries curvature. The rule enters at the next step (frames as bulk spin data).

---

## 3. Prerequisites from the open gaps, named precisely

| prerequisite | where it stands now | which routes need it |
|---|---|---|
| **P-S1. B3:** G_L → π²ρ(d) along θ_L = π·2⁻ᴸ, uniformly in L (θ³ remainder uniform) | repo [E]. ToE Gauge: upper side reduced to a sigma-model problem [P], certified finite-L upper bounds L ≤ 5 [C], L = 6 certificates and the T6 lower bound running under frozen preregs (`B3_cert_L6.json`, `B3_lower_T6.json`); lower side and uniform-in-L statement open | Route 3 (the mass entering the induced coefficient); Route 4 step 3 |
| **P-S2. SU(2) scaling on the chair complex beyond weak-coupling perturbation** | G2 Part A: R_SU2 → 1 at β = 64 on T₂, T₃ (W1, W2 hold, repo [E]); 2I freezes between β = 8 and 16 (β_× = 12.4, repo [E]); Q₈ has no continuum limit (repo [P]). Phase 3 2I → SU(2) step not closed | Route 3 (gauge-ensemble version); any route that couples a dynamical gauge field to geometry |
| **P-S3. Imprimitive rules** (13 130 rules with a periodic frame walk; even/odd limits) | open (PROOF.md "not proved" item 2) | Route 2b (level as time needs a monotone, rule-uniform level limit); Route 4 if frontier rules are used |
| **P-T1. A time direction with a continuum limit and a tuned anisotropy a_t/a_s** | G3 R0 [P] (Euclidean transfer matrix, rigid tiles, T_L × ℤ_Nt); G3H [P]/[C] strong-coupling Hamiltonian; no weak-coupling Hamiltonian limit, no Lorentz invariance, no anisotropy tuning (repo scope statement; G3H "not added") | Route 1 in 4D (T2), Route 2a, Route 3 in 4D |
| **P-T2. Wick rotation / causal structure** | missing (repo row 4) | Route 2 (CDT is Lorentzian by construction); Lorentzian versions of all routes |
| **P-G. A 4D base** (T_L × ℤ_Nt, C₄, or the inflation complex) | T_L × ℤ_Nt exists (G3); C₄ complex counts only (repo [C]), no connection; inflation complex not built | Routes 1, 2, 4 |

Gate-light items, which in principle do not depend on P-S1/P-S2: T1 and T5 (pure geometry/linear algebra) and T3 (a pipeline control). They are still listed as gated here, because the project rule is to freeze a prereg before any computation and Joey's brief gates the dynamical work [P as a statement of process].

---

## 4. Recommendation and rough ordering

1. **First (when the gate lifts, or earlier only if Theory of Everything explicitly ungates pure-geometry counts): T1, the rigidity count of tile-wise Regge metrics.** It is cheap and decisive. It answers whether a metric can be tied to chairs at all (H1) or whether every Regge-type route collapses onto an ℤ³ cube lattice with the substitution as decoration (H0) [X for both alternatives].
2. **Second: T5, curvature of the inflation complex.** It is the only idea found in which the substitution *itself* produces curvature, through its hierarchy rather than through a deformation that leaves the class. It is pure geometry and rule-independent at first step [X].
3. **Third, the main physics target once P-S1 and P-S2 close: T4, induced gravity.** This is where frustration, ρ(d) and the contact geometry could enter a gravitational coupling. Expect the cutoff-scale obstruction; the decisive sub-test is (a), whether pure-gauge perturbations give zero response [X].
4. **Fourth: T2,** frame-blindness of linearised 4D Regge on T_L × ℤ_Nt. Run it after P-T1 gives a sensible anisotropy. The expected outcome is "frame-blind" [X], which would confirm the inert-lattice picture for Route 1.
5. **Last / defer: Route 2 (CDT).** T3 can serve as a pipeline control alongside T2. A genuine sum over substitution histories needs a non-conforming move set that does not exist yet, and inside the substitution class there is nothing metric to sum over [P, elementary consequence of repo [P]].

**Honest overall assessment [X].**
- Every route either leaves the substitution class (1, 2) or makes gravity emergent (3) or holographic (4).
- None is an extension of the certified core in the sense of K1–K15.
- The scorecard's row 5 obstruction (repo [P]) is not contradicted by anything here. This note only maps where a metric could be attached and how to falsify each attachment cheaply.

---

## 5. References (all verified this session; no others are used)

**Reused key** from `/home/box/shared/bibliography/bibliography.bib`: `solomyak1997dynamics` (B. Solomyak, "Dynamics of self-similar tilings", Ergodic Theory Dynam. Systems 17 (1997) 695–738, doi:10.1017/S0143385797084988).

**New entries**, verified via Crossref or the arXiv API on 31 Oct 2026. They are proposed keys only and were *not* added to the shared bib; the Literature Librarian owns that file.

| proposed key | reference |
|---|---|
| regge1961 | T. Regge, "General relativity without coordinates", Il Nuovo Cimento 19 (1961) 558–571. doi:10.1007/BF02733251 |
| cheeger1984curvature | J. Cheeger, W. Müller, R. Schrader, "On the curvature of piecewise flat spaces", Commun. Math. Phys. 92 (1984) 405–454. doi:10.1007/BF01210729 |
| barrett1987geometry | J. W. Barrett, "The geometry of classical Regge calculus", Class. Quantum Grav. 4 (1987) 1565–1576. doi:10.1088/0264-9381/4/6/015 |
| barrett1988convergence | J. W. Barrett, R. M. Williams, "The convergence of lattice solutions of linearised Regge calculus", Class. Quantum Grav. 5 (1988) 1543–1556. doi:10.1088/0264-9381/5/12/007 |
| brewin2001convergence | L. C. Brewin, A. P. Gentle, "On the convergence of Regge calculus to general relativity", Class. Quantum Grav. 18 (2001) 517–526. arXiv:gr-qc/0006017, doi:10.1088/0264-9381/18/3/311 |
| christiansen2011linearization | S. H. Christiansen, "On the linearization of Regge calculus", Numer. Math. 119 (2011) 613–640. arXiv:1106.4266, doi:10.1007/s00211-011-0394-z |
| rocek1981quantum | M. Roček, R. M. Williams, "Quantum Regge calculus", Phys. Lett. B 104 (1981) 31–37. doi:10.1016/0370-2693(81)90848-0 |
| rocek1985threed | M. Roček, R. M. Williams, "Three-dimensional Einstein gravity and Regge calculus", Class. Quantum Grav. 2 (1985) 701–706. doi:10.1088/0264-9381/2/5/012 |
| hamber2009lattice | H. W. Hamber, "Quantum gravity on the lattice", Gen. Rel. Grav. 41 (2009) 817–876. arXiv:0901.0964, doi:10.1007/s10714-009-0769-y |
| dittrich2012measure | B. Dittrich, S. Steinhaus, "Path integral measure and triangulation independence in discrete gravity", Phys. Rev. D 85 (2012) 044032. arXiv:1110.6866, doi:10.1103/PhysRevD.85.044032 |
| bahr2009perfect | B. Bahr, B. Dittrich, "Improved and perfect actions in discrete gravity", Phys. Rev. D 80 (2009) 124030. arXiv:0907.4323, doi:10.1103/PhysRevD.80.124030 |
| deser1984threed | S. Deser, R. Jackiw, G. 't Hooft, "Three-dimensional Einstein gravity: dynamics of flat space", Ann. Phys. 152 (1984) 220–235. doi:10.1016/0003-4916(84)90085-X |
| ambjorn1998lorentzian | J. Ambjørn, R. Loll, "Non-perturbative Lorentzian quantum gravity, causality and topology change", Nucl. Phys. B 536 (1998) 407–434. arXiv:hep-th/9805108, doi:10.1016/S0550-3213(98)00692-0 |
| ambjorn2001dynamically | J. Ambjørn, J. Jurkiewicz, R. Loll, "Dynamically triangulating Lorentzian quantum gravity", Nucl. Phys. B 610 (2001) 347–382. arXiv:hep-th/0105267, doi:10.1016/S0550-3213(01)00297-8 |
| ambjorn2004emergence | J. Ambjørn, J. Jurkiewicz, R. Loll, "Emergence of a 4D world from causal quantum gravity", Phys. Rev. Lett. 93 (2004) 131301. arXiv:hep-th/0404156, doi:10.1103/PhysRevLett.93.131301 |
| ambjorn2005spectral | J. Ambjørn, J. Jurkiewicz, R. Loll, "The spectral dimension of the universe is scale dependent", Phys. Rev. Lett. 95 (2005) 171301. arXiv:hep-th/0505113, doi:10.1103/PhysRevLett.95.171301 |
| ambjorn2012nonperturbative | J. Ambjørn, A. Görlich, J. Jurkiewicz, R. Loll, "Nonperturbative quantum gravity", Phys. Rep. 519 (2012) 127–210. arXiv:1203.3591, doi:10.1016/j.physrep.2012.03.007 |
| ambjorn2024gateway | J. Ambjørn, R. Loll, "Causal dynamical triangulations: gateway to nonperturbative quantum gravity", arXiv:2401.09399 (2024) |
| calcagni2014spectral | G. Calcagni, D. Oriti, J. Thürigen, "Spectral dimension of quantum geometries", Class. Quantum Grav. 31 (2014) 135014. arXiv:1311.3340, doi:10.1088/0264-9381/31/13/135014 |
| rammal1983random | R. Rammal, G. Toulouse, "Random walks on fractal structures and percolation clusters", J. Physique Lett. 44 (1983) 13–22. doi:10.1051/jphyslet:0198300440101300 |
| sakharov2000vacuum | A. D. Sakharov, "Vacuum quantum fluctuations in curved space and the theory of gravitation", Gen. Rel. Grav. 32 (2000) 365–367 (reprint of the 1967 paper). doi:10.1023/A:1001947813563 |
| visser2002sakharov | M. Visser, "Sakharov's induced gravity: a modern perspective", Mod. Phys. Lett. A 17 (2002) 977–991. arXiv:gr-qc/0204062, doi:10.1142/S0217732302006886 |
| boyle2020conformal | L. Boyle, M. Dickens, F. Flicker, "Conformal quasicrystals and holography", Phys. Rev. X 10 (2020) 011009. arXiv:1805.02665, doi:10.1103/PhysRevX.10.011009 |
| jahn2022adsqcft | A. Jahn, Z. Zimborás, J. Eisert, "Tensor network models of AdS/qCFT", Quantum 6 (2022) 643. arXiv:2004.04173, doi:10.22331/q-2022-02-03-643 |
| boyle2022selfsimilar | L. Boyle, P. J. Steinhardt, "Self-similar one-dimensional quasilattices", Phys. Rev. B 106 (2022) 144112. arXiv:1608.08220, doi:10.1103/PhysRevB.106.144112 |
| amaral2023quasicrystalline | M. Amaral, R. Clawson, K. Irwin, "Quasicrystalline spin foam with matter: definitions and examples", arXiv:2306.01964 (2023), preprint (no journal reference listed) |

**Not found / not claimed.**
- No verified work does Regge calculus or CDT on 3D substitution tilings.
- No verified rigorous convergence theorem for Regge calculus on non-periodic, non-simplicial (chair) complexes.
- The hyperbolic-filling construction in Route 4 is stated without a source.

## T1 outcome (2026-11-01)

The prereg is `prereg/T1_regge_rigidity.json` (sha256 `f369930b…8e47`, frozen before the run, bus #474). Results are in `results/T1_RESULTS.md`.

**Counts [C], all ranks certified exact.**
- For FR30 and 1387 at L = 1..5 (up to 32768 tiles), tile-wise constant metrics with tangential-tangential continuity form a space of dimension N_L = 6.
- The interior count is 6 at L = 2..5; at L = 1 it is 0 (there are no interior tiles).
- The gauge rank is G = 6, so the moduli count is Q = 0.
- The two rules give identical partitions and identical counts.

**Control [C].** The cube-level control reproduces its exact formula 3n + 3n², so the pipeline is not blind to local moduli.

**Verdict.** The frozen alternative **H0 holds** for L ≤ 5 [C]; it is [X] for all L.

**Implication for Route 1.**
- **R1b has no local moduli at the tested levels L = 1..5.** In the tested tile-wise metric space, only global constant metrics remain [C]. This is not an all-level proof that the route is impossible.
- **To obtain local moduli at these tested levels in this model, refine below the tile or change the model.** Kuhn simplices or edge lengths on the cube or simplicial subdivision are candidate refinements, not a proved classification of all Regge routes.
- **At that resolution the substitution carries no metric role in the count.** The cell complex is a subset of the ℤ³ cube complex, so Route 1 reduces to R1a: ordinary Regge on a cubic or simplicial lattice, with the chair tiling as decoration.
- T2 (frame-blindness) is therefore expected, and is now low priority.

**Updated ordering.**
- Make Route 3 (induced gravity) the main physics target once Phase 3 closes.
- Keep Route 4 as the high-risk side track.
- Deprioritise Route 1 together with Route 2.
