# Phase VI — Is there a bridge between gauge theory and quantum mechanics in the Chair44 Clifford-holonomy framework?

**Scope.**
- *Branch.* `claude/phase6-gauge-qm-audit`, from the Phase V-E head.
- *Code and tests.* New code is in `audit/phase6_*.py`, tests in `tests/test_phase6.py` (10 tests, passing) and Lean in `certificates/Phase6Gauge.lean`.
- *Results.* `audit/results/phase6_*`.

**Status tags.**
- **[P]** proved: proof given here, or kernel-checked where stated.
- **[C-A]** computer-assisted proof: exhaustive finite computation in exact arithmetic.
- **[E]** numerically verified, with the stated error.
- **[S]** suggested by data, not established.
- **[U]** unsupported.

---

## 1. Executive finding

**The bridge that exists.** The repository contains a genuine, exactly verifiable chain from the substitution geometry to a quantum spectral observable:

**Chair substitution geometry → Clifford face-normal connection with forced curvature → gauge-covariant Hamiltonian D_U†D_U with a strictly positive ground energy.**

**The strongest new result is Theorem F** (§7), computer-assisted and certified in exact arithmetic:
- Take *every* orientation-preserving frame field compatible with the chair substitution geometry. These are all 3^N choices, not only FR30 and not only self-similar rules.
- The induced Q8 connection is never pure gauge. Already on each level-1 supertile, 9 two-cycles carry holonomy −1 or a traceless class (Theorem F′, proved by hand).
- The connection Laplacian has inf spec ≥ **167/100**, uniformly, on every union of level-1 supertiles (every level-L supertile, L ≥ 1) and on the infinite tiling.
- With trivial links on the same graph, the ground energy is 0.

**What this changes in the reading of earlier phases.**
- *The positive spectral floor is local.* It is forced by the octant reflections of a single substitution step, not by aperiodic order or the substitution hierarchy.
- *The hierarchy affects the value, not the existence, of the gap.* FR30's bulk floor is certified in [4.008189, 8.7649120247]; other rules range up to about 9.5 at level 4.
- *Positivity is generic, not aperiodic.* A periodic cube-substitution control with the same construction is also gapped (1.85), and random Q8 links are gapped more strongly (14.4).
- *Non-Abelian structure matters quantitatively, provably.* The bulk floor of FR30 (≥ 4.008) strictly exceeds that of the Abelian Z₂ frustration produced by the octant reflections alone (≤ 3.8223, certified; Corollary F″).

**The mathematical machinery is standard.**
- Discrete connections and Wilson loops [Wilson 1974].
- Connection Laplacians and their zero modes [Kenyon 2011].
- Plaquette frustration [Toulouse 1977].
- Non-Abelian Hofstadter models [Osterloh et al. 2005].

**What is new, and what is not.**
- *New, as far as the searches went:* the specific structure theorems of the Clifford face-normal connection (lab-gauge form, corner factorization, axis flatness; §4) and the forced-frustration theorem for this geometry. These are model-specific results, modest in scope.
- *No new evolution law.* The repository contains **no quantum evolution law** beyond what this audit adds. The Schrödinger evolution e^{−itH_U} is the standard one, and is gauge-covariant in the standard way.
- *No new physics.* Nothing here derives quantum mechanics from geometry or unifies gauge theory with quantum mechanics.

**Corrected version of the claim under audit** (the original's errors are listed in §7.4):

> The repository does not derive quantum mechanics. It establishes an exact link from the chair substitution geometry, through a discrete non-Abelian Q8 ⊂ SU(2) connection, to the spectrum of a gauge-covariant Hamiltonian.
> 1. The connection U_f = (σ·M_aᵀn_f)(σ·M_bᵀn_f) is not pure gauge. For every orientation-preserving frame field compatible with the substitution geometry, curvature is forced on every level-1 supertile (Theorem F′; exhaustively confirmed for all 6561 rules). For FR30 the plaquette holonomy census obeys an exact substitution law: D·N_m(c) = 8^m W8(c) + 4^m W4(c) + 2^m W2(c) + W1(c), with limiting class frequencies 19/36, 13/144, 1/9, 23/144, 1/9. This is certified in Lean (`certificates/TypeSubstitutionCertificate.lean`: `class_counts_closed_form`, `limit_frequencies`) and reproduced by an independent count at levels 3 and 4. The decomposition lemma linking the geometry to the recursion is proved on paper and verified at levels 1–2.
> 2. Gauge covariance, H_U ↦ gH_Ug† under ψ_a ↦ g_aψ_a, U_ab ↦ g_aU_abg_b⁻¹, is an exact identity. It makes spectra and spin-traced transition probabilities gauge invariant. Numerical checks confirm it to ≤ 2×10⁻¹³ (`audit/phase5d_schur.py validate`, `audit/phase5e_run.py gauge`, `audit/phase6_gauge_audit.py`).
> 3. The non-trivial holonomy forces a strictly positive ground energy of H_U = D_U†D_U.
>    - For FR30 the bulk spectral floor is certified in [4.008189, 8.7649120247]. The lower end comes from a radius-2 collared local decomposition in exact arithmetic (`phase5b_e_radius2_bound.py`). The upper end is the exact Rayleigh quotient of the converged level-7 ground vector (`phase5e_level7_runner.py certify`).
>    - Every compatible frame field has floor ≥ 1.67, while the trivial connection has floor 0.
>    - Positivity is a local consequence of the geometry and is shared by periodic and random-flux controls. What distinguishes FR30 is the value of the floor and its hierarchy-dependent residual, established numerically against controls rather than proved.
>    - With free boundaries, frustration-induced surface states appear below the bulk floor.
>    - The child-to-parent Schur-complement recursion is exact (`phase5d_schur.py`, Theorem E1 of Phase V-E). No compressed renormalization flow separating FR30 from the controls has been found (Phase V-E).

**Corrected chain** (the diagram under audit, with every arrow justified):

$$\boxed{\text{chair substitution }\Sigma\text{ (octant reflections }D_{s(v)}\text{)}}\xrightarrow[\text{Thm G1–G3, F}']{\;U_f=(\sigma\cdot M_a^{\mathsf T}n_f)(\sigma\cdot M_b^{\mathsf T}n_f)\;}\boxed{Q_8\text{ connection, forced curvature}}\xrightarrow[\text{Lemma K, Thm F}]{\;D_U,\;H_U=D_U^\dagger D_U\;}\boxed{\text{gapped gauge-covariant Hamiltonian}}\xrightarrow[\text{exact identity}]{\;\operatorname{Spec},\ \mathrm{IDS},\ |\langle a|e^{-itH_U}|b\rangle|^2\;}\boxed{\text{gauge-invariant observables}}$$

| arrow | status | justification |
|---|---|---|
| Σ, FR30 → connection | **[P]** | Proposition E0 (Phase V-E: one geometry for all decorations) and the link formula. Curvature is forced for every proper compatible frame field (Theorem F′). For FR30 the census law is Lean-certified |
| connection → Hamiltonian | **[P]** | H_U = D_U†D_U is self-adjoint and gauge-covariant. ker H_U ≠ 0 ⇔ pure gauge (Lemma K). Uniform floor ≥ 167/100 (Theorem F, exact arithmetic) |
| Hamiltonian → observables | **[P] / [E]** | Spectra and spin-traced transition probabilities are gauge invariant (exact identity; checked to 2×10⁻¹³). FR30 bulk floor certified in [4.008189, 8.7649120247] |
| "Δ_solder" | **[U] as written** | the repository's *soldered* Laplacian is a real O(3)-frame operator with no Q8 links. The operator that carries the connection is D_U†D_U |
| "quantum transport" | **[U]** | no transport or time evolution is computed in the repository. The Schrödinger evolution e^{−itH_U} is standard; its covariance is shown in §5 (extension). Any transport claim needs a new computation |
| aperiodicity → gap | **[U] for existence, [E] for the value** | existence of the gap is local (Theorem F) and shared by periodic and random controls. Only the value, and FR30's residual, carry hierarchy information |

---

## 2. Repository map

| object | file : lines / function | what it is |
|---|---|---|
| substitution, FR30 frames | `audit/independent_clifford_q8_audit.py:11-31` (`FR30`, `tiles_at_level`); `src/chair44/frames.py`, `fr30_frames.py` | poses (G, T) by iterating 8 child maps: centre (P(π₀), (1,1,1)) and octant v (D_{s(v)}P(π_v), 4v); cubes = (G·bc + 2T − 1)//2 |
| panel multigraph | `independent_clifford_q8_audit.py:50-61` (`panel_edges`); `audit/phase6_gauge_audit.py` (`panels`) | one edge per shared unit panel, with normal e_k; multiplicities kept |
| Clifford link | `src/chair44/clifford.py:85-91`; `clifford_holonomy.py:54-60`; `holonomy.py:49-55`; `independent_clifford_q8_audit.py:63-65` | C_ab = (σ·M_aᵀn)(σ·M_bᵀn) ∈ Q8 |
| covariant Laplacian (free) | `src/chair44/clifford.py:63-99` (H_cliff, diagonal = degree) | D_U†D_U assembled entrywise |
| pinned Hamiltonian (Phases V) | `audit/phase5a_controls.py:91-101` (`build_H`, diagonal 24) | H_pin = 24 − A_U = D_U†D_U + (24 − Deg) |
| "soldered" Laplacian | `src/chair44/laplacians.py:27-79`; `solder_laplacian.py:16-61` | real 3N×3N operator with O(3) frames (L_proto ⊗ I₃ + normal projectors). **No Q8 links**; a different object from H_U |
| Hodge / cellular | `src/chair44/foam_hodge.py:52-66`; `cellular_complex.py:80-132` | real d₀, d₁, d₂ and Hodge Δ; no links |
| Kähler–Dirac | `audit/phase5c_dirac.py:85-188` | dual cubical complex, Q8 links on cube adjacencies (`:105-108`), D = d + d† |
| Q8 lattice gauge Monte Carlo | `audit/phase5c_q8_gauge.py:38-174` | Wilson-action heat bath with dynamical links. **It never uses the FR30 Clifford links**, and it does **not** test spectral gauge invariance |
| holonomy census law | `certificates/TypeSubstitutionCertificate.lean` (`class_counts_closed_form` :862, `total_closed_form` :867, `limit_frequencies` :875); data-free lemma `audit/results/phase5b_a_lean_datafree_extract.lean` (`closed_form_general` :189) | exact plaquette-class recursion (formal), plus a generic induction lemma (no census data) |
| controls | `audit/phase5a_controls.py:164-176, 71-79, 349-358`; `phase5a_scaling_controls.py:92-98` | trivial links; stripped (sign removed); randq8 (i.i.d. Q8); cube substitution (periodic) |
| bulk lower bounds | `audit/phase5a_star_closure_lower_bound.py` (1.568725); `audit/phase5b_e_radius2_bound.py` (72147403/18000000 = 4.008189) | local decompositions certified with exact LDLᵀ / Bareiss, under V-B's closure theorem |
| level-7 upper bound | `audit/phase5e_level7_runner.py certify` → `audit/results/phase5e_level7_certified.json` | exact Rayleigh quotient 2467103454595458/281474982023175 |
| time evolution | none in the repository before this phase (`audit/phase5_dynamics_boundary.py` is static despite its name) | — |
| 6D→3D quasicrystal modules | `src/icosahedral_qc/quantum_metric.py:69-179`, `honhse.py:16-64`, `non_hermitian.py:89-166`, `floquet_phason.py`, `floquet_pump.py` | independent of the Chair44 connection; no Q8/SU(2) links. Several outputs are calibrated constants or analytic ansätze (`quantum_metric.py:146-159`, `non_hermitian.py:152-155`, `floquet_phason.py:72`, `floquet_pump.py:21-38`) — **no gauge–QM bridge exists in this part of the repository** |
| Phase VI audit | `audit/phase6_gauge_audit.py`, `phase6_forced_flux.py`, `phase6_ablation.py`, `phase6_z2_ablation.py`; `tests/test_phase6.py`; `certificates/Phase6Gauge.lean` | this report |

---

## 3. Equation-level reconstruction

**Notation.**
- s(v) := σ·v. For a unit coordinate vector, s(v) is Hermitian and unitary with det −1, and s(v)² = 1.
- Tiles a carry frames M_a = G_a ∈ O(3,ℤ), signed permutation matrices. Under the substitution, det M_a = +1.
- Panels f = (a, b, k) are unit squares shared by tiles a ≠ b, with normal e_k. Several panels can join the same pair.

**Definitions.**

| object | definition |
|---|---|
| link | U_f := C_ab^{(f)} = s(M_aᵀe_k)·s(M_bᵀe_k), with U_{f⁻¹} = U_f† |
| Hilbert space | 𝓗 = ℓ²(tiles) ⊗ ℂ² |
| covariant coboundary | D_U: 𝓗 → ℓ²(panels) ⊗ ℂ², (D_Uψ)_f = ψ_a − U_fψ_b |
| free Hamiltonian | H_U := D_U†D_U = Deg − A_U, with (A_Uψ)_a = Σ_{f∋a} U_fψ_b |
| pinned Hamiltonian | H_pin := H_U + diag(24 − Deg_a) = 24 − A_U (Phases V-A to V-E) |

**Elementary facts [P].**
- Every 2×2 block of H is a real quaternion, so H commutes with T = (1⊗iσ_y)K, T² = −1. Every eigenvalue has even multiplicity (Kramers; Lean `kramers_commutes`).
- ‖A_U‖ ≤ 24 by the Schur test, so spec H_pin ⊂ [0, 48].

**Gauge group.** 𝒢 = ∏_a SU(2), acting by ψ_a ↦ g_aψ_a and U_f ↦ g_aU_fg_b⁻¹, so that H ↦ gHg†.

**Holonomy.** For a closed walk γ = (a₀, f₁, a₁, …, f_m, a₀), W_γ = U_{f₁}⋯U_{f_m}, and W_γ ↦ g_{a₀}W_γg_{a₀}⁻¹.
- The SU(2) conjugacy class is gauge invariant: {+1}, {−1}, or "traceless".
- The finer Q8 classes ±i, ±j, ±k are invariant only under Q8-valued gauge transformations. The Lean census uses Q8 classes; spectra are invariant under all of SU(2).

---

## 4. Gauge audit

All statements below are verified exactly on every panel and every fundamental cycle at levels 1–3, by `audit/phase6_gauge_audit.py`.

| level | tiles | panels | fundamental cycles (+1 / traceless / −1) | plaquettes (+1 / traceless / −1) | holonomy group |
|---|---|---|---|---|---|
| 1 | 8 | 48 | 17 / 23 / 1 | 26 / 31 / 3 | Q8 |
| 2 | 64 | 576 | 158 / 315 / 40 | 385 / 365 / 42 | Q8 |
| 3 | 512 | 5376 | 1571 / 2799 / 495 | 3945 / 3253 / 530 | Q8 |
| 4 | 4096 | — | — | 35161 / 27125 / 5394 | — |

The plaquette counts at levels 3–4 equal the Lean-certified closed form exactly (test `test_level3_census_matches_certified_closed_form`).

**Theorem G1 (lab-gauge form) [P, E].**
- *Statement.* For a proper frame M ∈ SO(3), let ĝ(M) ∈ SU(2) be a lift: ĝ(σ·v)ĝ† = σ·(Mv), defined up to sign. Then

  ĝ_a U_f ĝ_b⁻¹ = s(e_k) · ĝ_aĝ_b⁻¹ · s(e_k) = Ad_{s(e_k)}(ĝ_aĝ_b⁻¹).
- *Proof.* s(M_aᵀe_k) = ĝ_a†s(e_k)ĝ_a. Substitute into U_f. ∎
- *Check.* Maximum deviation 4.4×10⁻¹⁶.
- *Meaning.* Up to a gauge transformation, the connection is the frame-transition cochain ĝ_aĝ_b⁻¹ — a coboundary in the binary octahedral group 2O — twisted by the face π-rotation s(e_k). Without the twist (V_ab = M_aᵀM_b, the "vertex coboundary") the connection is pure gauge; the repository already certified this (`Chair44Certificates.lean`, `vertex_coboundary_3cycle_trivial`). **All curvature comes from the face-normal twist.**

**Theorem G2 (corner factorization) [P, E, Lean].**
- *Statement.* For a closed walk with panel normals n₁, …, n_m,

  W_γ = s(M_{a₀}ᵀn₁) · ∏_{i=1}^{m−1} [s(M_{a_i}ᵀn_i) s(M_{a_i}ᵀn_{i+1})] · s(M_{a₀}ᵀn_m).

  Each interior factor is 1 if n_i = n_{i+1} (a straight passage). Otherwise it is the *turning element* i·det(M_{a_i})·σ·(M_{a_i}ᵀ(n_i × n_{i+1})), a traceless unit quaternion. Lean: `corner_identity`, `straight_identity`.
- *Proof.* Telescope U_{f_i} = s(M_{a_{i−1}}ᵀn_i)s(M_{a_i}ᵀn_i). Then use s(u)s(v) = u·v + iσ·(u×v) and Mᵀ(u×v) = det(M)·(Mᵀu × Mᵀv). ∎
- *Check.* Exact (deviation 0) on all 41 + 513 + 4865 fundamental cycles.
- *Consequence.* The holonomy of a loop depends only on the frames of the tiles where the loop *turns* and on the turning planes. A loop that turns only at tiles of equal frame has W = 1, because ∏ s(n_i)s(n_{i+1}) telescopes to 1.

**Theorem G3 (axis flatness) [P, E].**
- *Statement.* For each axis k, the subgraph of e_k-panels carries a pure-gauge connection: U_f = g_a g_b⁻¹ with g_a = i·s(M_aᵀe_k) ∈ SU(2).
- *Check.* Exact. The zero-mode count on each single-axis subgraph equals 2 × (number of components).
- *Meaning.* The connection consists of three flat structures, one per axis. They are glued at each tile by the transition elements s(M_aᵀe_k)s(M_aᵀe_l). Curvature is exactly the failure of these transitions to be gauge-compatible around loops.

**Theorem G4 (curvature, not topology) [P].**
- *Statement.* A level-L supertile is a 3-ball, so its cube complex is simply connected. The cube-resolved connection is identity inside tiles and U_f across panels. Every tile-graph cycle lifts to a cube-graph cycle through tile interiors (each chair is face-connected). That cycle is a product of conjugated plaquette loops. Hence every holonomy is generated by plaquette holonomies.
- *Meaning.* Nontrivial holonomy ⇔ nonzero curvature. There is **no global topological holonomy**.
- *How the related notions separate here:*
  - Link variables ≠ 1 do not by themselves mean flux. A random gauge changes the links by up to 2 while every trace is preserved to 3×10⁻¹⁵.
  - Nonzero curvature ⇔ nontrivial holonomy.
  - The topology is trivial.

**Pure gauge or not?** Not pure gauge, at every level (Theorem F′ below). The connection *is* pure gauge in each of these cases:
- the frame field is constant (U ≡ 1);
- the face twist is removed (V_ab = M_aᵀM_b);
- the connection is restricted to one axis (G3);
- the frames ignore the substitution geometry (identity frames: tested, λ_min = 0).

---

## 5. Quantum audit

| item | status |
|---|---|
| Hilbert space | 𝓗 = ℓ²(tiles) ⊗ ℂ², finite-dimensional per patch. The infinite tiling gives ℓ²(ℤ-indexed tiles) ⊗ ℂ² with bounded H **[P]** |
| Hamiltonian | H_U = D_U†D_U (free); H_pin = 24 − A_U (pinned wall: diagonal 24 on boundary tiles = Dirichlet-type). Both are bounded and self-adjoint; no non-Hermitian description is needed **[P]** |
| gauge covariance | H ↦ gHg† exactly. Spectra are invariant; e^{−itH} ↦ g e^{−itH} g†; spin-traced transition probabilities P_ab(t) = ½‖⟨a\|e^{−itH}\|b⟩‖²_F are invariant **[P]**. Checked: spectra to 2×10⁻¹³, P_ab(t) to 7×10⁻¹⁶ at levels 1–3, while the amplitudes themselves change by up to 0.85 **[E]** |
| dynamics | **not implemented in the repository.** The natural law i∂_tψ = H_Uψ is standard, and its covariance is the identity above. It is used here only for the invariance check (labelled extension) |
| dependence on gauge-invariant data | the spectrum is a function of the gauge-equivalence class of U, i.e. of the holonomies (G4: of the plaquette fluxes) and the graph |
| zero modes | **Lemma K [P]:** ker H_U ≅ {v ∈ ℂ²: Wv = v for all W ∈ Hol} on a connected graph. An SU(2) element fixing a nonzero vector is the identity. So λ_min(H_U) = 0 ⇔ U is pure gauge (cf. Kenyon 2011 for general vector bundles). Checked: FR30 gives 2.889, 4.726, 5.115 at levels 1–3; trivial and random pure gauge give 0 (two zero modes) |
| continuum limit | **not established [U].** No single power law fits levels 4–7 (Phase V-E, r₇ = 0.194). The apparent D₂ ≈ 1.9 is boundary-condition dependent |
| Dirac operator | `phase5c_dirac.py` couples the Q8 links into a Kähler–Dirac operator on the dual cube complex. Its index is 2 = 2χ for every connection (topological, flux-blind). Flux makes its smallest nonzero \|E\| *smaller* (FR30 0.276 / 0.076 / 0.013 against trivial 0.660 / 0.342 / 0.173 at levels 1–3). The Dirac sector shows no flux-induced gap **[E]** |
| quasicrystal QGT, non-Hermitian, Floquet | not coupled to this gauge structure (§2) |

---

## 6. Reproduction report

**Environment.**
- *Hardware.* Windows 11, 24 cores, 32 GB RAM.
- *Software.* Python 3.12.10, numpy 2.5.2, scipy 1.18.1, Lean 4.35.0 (core).
- *Portability.* A stub for the Unix-only `resource` module makes the V-B/V-D modules importable.

| command | result |
|---|---|
| `python -u -I audit/phase6_gauge_audit.py 3` | A: independent operator equals `build_H` exactly (0.0). B: 4.4×10⁻¹⁶. C: 0. D: 0. Census and zero modes as in §4–5. `audit/results/phase6_gauge_audit.json` |
| `python -u -I audit/phase6_forced_flux.py` | 6561 / 6561 decorations not pure gauge (≥ 11 of 41 fundamental cycles nontrivial). Free λ_min: min 1.671574 (decoration 6255), median 3.063, max 4.026, FR30 2.889. **L_U − (167/100)·I ≻ 0 certified for all 6561 by exact rational LDLᵀ** (56 s). `phase6_forced_flux.json` |
| `python -u -I audit/phase6_ablation.py` | identity frames: pure gauge, λ_min = 0. Reflection-only frames M = D_s(v): Abelian ±1 links, 27 cycles with −1, λ_min = 2.923. 20000 random permutation choices (82 proper, 19918 improper): none pure gauge; min λ_min 2.121 proper, 1.899 improper. `phase6_ablation.json` |
| `python -u -I audit/phase6_z2_ablation.py` | reflection-only (Abelian Z₂) frames, pinned / free bottoms at L2–L4: 9.028 / 3.278, 5.133 / 3.318, 3.822 / 3.323. FR30: 10.777 / 4.726, 9.378 / 5.115, 8.920 / 5.210. Trivial: 4.751 / 0, 1.670 / 0, 0.503 / 0. **Exact certificate: E_∞(Z₂) ≤ E₄(Z₂) ≤ 1075868655136284/281475010395005 = 3.8222528**. Level 5 exceeded the 50-minute budget and was dropped. `phase6_z2_ablation.json` |
| Lean census check (test) | independent plaquette census = `class_counts_closed_form` at m = 3, 4 |
| `lean certificates/Phase6Gauge.lean` | `straight_identity`, `corner_identity`, `two_cycle_classes`: kernel-checked, no axioms (`audit/results/phase6_lean_compile.txt`) |
| `python -m unittest tests/test_phase6.py` | 10 / 10 pass |
| `python -m unittest tests/test_phase5e.py` | 15 / 15 pass (Phase V-E) |

**Existing results re-read from source** (pinned bottoms of 24 − A_U at levels L3 / L4 / L5 [/ L6 / L7]):

| system | values |
|---|---|
| FR30 | 9.3785 / 8.9196 / 8.7970 / 8.7701 / 8.7649 |
| trivial links | 1.6695 / 0.5027 / 0.1386 (→ 0) |
| randq8 | 15.145 / 14.695 / 14.408 |
| stripped (signs removed) | 6.959 / 6.146 / 6.001 |
| cube substitution (periodic, diagonal 6) | 1.914 / 1.861 / 1.852 / 1.851 |

**Failed attempt.** The first version of the two-cycle lemma omitted the factor det(M_a)·det(M_b). The randomized test with improper frames caught it, and the corrected lemma restricts the forcing argument to proper frames.

---

## 7. Theorem: forced frustration and a uniform spectral floor

**Setting.**
- The chair substitution places the child at octant v of a parent with frame G_p.
- Geometry compatibility means the child's frame maps the base chair onto the placed child. This forces M ∈ G_p·D_{s(v)}·S₃, because the chair is invariant exactly under axis permutations and its missing octant must map to octant s(v) = (1 − 2v).
- A frame field is **compatible** if every tile's frame is of this form relative to its geometric parent; it is **proper** if det M = 1 throughout.
- Proper compatible frame fields are exactly the per-tile choices in the 3-element coset. At level 1 these are the 3⁸ = 6561 parity-admissible decorations.
- The class includes every substitution rule and every non-self-similar field: the V-B controls `iid`, `coarse`, `fine`, `shuffle` and `flip`.

**Lemma F′.1 (two-cycle holonomy) [P, Lean for the finite identity].**
- *Statement.* Let tiles a, b share panels with normals e_k ≠ e_l, and let e_m be the third axis. The two-cycle a →(k) b →(l) a has

  W ∼ det(M_a)·det(M_b) · s(M_bᵀe_m) · s(M_aᵀe_m).

  For proper frames, W = 1 iff M_aᵀe_m = M_bᵀe_m, W = −1 iff M_aᵀe_m = −M_bᵀe_m, and W is traceless iff M_aᵀe_m ⊥ M_bᵀe_m.
- *Proof.* Theorem G2 with two turns, then the Lean `two_cycle_classes`. ∎

**Theorem F′ (forced flux) [P].**
- *Statement.* For every proper compatible frame field, every level-1 supertile contains 9 two-cycles with W ∈ {−1, traceless}. Hence the connection is not pure gauge on any patch containing a level-1 supertile, nor on the infinite tiling.
- *Proof.*
  - In parent coordinates, M_x = D_{s(v_x)}π_x with the centre's sign vector equal to +.
  - So M_xᵀe_m = s_{v_x}(m)·e_{π_x⁻¹(m)}.
  - If (v_a)_m ≠ (v_b)_m, the signs differ. Lemma F′.1 then rules out W = 1 for every choice of π_a, π_b.
  - The level-1 contact geometry contains 9 such (pair, axis-pair) configurations: the centre against octants (010), (100), (001), (011)×2, (101)×2 and (110)×2 (`audit/phase6_gauge_audit.py` geometry, listed in §6).
  - A level-1 block's links depend only on the frames relative to G_p, by link rotation invariance (V-D Theorem D0). ∎
- *Essential hypotheses.*
  - **Geometry compatibility.** Identity frames are pure gauge.
  - **Properness, for this proof.** With improper frames the factor det·det can cancel the sign mismatch. Empirically no improper field of 20000 sampled is pure gauge, but that case is **not proved**.

**Theorem F (uniform spectral floor) [C-A].**
- *Statement.* For every proper compatible frame field on any union 𝒫 of level-1 supertiles, including the infinite chair tiling:

  inf spec H_U ≥ 167/100   and   inf spec H_pin ≥ 167/100,

  while for U ≡ 1 on the same graph, inf spec H_U = 0.
- *Proof.*
  - H_U = Σ_panels |D_Uψ|²_f ≥ Σ_{blocks B} H_U|_B, by dropping the inter-block panels (each term ≥ 0). The blocks partition the tiles, so the right side is ⊕_B H_U|_B.
  - Each H_U|_B is unitarily equivalent to the level-1 free Laplacian of some decoration: rotation invariance plus a relabelling of tiles.
  - For all 6561 decorations, L − (167/100)·I is positive definite. This is certified by exact rational LDLᵀ of the real 32×32 form (`phase6_forced_flux.py`).
  - H_pin = H_U + diag(24 − Deg) ≥ H_U.
  - For U ≡ 1 the constant spinor is a zero mode on finite patches, and E_L → 0 on the infinite tiling (trivial pinned bottoms 1.67, 0.50, 0.14). ∎
- *How sharp it is.*
  - The certified floor is 1.67, against the observed minimum λ_min of 1.6716 over level-1 blocks.
  - Actual bulk floors are much higher: FR30 ∈ [4.008, 8.765] (certified); other rules have pinned level-4 bottoms of 6.1–9.5.
  - The bound is a uniform *existence* statement, not an estimate of E_bulk.

**Counterexamples and failure cases.**
- Identity frames are pure gauge, with zero floor.
- Removing the face twist (V = MᵀM) gives a pure gauge connection.
- The trivial connection has floor 0.
- **Positivity does not need aperiodicity.** The periodic cube substitution with Clifford links has floor 1.85, and i.i.d. random Q8 links give 14.4 — higher than FR30.
- **Positivity does not need non-Abelian structure.** Reflection-only frames M = D_s (improper, so outside Theorem F′'s proof) give a purely Abelian Z₂ (Toulouse-type sign) frustration.
  - Free bottom: 3.28 / 3.32 / 3.32 at levels 2–4.
  - Pinned bottom: 9.03 / 5.13 / 3.82.

**Corollary F″ (the non-Abelian decoration raises the bulk floor) [P + exact arithmetic].**
- *Statement.* inf spec H_∞(FR30) ≥ 4.008189 > 3.8222529 ≥ inf spec H_∞(Z₂ reflection-only).
- *Proof.*
  - The lower bound is V-B's radius-2 certificate, valid under V-B's closure theorem.
  - For the upper bound, H_pin(T₄) is a principal submatrix of the infinite operator, so inf spec H_∞ ≤ E₄.
  - E₄(Z₂) ≤ the exact Rayleigh quotient above.
  - Link rotation invariance (D0) holds for improper frames as well, so Theorem E6 applies to the reflection-only substitution. ∎
- *Meaning.* The octant reflections alone already force (Abelian) frustration. The Q8 permutation decoration of FR30 then raises the infinite-volume floor strictly. This is the one place where the *non-Abelian* structure provably matters for the spectrum.

**Computational test of the predictions.**
- The bound is respected by every computed bottom of every compatible frame field in Phases V-A to V-E: 6561 level-3 bottoms (min Y3 > 6), 264 level-4 classes (min 6.10), all 18 controls (min 7.09), and FR30 at levels 1–7 (min 8.7649).
- With trivial links the bound fails on the same graph, as it must: 0.139 at level 5.

### 7.4 Errors corrected in the audited claim

1. **Wrong citation for the census law.** The census law is not in `phase5b_a_lean_datafree_extract.lean`. That file proves only the generic induction `closed_form_general`, under hypotheses, without census data. The data-bearing certificate is `certificates/TypeSubstitutionCertificate.lean`, and its geometric decomposition lemma is a paper argument.
2. **Wrong citation for spectral gauge invariance.** `audit/phase5c_q8_gauge.py` does not verify spectral gauge invariance. It is a Wilson-action Monte Carlo of a *dynamical* Q8 gauge field that never uses the FR30 links. Spectral invariance is an exact identity, numerically checked elsewhere (§5).
3. **Causal attribution.** The positive floor is "a consequence of nontrivial holonomy" (Lemma K, Theorem F), but not of the *aperiodic* structure: it is local and generic.
4. **"Separates provably from controls" is unsupported.**
   - Trivial links separate qualitatively: floor 0 against floor > 0 (proved).
   - The periodic cube and random-Q8 controls are also gapped. Their separation from FR30 is quantitative and numerical.
   - The Schur recursion is exact, but no compressed RG flow separates FR30 (Phase V-E).
5. **Which operator.** "Soldered covariant Laplacian H_U = D_U†D_U" conflates two operators. The repository's *soldered* Laplacian (`src/chair44/laplacians.py`) is a real O(3)-frame operator without Q8 links. The Q8 operator is H_U = D_U†D_U (free) or 24 − A_U (pinned).
6. **Bounds.** The bracket's ends are a radius-2 collared certificate (not star closure, which gives 1.5687) and exact Rayleigh quotients (not LOBPCG or ChebFSI values).
7. **"Flux-pinned boundary states."** These are free-boundary surface states, with bottoms 5.11 / 5.21 / 5.25 at levels 3–5 below the bulk ≈ 8.76. They are frustration-induced; there is no separate pinning mechanism.

---

## 8. Novelty assessment

| ingredient | closest established theory | assessment |
|---|---|---|
| link variables, Wilson loops, gauge covariance | Wilson, PRD 10, 2445 (1974); Kogut–Susskind | standard |
| H_U = D_U†D_U, zero modes ⇔ trivial holonomy | Kenyon, Ann. Probab. 39, 1983 (2011) (vector-bundle Laplacians); Shubin, CMP 164, 259 (1994) (discrete magnetic Laplacian) | standard (Lemma K is a special case) |
| frustration ⇔ plaquette products ≠ 1; local decomposition lower bounds | Toulouse, Commun. Phys. 2, 115 (1977) (standard citation; not re-verified online); Bandeira–Singer–Spielman, SIAM J. Matrix Anal. Appl. 34, 1611 (2013); Liu–Münch–Peyerimhoff, SIAM J. Discrete Math. 33 (2019) | standard mechanism. The certified *values* are model-specific |
| non-Abelian flux on lattices, Hofstadter "moth" | Osterloh et al., PRL 95, 010403 (2005) | standard model class (here with Q8 flux on an aperiodic graph) |
| tight-binding on aperiodic tilings in fields | Fuchs & Vidal, PRB 94, 205437 (2016) (Rauzy tiling, Abelian field); Damanik–Embree–Gorodetski (Fibonacci) | related; the searches found no SU(2)/Q8 flux on 3D substitution tilings |
| optimal flux | Lieb, PRL 73, 2158 (1994) (flux π per plaquette minimizes energy at half filling) | related question (energy-optimal flux); not used here |
| Kähler–Dirac with links | Becher & Joos, Z. Phys. C 15, 343 (1982) | standard construction; index topological |
| **Clifford face-normal connection U = (σ·Mᵀn)(σ·Mᵀn) and Theorems G1–G3** | spin-connection discretizations in lattice gravity and spinfoams use σ·n factors in different roles | no prior statement of this construction or its corner and lab-gauge structure was found in the searches. It is an elementary but useful structural description, **not a new theory** |
| **Theorem F′ / F (forced flux, uniform floor over all compatible frame fields)** | — | model-specific computer-assisted theorem. To our knowledge new as a statement; modest. It *reduces* the role of aperiodicity rather than establishing a new aperiodic effect |

**Verdict.** The framework is an application of known machinery (lattice gauge fields, connection Laplacians, frustration) to a specific aperiodic geometry, with exact and certified results. It does not yield a new evolution law or a new physical principle. Its distinctive pieces are three:
- the structure of the face-normal soldering (G1–G3);
- forced, decoration-independent frustration with a certified uniform floor (F′, F);
- for FR30, a certified bulk bracket and an exact census law.

---

## 9. Next decisive experiment

**Local determinacy of the bulk floor.**

- *Settled.* Theorem F shows that the *existence* of the gap is local.
- *Open.* Is the *value* E_∞ also determined by finite-radius local data, or does it carry information from arbitrarily deep levels of the hierarchy?
- *Experiment.*
  - Build periodic approximants of the chair tiling that reproduce the FR30 local configurations up to radius R, with the FR30 frames.
  - Compute their bulk floors with Bloch-twisted, gauge-covariant boundary conditions, sweeping the twist.
  - Push the radius-R certified lower bound of Phase V-B (R = 2 gives 4.008) to R = 3 and 4.
- *Decision.*
  - **Local determinacy:** the approximants' floors and the radius-R lower bounds both converge to 8.76 as R grows.
  - **Hierarchy sensitivity** (only aperiodic order can produce): the lower bounds saturate well below 8.76 while the approximants do converge.
- *Why it is the sharpest test.* It decides whether "aperiodic" means anything beyond local frustration for this observable, and it can be phrased as a certified computation.

---

## 10. Publication-ready core

**Title (suggested).** *Forced non-Abelian frustration and a uniform spectral gap for Clifford connections on the chair tiling.*

**Abstract.**
- *Construction.* Each tile of the three-dimensional chair substitution tiling carries a frame M_a ∈ SO(3). Each shared face with normal n carries the link U = (σ·M_aᵀn)(σ·M_bᵀn) ∈ Q8 ⊂ SU(2).
- *Structure.* This Clifford face-normal connection is gauge-equivalent to the frame-transition cochain twisted by the face π-rotations. Its holonomies factor into turning elements at the tiles where loops change direction. Restricted to any single face orientation it is flat.
- *Forced flux.* For every orientation-preserving frame field compatible with the substitution geometry — every substitution rule and every non-self-similar choice — the octant reflections force curvature on every level-1 supertile. So the connection is never pure gauge.
- *Uniform gap.* By an exact decomposition into level-1 blocks and an exhaustive certification over all 6561 local frame choices, the covariant Laplacian D_U†D_U has spectrum bounded below by 167/100 uniformly. With trivial links the bottom is 0.
- *FR30.* For the FR30 rule, the plaquette-holonomy census obeys an exact substitution law (Lean-certified), and the bulk spectral floor is certified in [4.008189, 8.7649120247].
- *Abelian versus non-Abelian.* The octant reflections alone produce an Abelian Z₂ frustration whose bulk floor (≤ 3.8223) lies strictly below FR30's (≥ 4.008).
- *Conclusion.* The gap is a local consequence of the geometry. Periodic and random-flux analogues are also gapped. Aperiodic order and the non-Abelian decoration affect the size of the gap, not its existence.

**Central results.**
- Theorems G1–G3 (structure of the connection).
- Theorem F′ (forced flux, proved).
- Theorem F (uniform floor ≥ 167/100, computer-assisted in exact arithmetic).
- Corollary F″: FR30 > Abelian Z₂ in infinite volume.
- The certified FR30 bracket.

**Limitations.**
1. The quantum content is that of a single particle on a graph with a fixed, non-dynamical gauge field. There is no derivation of quantum mechanics, no dynamical gauge field (the repository's Q8 Monte Carlo is a separate model), no continuum limit, and no Lorentz structure.
2. Theorem F′ needs orientation-preserving frames; the improper case is only sampled. Theorem F is not sharp.
3. The FR30-specific excess over flux-matched rules (Phases V-B to V-E) is numerical and hierarchy-sensitive. It has not been derived.
4. The 6D→3D quasicrystal modules are not connected to this gauge structure. Several of their outputs are calibrated constants rather than computations.
5. Novelty claims rest on the literature searched (§8). The general mechanisms are classical.
