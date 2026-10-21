# Phase V-C — The four-point physics checklist, executed

Branch `claude/phase5c-physics-checklist` (from the Phase V-B head c4fd0bc). All numbers below were computed in this phase by the scripts named, unless marked *[V-B]* (taken from the Phase V-B record, itself independently reproduced). Status tags: **[P]** proved (argument given), **[X]** exact certificate, **[E]** numerical with errors stated, **[U]** unresolved.

## Bottom line

None of the four checks supports the claim that this framework displaces continuum quantum field theory, supersymmetry or string theory. Each check produced a definite answer:

1. **Lorentz violation.** The only massless operator in the program has an isotropic p² term (c² = 14.9561 hopping·a², isotropic to five digits) and an anisotropic p⁴ term (α between −0.30 and −0.14 a², direction-dependent). That is generic lattice behaviour, quantitatively like the simple cubic lattice. Quadratic time-of-flight bounds are satisfied for a ≲ 3×10⁻²⁷ m. The decisive problem is the radiatively induced speed difference δc of order loop factors, and nothing in the model suppresses it.
2. **Chirality and three generations.** The index of D = d_A + d_A* is exactly 2χ(patch) = 2, for any connection, by a counting theorem. Its density in infinite volume is exactly zero. The zero modes and all near-zero modes are surface states of the open patch. There are no bulk chiral zero modes, no count of 3, and no γ₅ in three spatial dimensions.
3. **Dynamical Q₈ gauge theory.** It has the textbook phase structure. A strong-coupling confined phase has an area law and condensed −1 vortices; a weak-coupling deconfined phase has a perimeter law; in 4D they are separated by a first-order transition with hysteresis. The FR30 connection is not an equilibrium configuration at any β: at its own plaquette value its −1 density is five times the thermal value. Dynamics does not select FR30.
4. **Gap under coarse-graining.** The gap survives, and this is proved: 4.008 ≤ E_bulk ≤ 8.770. It is a bulk flux-frustration gap, not a boundary-pinning artefact. But it is a cutoff-scale mass with no free parameter to make it light, so it is not a Higgs-like scale.

## 1. Low-energy dispersion and Lorentz violation

**Operator.** The decorated operator 24 − A_Q8 is gapped (§4), so it has no long-wavelength branch at all; its excitations are massive at the cutoff. The only gapless operator on the tiling is the tile-graph Laplacian with trivial links, L = 24 − A₀ (24 panels per tile). Its lowest Bloch band was computed exactly on FR30 periodic approximants of level k. These are the level-k supertile repeated on 2ᵏΛ₇, with true frames and 24 panels per chair. Fits of ω²(t n̂) = c²t² + c₄t⁴ + c₆t⁶ were made along 49 directions with t ∈ [0.005, 0.08]a⁻¹; the maximum fit residual is 3×10⁻¹¹. Script: `audit/phase5c_dirac.py dispersion`; data: `audit/results/phase5c_dispersion.json`. **[E]**

| approximant | tiles per cell | eigenvalues of the p² tensor D | anisotropy of c² | α = c₄/c² over 49 directions (units a²) |
|---|---|---|---|---|
| k = 1 | 8 | 14.966, 14.966, 14.990 | 0.002 | −0.294 … −0.144, mean −0.205 |
| k = 2 | 64 | 14.9561, 14.9561, 14.9565 | 3×10⁻⁵ | −0.301 … −0.141, mean −0.207 |
| k = 3 | 512 | 14.9561 (×3) | < 10⁻⁵ | −0.301 … −0.141, mean −0.207 |
| simple cubic reference (exact) | 1 | 1 (×3) | 0 | −1/12 … −1/36 |

[[K4]]

**Reading.**

- **p² order.** The emergence of an isotropic c² is a theorem of the cubic symmetry. The hull is SO(3,ℤ)-invariant (Phase V-A), and a rank-2 tensor invariant under the cubic group is scalar. The approximants, which have only a threefold axis, converge to it as the seams become sparse.
- **p⁴ order.** A rank-4 tensor has two cubic invariants, and both appear: α varies by a factor two with direction, exactly as on the cubic lattice. The tiling's aperiodicity does not remove the p⁴ anisotropy.
- **Odd powers.** There is no p³ term, because L(q) is real and ω²(q) = ω²(−q).

**Comparison with time-of-flight bounds.** With E² = c²p²(1 + αp²), the group velocity is v = c(1 + (3/2)αp² + …). Here α < 0, so propagation is subluminal. Matching the standard quadratic parametrization v = c[1 − (3/2)(E/E_QG,2)²] gives E_QG,2 = ħc/(a√|α|). With |α| ≤ 0.30 a², a quadratic bound of order E_QG,2 ≳ 10¹¹ GeV, the published Fermi-LAT order of magnitude for n = 2 (recalled, not re-derived here), requires

  a ≲ ħc / (10¹¹ GeV · 0.55) ≈ 3×10⁻²⁷ m.

A Planck-length spacing (1.6×10⁻³⁵ m) passes this test by eight orders of magnitude. The request's "α < 10⁻¹⁷" mixes two quantities. α is dimensionful (a²). The dimensionless 10⁻¹⁷-type bounds apply to δc = v − c at fixed energy, or to the n = 1 scale E_QG,1 ≳ M_Pl. The model has no n = 1 term, as shown above.

**What actually decides the question [P, literature].** This is a spatial lattice with continuous time. Boosts are broken explicitly, not dynamically. In an interacting theory, loop corrections feed the dimension-6 Lorentz violation computed here into dimension-4 operators (Collins, Perez, Sudarsky, Urrutia, Vucetich, 2004). The result is species-dependent speed shifts δc ~ g²/(16π²), unsuppressed by the cutoff and excluded by many orders of magnitude, unless a symmetry protects them. The Chair44 program contains no such symmetry. Emergent Lorentz invariance "without fine-tuning" is therefore **not** shown and, on present structure, not available. **[U]**

## 2. Chiral index and doubler census

**Complex and operator.** The dual cubical complex of the level-L patch has 0-cells = unit cubes, 1-cells = adjacent cube pairs, 2-cells = 2×2 squares and 3-cells = 2×2×2 blocks of present cubes, all with coefficients ℂ². Transport U(x, μ) is the identity inside a tile and the FR30 Clifford link C_ab across a panel. The covariant coboundary is the standard lattice exterior derivative, and D = d_A + d_A* is odd for Γ = (−1)^degree. Script: `audit/phase5c_dirac.py dirac | lowmodes`; data: `audit/results/phase5c_dirac.json`, `phase5c_dirac_lowmodes_L{2,3}.json`.

**Theorem [P].** For any finite cell complex and any connection, flat or not:

  ind D₊ = dim ker D₊ − dim ker D₊* = dim C^even − dim C^odd = (rank) · χ.

Proof: D₊ is a linear map between finite-dimensional spaces, so rank–nullity gives the identity. Consequences:

- On a contractible patch the index is 2 (ℂ² coefficients, χ = 1), whatever the connection.
- Per unit volume the index density is χ/n → 0. The alternating cell count of any cubical decomposition of ℝ³ has density zero.
- The index cannot produce generations: it is topological, equal to 2, and carried by the boundary.

**Computation [E].** The FR30 connection is curved: ‖d_A²‖ = 2 (holonomy −1 against 1), so this D is not the Dirac operator of a chain complex.

| level | cells (0,1,2,3) | χ | connection | ker D₊ | ker D₋ | index | smallest nonzero \|E\| | bottom of Δ₀ (scalar sector) |
|---|---|---|---|---|---|---|---|---|
| 1 | 56, 120, 84, 19 | 1 | trivial | 2 | 0 | 2 | 0.660 | 0 |
| 1 | | | FR30 | 2 | 0 | 2 | 0.276 | 0.282 |
| 2 | 448, 1152, 984, 279 | 1 | trivial | 2 | 0 | 2 | 0.342 | 0 |
| 2 | | | FR30 | 2 | 0 | 2 | 0.0763 | 0.431 |
| 3 | 3584, 9984, 9264, 2863 | 1 | trivial | 2 | 0 | 2 | 0.173 | 0 |
| 3 | | | FR30 | 2 | 0 | 2 | 0.0130 | 0.464 |

The FR30 near-zero modes shrink much faster than the trivial operator's 1/side law. Their eigenvectors identify them at level 3:

- The two zero modes have 96 % of their weight on the 47 % of cells that touch the patch boundary, with form-degree content 0 and 2 only.
- The next six modes (|E| = 0.0130) have 96–97 % of their weight on boundary cells, with participation about 1/140 to 1/180 of the complex.

These are **surface states of the open patch**, not bulk zero modes. The scalar (degree-0) sector stays gapped (0.46) and is the cube-resolved version of the gapped operator of §4.

**Answers to the checklist.**

- **Uncompensated chiral charge on the FR30 edge states.** No such object exists. Those states are eigenvectors of a degree-0 operator, so all have Γ = +1 trivially. In three spatial dimensions there is no γ₅ and no chiral anomaly: chirality is defined in even spacetime dimension, and the static tiling has no time direction.
- **Three zero-mode branches without doublers.** No. The index is 2 = 2χ and boundary-localized, and the bulk index density is zero. With the trivial connection, the Kähler–Dirac operator on a cubic complex has its known taste structure: 2³ components describe two 2-component tastes. The aperiodic connection does not reduce these to three chiral species. Aperiodicity evades the hypotheses of the Nielsen–Ninomiya theorem, but not its conclusion: the index theorem above is the finite-volume version of the same obstruction. **[P + E]**

## 3. Dynamical Q₈ gauge theory with the Wilson action

**Model.** S[U] = β Σ_p (1 − ½ Re Tr U_p), with U_l ∈ Q₈ ⊂ SU(2). The sampler is an exact heat bath over the 8 group elements, vectorized over sets of links sharing no plaquette. Engine P is periodic Lᵈ with a checkerboard; engine G is a general complex with greedily coloured links. Engine G was used on the FR30 level-4 patch: the dual cubical complex, with links inside a tile frozen to 1 (rigid tiles), 82 944 links (36 864 frozen) and 79 968 plaquettes. Script: `audit/phase5c_q8_gauge.py`; data: `audit/results/phase5c_q8_gauge.json`. **[E]**

**Validation.**

- The two engines agree on the 3D L = 6 torus at β = 0.5, 1, 1.5, 2, 3 within one standard error (e.g. 0.4280 ± 0.0063 against 0.4257 ± 0.0069 at β = 1.5).
- The strong-coupling limit ⟨P⟩ → β/4 is reproduced (0.1247 at β = 0.5).

**Phase structure.**

| system | confined side | transition | deconfined side |
|---|---|---|---|
| 4D, L = 6 | ⟨P⟩ = 0.10 → 0.33 for β = 0.4 → 1.2; −1 density 0.082 → 0.029 | **first order with hysteresis**: the hot-start scan jumps between β = 1.2 and 1.4; the cold-start scan stays ordered down to 1.2 and drops between 1.2 and 1.0 | ⟨P⟩ → 1; −1 density 0 (cold); the hot start freezes into a metastable defect state at ⟨P⟩ ≈ 0.95 |
| 3D, L = 12 | ⟨P⟩ = 0.10 → 0.47 for β = 0.4 → 1.6 | between β = 1.6 and 1.9 (up and down scans agree within errors at the points sampled) | ⟨P⟩ ≥ 0.996 for β ≥ 2.2 |
| FR30 patch (3D, level 4, rigid tiles), inter-tile plaquettes | ⟨P⟩ = 0.103 → 0.566 for β = 0.4 → 1.6; −1 density 0.081 → 0.010 | between β = 1.6 and 2.0 | ⟨P⟩ = 0.972 at β = 2 |

**Wilson loops and Creutz ratios χ(R,T)** (4D L = 8 and 3D L = 16; area law means χ > 0, perimeter law means χ → 0):

| β (4D) | W(1,1) | W(2,2) | χ(2,2) | χ(3,3) |
|---|---|---|---|---|
| 0.8 | 0.206 | 0.0019 | 1.57 | noise |
| 1.2 | 0.332 | 0.0123 | 1.09 | 0.63 |
| 1.6 | 0.993 | 0.975 | 0.005 | −0.01 |
| 2.0 | 0.9998 | 0.9997 | 6.5×10⁻⁶ | 6.5×10⁻⁶ |

| β (3D) | W(1,1) | W(2,2) | χ(2,2) | χ(3,3) |
|---|---|---|---|---|
| 0.8 | 0.206 | 0.0020 | 1.46 | noise |
| 1.6 | 0.471 | 0.051 | 0.72 | 0.78 |
| 2.4 | 0.998 | 0.996 | ≈ 0 | ≈ 0 |

**Answer.** Yes: in the dynamical theory, −1 flux loops condense into an area-law confining regime at strong coupling, and they disappear in a perimeter-law deconfined regime at weak coupling. This is the generic behaviour of discrete-group lattice gauge theories (for Q₈ in 4D, compare Petcher and Weingarten, 1980). It is a property of Q₈ gauge theory on any lattice, not of the tiling: the FR30 patch behaves like the periodic lattice, with the transition shifted slightly by the frozen intra-tile plaquettes and the open boundary.

**Where FR30's connection sits.** Its inter-tile plaquettes have ⟨½ReTr⟩ = 19/36 − 13/144 = 63/144 = 0.4375 and a −1 density of 13/144 = 0.090.

- At the β where the thermal ensemble has the same ⟨P⟩ (β ≈ 1.5 in 3D, confined side), the thermal −1 density is about 0.017: FR30 has five times more.
- At the β where the thermal −1 density is 0.09 (β ≈ 0.35), the thermal ⟨P⟩ is about 0.09, against FR30's 0.44.

So FR30 lies far off the equilibrium curve at every β, a highly structured configuration with excess +1 and −1 plaquettes and a deficit of traceless ones. A Wilson-action path integral does not select or protect it, and its classical minimum is the trivial connection. Making FR30 dynamical would require a different action in which it is a stationary point. No such action is known here. **[E + U]**

## 4. Gap scaling under coarse-graining

Script: `audit/phase5c_gap_scaling.py`; data: `audit/results/phase5c_gap_scaling.{txt,json}`.

| level k | 2 | 3 | 4 | 5 | 6 |
|---|---|---|---|---|---|
| pinned FR30 bottom *[V-B]* | 10.776951 | 9.378470 | 8.919634 | 8.797011 | 8.770134 |
| decrement ratio | | 0.328 | 0.267 | 0.219 | |
| trivial links, same graph *[V-B]* | 4.7512 | 1.6695 | 0.5027 | 0.1386 | 0.0365 |

**Certified [P + X]:** 72147403/18000000 = 4.008189 ≤ E_bulk ≤ 19748585252900893/2251799811448142 = 8.770134. Extrapolations [E]: 8.7626 (geometric), 8.7612 (4⁻ᵏ), 8.7619 (4⁻ᵏ + 8⁻ᵏ). The level-7 run of Phase V-B was stopped at pass 1 and adds nothing (its Ritz value 8.798 is weaker than the level-6 certificate).

**Answer.**

- **The gap is nonzero in the infinite-volume limit, and this is proved.** It approaches a constant near 8.76 in hopping units.
- **It is a bulk flux-frustration gap.** With trivial links the same graph is gapless: the bottoms fall by a factor near 1/4 per level, a 1/side² law with 4ᵏ·bottom converging.
- **It does not come from the Dirichlet pinning.** Pinned and free spectra have the same infinite-volume limit (boundary-independence theorem, Phase V-A). The free patch's lower bottom (5.25) is a surface band.
- **"Boundary pinning survives coarse-graining" is the wrong description.** What survives is a bulk gap of order the hopping, i.e. a mass at the cutoff scale 1/a. The model has no free parameter that could make it parametrically smaller.
- **It is not a Higgs mechanism.** The background is fixed, not a fluctuating field. No effective potential λ(φ² − v²)² is generated, because there is no functional integral over Q₈ configurations in this operator. In the dynamical theory of §3 the FR30 configuration is not even an equilibrium point.

## 5. Phase V-B continuation

The decoration census killed in Phase V-B was resumed. [[CENSUS]]

## 6. What would have to be true for the larger program, stated as obligations

1. A symmetry, or a dynamical mechanism, that protects δc between species at the 10⁻²⁰ level, with a computation.
2. A 3+1-dimensional structure with a time direction and an even-dimensional chirality operator, together with an index theorem whose bulk density is nonzero and equal to 3 (impossible for an index equal to the Euler characteristic of a cell decomposition of ℝ⁴, whose density is also 0).
3. An action in which the FR30 connection is a stationary point and whose fluctuation spectrum contains a massless spin-2 mode.
4. A mechanism producing a scale m ≪ 1/a.

None of these is supported by any computation in this repository. The rigorous mathematics established in Phases V-A to V-C is unaffected: exact recursion, Lean certificate, hull theorems, certified spectral bracket and exact correlation limits.

## 7. Files, tests, commands

New scripts: `audit/phase5c_dirac.py`, `audit/phase5c_q8_gauge.py`, `audit/phase5c_gap_scaling.py`. Results: `audit/results/phase5c_{dispersion,dirac,dirac_lowmodes_L2,dirac_lowmodes_L3,q8_gauge,gap_scaling}.*`. Tests: `tests/test_phase5c.py`. [[TESTS]]

```
python3 -u -I audit/phase5c_dirac.py dispersion 4        # Bloch fits on approximants k=1..4
python3 -u -I audit/phase5c_dirac.py dirac 3             # index and low spectrum, levels 1-3 (about 4 min)
python3 -u -I audit/phase5c_dirac.py lowmodes 3          # localisation of the lowest modes
python3 -u -I audit/phase5c_q8_gauge.py all              # engine check, 4D/3D scans, Wilson loops, FR30 patch (about 5 min)
python3 -u -I audit/phase5c_gap_scaling.py
```
