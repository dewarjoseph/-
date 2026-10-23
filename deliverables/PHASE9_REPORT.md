# Phase IX — The novelty boundary: what explains the FR30 spectral edge, and is its law new?

**Repository state.**
- Branch `claude/phase8-interface-recursion`, from main 585e05a: Phase VIII plus this phase.
- Definitions are those of `deliverables/PHASE7_DEFINITIONS.md`.
- The target throughout is **E_\* = inf σ(H_Y)** for H = 24 − A_U on ℓ²(Y) ⊗ ℂ² and Y in the FR30 hull Ω_FR30. It is the same for every Y, by minimality.
- Finite supertiles enter only as compressions: their bottoms are upper bounds on the floor of their own hull.

**Labels.**

| for | label | meaning |
|---|---|---|
| bounds | rigorous | a proof, or a computer-assisted proof with exact arithmetic or a rigorous rounding bound |
| | fv-certificate | rigorous, but about a finite matrix only |
| | numerical | floating-point evidence |
| | conjectural | rests on an unproved hypothesis |
| claims | [P] [C] [E] [X] [U] | proved, certified, evidence, exploratory, unresolved (as in Phases VII–VIII) |
| novelty | A / B / C / D | standard machinery / new application / model-specific mathematical novelty / potentially new physical principle (Part II) |

---

## 0. Answer

**The question.** What is the smallest mathematically justified piece of information that explains the FR30 spectral edge? And is the law governing it genuinely new, or an exact consequence of established gauge and spectral theory applied to this geometry?

**1. The information is local, and of support type, not frequency type.**
- E_\* is an extremal quantity: the infimum of the energies of legal local patterns. By the localization theorem (Phase VII Thm 7.1, §6 L-A), for every R ≥ 6,

  |D_R − E_\*| ≤ ε(ρ) ≤ K(ρ) S₁/ρ², with ρ = R − 311/175,

  where D_R is the lowest ground-state energy over the legal radius-R balls, K(ρ) → π²/6 and S₁ = 4734/49.
- The constants are geometric, so the statement holds for every decoration with a minimal hull.
- To accuracy ε, the information needed is the **set** of gauge classes of legal radius-R balls, with R ≈ (π² S₁/(6ε))^{1/2}. That set is fixed by the radius-1 local rules. Frequencies and long-range arrangement do not enter.

**2. Frequency-type curvature summaries are provably insufficient** (Theorem 9.1, §8).
- Rules 937 and 938 have the same geometry and hierarchy. They also agree in:
  - plaquette conjugacy-class counts, also split by owner count;
  - two-cycle class counts;
  - spectral moments of order ≤ 3.
- Their supertile bottoms are nevertheless separated, rigorously: by ≥ 0.2776 at level 3 and ≥ 0.2502 at level 4.

**3. Where matched differences come from.** In the pre-registered comparison (§7), the 937/938 edge difference is already carried by the radius-1 environments:
- 74 % on the bare 1-stars;
- 94 % after one inflation, on patches of ≤ 216 tiles.

The null model (local frustration) is supported, and the hierarchy model is falsified for this pair. The non-Abelian FR30-versus-χ₁ difference is local in the same sense (post hoc).

**4. The law is not new.** Every mechanism used is an exact consequence of established theory applied to this geometry: the variational principle (compression), IMS localization, Schur complements and the minimality of the hull.
- The hierarchy's role is to fix which local patterns are legal, through radius-1 matching rules, and to organise upper bounds, through selection chains.
- At equal patch size neither improves on generic legal patches (§7.1).
- The candidate "laws" beyond these are an approximation scheme (the fiber) and a drifting fit (the chain ratio) (§6).
- **No claim reaches category D.**

**5. What is new (provisional, §3):**
- the computed examples (category B): the rigorous enclosure, the certified matched pair and the census structure;
- the radius-1 matching-rule theorem for the FR30 decoration (category C). Its priority against three 2026 preprints on 3D-chair matching rules is unsettled.

**Rigorous enclosure.**
- **E_\* ∈ [7.954292, 8.7642270381]**: both endpoints are computer-assisted proofs, and neither uses an extrapolation (§2).
- The sharper [8.76385, 8.76423] is conjectural.

---

## 1. Phase VIII closed (Part I)

| item | status | result | artifact |
|---|---|---|---|
| level-6 held-out copy-lattice edge, env fiber, d = 114 | done | E_W − E₆ = +0.00205 (Ritz, so ≥ 0) | `phase8_copy_rg.jsonl` |
| level-6 copy-lattice edge, deep(6,7) fiber, d = 58 | done | +0.00112 (in-sample) | same |
| level-7 copy-lattice edges, env and deep(6,7), d = 58 | deep(6,7) done; env in progress at this commit | deep(6,7): +0.00079 (in-sample). env (held-out): in progress | same |
| near-edge density of states, levels 3–5 | done | clustered finite-volume spectrum; no scaling form established [U] | `phase8_dos.json` |
| first poles of R_k, k ≤ 5 | done | λ_II(k) − E_k = 6.66, 0.576, 0.0289, 0.0022 | `phase8_poles.json` |
| selection-chain and supertile extrapolations | relabelled | conjectural: they rest on unproved ratio hypotheses (§2) | `phase8_patch_bounds.json` |
| 12 Phase VIII tests | done | 12 passed (31 s) | `tests/test_phase8.py` |
| report and ledger | completed | no blank remains except as stated in this table | `PHASE8_REPORT.md`, `phase8_ledger.json` |

**Regeneration.** Every number quoted in the Phase VIII and IX reports is produced by a committed script from committed inputs, with one exception.
- The exception is the level-7 V-E eigenvector `phase5e_fr30_level7_lowest4.npy` (268 MB, git-ignored). It is regenerated by V-E's level-7 run, which takes about 6.8 h.
- It feeds only the level-7 parts of `phase8_env_fiber.py` and the `geo`/`fiber` diagnostics.
- Both fibers used by the copy lattice are cached in the tracked `phase8_fibers_k3.npz`.

---

## 2. The bound audit

**The two endpoints of E_\* ∈ [7.954292, 8.7642270381], separately.**

| endpoint | label | what it is | what it depends on | what it does not depend on |
|---|---|---|---|---|
| **7.954292** = Λ₁₂ (exact rational in `phase7_ims.json`) | **rigorous**, infinite volume | an IMS-localization lower bound, E(Y) ≥ Λ₁₂ for **every** Y with legal 12-stars (Phase VII Thm 7.1(a)) | (i) Thm 7.1, an exact identity with explicit overlap function; (ii) Thm 6.2, 𝒯₁ = Ω_FR30, a computer-assisted proof; (iii) completeness of the enumeration of the 2315 legal 12-balls; (iv) a floating Cholesky with Higham's Thm 10.3 rounding bound, and amplification factors in interval arithmetic | any extrapolation. *Caveat:* at R = 12 the enumeration has a single implementation; two independent implementations agree at R = 6 and 8 |
| **8.7642270381** = 95969095435322528/10950092349041091 | **rigorous**, infinite volume | a variational upper bound: the exact rational Rayleigh quotient of an integer vector supported on the legal patch σ⁵(τ₅₉) (884 736 tiles) | (i) the pinned patch operator is the compression P H_Y P (definitions §5); (ii) σ⁵(τ₅₉) occurs in Ω_FR30: τ₅₉ occurs in FR30 supertiles, and σ maps occurring patches to occurring patches; (iii) minimality; (iv) H has Gaussian-integer entries (link table ⊂ {−1, 0, 1}, verified here), so the arithmetic is exact | any ratio or extrapolation hypothesis |

**Answers to the audit questions.**
- *Lower endpoint.* A rigorous infinite-volume lower bound. It is a localization estimate, but it has no unverified assumptions: its constants are explicit and certified. It is not a finite-volume result.
- *Upper endpoint.* A single certified Rayleigh quotient on one legal finite patch, which bounds the infinite-volume infimum by the variational principle. It is not an extrapolation, and it does not depend on any ratio hypothesis.
- *Same quantity.* Yes. Both bound inf σ(H_Y) for Y ∈ Ω_FR30, with the same operator and normalisation. Thm 7.1 covers every Y ∈ 𝒯₁₂, and 𝒯₁₂ = Ω_FR30 by Thm 6.2. The upper bound covers the hull element containing the patch, hence every element, by minimality.
- **Verdict.** [7.954292, 8.7642270381] is a rigorous two-sided enclosure: both endpoints are computer-assisted proofs.

**Every other quoted number, with one label each** (also in `phase9_ledger.json`):

| number | label | note |
|---|---|---|
| E_\* ≤ 8.7649120247 (T₇), ≤ 8.7662710593 (σ⁴(τ₃₉)) | rigorous | superseded by 8.7642270381 |
| 8.764911988 = λ_min(H_pin(T₇)) | numerical | residual 1.0·10⁻⁸; its certificate bounds the same finite matrix from above |
| 8.7642270377 = λ_min(H\|σ⁵(τ₅₉)) | numerical | residual 5·10⁻¹² |
| λ_min(H_pin(T₃)) ∈ [8.4910240, 8.4910257] (rule 937), [8.2134323, 8.2134341] (rule 938) | fv-certificate | §4 |
| λ_min(H_pin(T₄)) ∈ [8.0357080, 8.0357096] (rule 937), [7.7854810, 7.7854826] (rule 938) | fv-certificate | §4 |
| E_\* ∈ [8.76385, 8.76423] | **conjectural** | holds if every later chain decrement ratio is ≤ 0.1541 |
| E_\* ≈ 8.7631–8.7637 (V-E) | **conjectural** | last-ratio tails of the pinned supertiles |
| "E_\* ≈ 8.764" | numerical | a rounded value inside the rigorous enclosure; not a bound |

---

## 3. The novelty boundary (Part II)

**Categories.**
- **A**: follows from established discrete gauge theory, connection Laplacians, Schur complements, spectral theory or substitution dynamics.
- **B**: standard machinery applied to Chair44, giving a new computed example but no new general theorem.
- **C**: a proved model-specific geometric, combinatorial or spectral theorem not found in the prior literature.
- **D**: a law with a defined observable and predictive content that survives appropriate controls.

**The novelty assessment is provisional.** The search covered:
- about 60 web searches;
- arXiv and publisher pages, and Crossref;
- 6 Consensus queries.

It did not cover MathSciNet, zbMATH or Google Scholar. Several paywalled full texts were not read. References are listed at the end of this section.

| # | claim (exact statement) | cat. | proof or evidence | prior theory | smallest remaining gap |
|---|---|---|---|---|---|
| 1 | The child→parent Schur recursion R_{m+1}(E) = 𝓡_E(R_m(E)) is exact, Loewner monotone, concave and gauge covariant (Phase VIII Prop. 8.1) | **A** | proof; tests | inertia additivity [R7]; Schur complement extremal characterisation [R8]; spectral decimation [R9, R10]; a Schur-formula RG on the octagonal tiling [R14]; gauge-covariant U(1) decimation [R12] | None as mathematics. No prior use on an SU(2)/Q₈ connection over a substitution tiling was found |
| 2 | U_m(τ) is a functional of R_m; along every Φ-self-loop it decreases to E_\*; the first poles of R_k decrease to E_\* (Thms 8.2–8.3, Prop. 8.4) | **A** | proofs (interlacing, exhaustion, minimality) | min–max principle; constancy of the spectrum on minimal hulls [R15]; Schur reductions and their spectra [R13, R11] | — |
| 3 | E_\* ∈ [7.954292, 8.7642270381], rigorous (§2) | **B** | computer-assisted | IMS localization [R23]; rigorous patch bounds for scalar and U(1) quasicrystal operators [R16] | width 0.81; the lower side converges as O(R⁻²) |
| 4 | Over the 72 legal 1-star types, U_m is minimised by the self-loop pair τ₅₉/τ₆₃ at m = 1–3, with a four-way tie to 3·10⁻¹⁰ at m = 4 | **B** [C, E] | exhaustive computation over types | — | selection for all m is unproved |
| 5 | The FR30 frame decoration is itself a radius-1 matching rule, 𝒯₁ = Ω_FR30 (Phase VII Thm 6.2) | **C, provisional** | computer-assisted proof | general local-rules theorems [R17, R18]; three unrefereed 2026 preprints on 3D-chair matching rules [R19] | priority against [R19], not read in full |
| 6 | Every compatible frame field is curved, with a uniform gap (Phase VII) | **C, provisional** | Phase VII proofs | flux-phase theorems [R5, R6]; frustration index and Cheeger bounds [R2, R3] | no non-Abelian optimal-flux theorem was found to compare with |
| 7 | Theorem 9.1: class counts do not determine the spectral bottom (937/938) | **B** | exact counts and moments; certified enclosures (§4, §8) | cospectral but non-switching-equivalent gain graphs, and closed-walk gains [R22]; trace invariants determine the connection up to gauge [R20, R21] | infinite-volume separation of the two floors is not certified |
| 8 | The 6561 proper decorations form 1125 S₃-orbits and 1098 gauge classes. The level-3 spectrum separates all classes; class counts separate all but the 937/938 pair (§5) | **B** | computation | switching equivalence via closed-walk gains [R22] | level 3 only |
| 9 | tr Aᵖ is the sum of holonomy traces over closed walks; for 937/938 the first differing order is p = 4 (§4) | **A** (identity), **B** (value) | exact integer arithmetic | [R4], [R1] | — |
| 10 | Environment-selected fiber: held-out copy-lattice edges within +0.002 to +0.0085 at level 6 | **B** [E] | numerical; Ritz upper bounds | spectral decimation and RG [R9, R14] | no error bound beyond the one-sided Ritz property |
| 11 | Seam-bound edge states; clustered near-edge spectrum | **B** [E] | numerical, finite volume | — | infinite-volume nature unknown |
| 12 | Chain decrement ratio r ≈ 0.15–0.17 | **X** (phenomenological) | four ratios | — | not derived, and drifting |
| 13 | a hierarchy-specific spectral law | **D: not established** | §6–§7 | — | — |

**No claim reaches D.** The literature search found no paper combining substitution tilings, non-Abelian (SU(2)/Q₈) lattice connections and spectral edges. It also found no spectral-theory paper on chair tilings in two or three dimensions. That is why rows 1, 3 and 7–11 read "new application" rather than "known".

**References** (verification: F full text, A abstract or publisher page, S secondary sources only, B bibliographic data only).
- [R1] Kenyon, *Spanning forests and the vector bundle Laplacian*, Ann. Probab. 39 (2011) 1983–2017, doi:10.1214/10-AOP596 [F].
- [R2] Bandeira, Singer, Spielman, *A Cheeger inequality for the graph connection Laplacian*, SIAM J. Matrix Anal. Appl. 34 (2013) 1611–1630, doi:10.1137/120875338 [F].
- [R3] Lange, Liu, Peyerimhoff, Post, *Frustration index and Cheeger inequalities for discrete and continuous magnetic Laplacians*, Calc. Var. PDE 54 (2015) 4165–4196, doi:10.1007/s00526-015-0935-x [F].
- [R4] Cavaleri, D'Angeli, Donno, *A group representation approach to balance of gain graphs*, J. Algebr. Comb. 54 (2021) 265–293, doi:10.1007/s10801-020-00977-w [A].
- [R5] Lieb, *The flux phase of the half-filled band*, Phys. Rev. Lett. 73 (1994) 2158, doi:10.1103/PhysRevLett.73.2158 [F].
- [R6] Lieb, Loss, *Fluxes, Laplacians, and Kasteleyn's theorem*, Duke Math. J. 71 (1993) 337–363, doi:10.1215/S0012-7094-93-07114-1 [F].
- [R7] Haynsworth, *Determination of the inertia of a partitioned Hermitian matrix*, Linear Algebra Appl. 1 (1968) 73–81, doi:10.1016/0024-3795(68)90050-5 [S].
- [R8] Li, Mathias, *Extremal characterizations of the Schur complement and resulting inequalities*, SIAM Rev. 42 (2000) 233–246, doi:10.1137/S0036144599337290 [A]. Also Anderson, Trapp, *Shorted operators II*, SIAM J. Appl. Math. 28 (1975) 60–71 [S].
- [R9] Malozemov, Teplyaev, *Self-similarity, operators and dynamics*, Math. Phys. Anal. Geom. 6 (2003) 201–218, doi:10.1023/A:1024931603110 [S].
- [R10] Sabot, *Spectral properties of self-similar lattices and iteration of rational maps*, Mém. SMF 92 (2003), doi:10.24033/msmf.405 [F, partial].
- [R11] Krön, *Green functions on self-similar graphs and bounds for the spectrum of the Laplacian*, Ann. Inst. Fourier 52 (2002) 1875–1900, doi:10.5802/aif.1937 [A].
- [R12] Chen, Guo, *Spectral decimation of the magnetic Laplacian on the Sierpinski gasket*, Commun. Math. Phys. 380 (2020) 187–243, doi:10.1007/s00220-020-03850-w [A].
- [R13] Bunimovich, Webb, *Isospectral graph transformations, spectral equivalence, and global stability of dynamical networks*, Nonlinearity 25 (2012) 211–254, doi:10.1088/0951-7715/25/1/211 [A].
- [R14] Sire, Bellissard, *Renormalization group for the octagonal quasi-periodic tiling*, Europhys. Lett. 11 (1990) 439–443, doi:10.1209/0295-5075/11/5/009 [A].
- [R15] Lenz, Stollmann, *Delone dynamical systems and associated random operators*, arXiv:math-ph/0202042 [F]; and J. Anal. Math. 97 (2005) 1–24, doi:10.1007/BF02807400 [A].
- [R16] Hege, Moscolari, Teufel, *Finding spectral gaps in quasicrystals*, Phys. Rev. B 106 (2022) 155140, doi:10.1103/PhysRevB.106.155140 [F, partial].
- [R17] Mozes, *Tilings, substitution systems and dynamical systems generated by them*, J. Anal. Math. 53 (1989) 139–186, doi:10.1007/BF02793412 [A].
- [R18] Goodman-Strauss, *Matching rules and substitution tilings*, Ann. of Math. 147 (1998) 181–223, doi:10.2307/120988 [A].
- [R19] Tsiokos, arXiv:2609.19214; Flicker, arXiv:2609.23783; Kamenetsky, arXiv:2610.00916. All three are 2026 and unrefereed, on matching rules for the 3D chair [A / F, partial].
- [R20] Giles, *Reconstruction of gauge potentials from Wilson loops*, Phys. Rev. D 24 (1981) 2160–2168, doi:10.1103/PhysRevD.24.2160 [S].
- [R21] Procesi, *The invariant theory of n×n matrices*, Adv. Math. 19 (1976) 306–381, doi:10.1016/0001-8708(76)90027-X [S].
- [R22] Cavaleri, Donno, *On cospectrality of gain graphs*, Spec. Matrices 10 (2022) 343–365, doi:10.1515/spma-2022-0169 [A].
- [R23] Cycon, Froese, Kirsch, Simon, *Schrödinger Operators*, Springer (1987), Thm 3.2 (IMS) [S].

---

## 4. Rules 937 and 938 (Part III)

Everything below is recomputed by `audit/phase9_pair.py`, which builds tiles, panels, links (by the Pauli formula), plaquettes and the operator from `PHASE7_DEFINITIONS.md`. It shares no code with the census except the index → decoration map. That map is re-derived and checked against the census map, and the level-3 to level-5 bottoms reproduce the census values to 10⁻¹².

### 4.1 What the two rules are [exact]

**One substitution choice.** A decoration chooses one of 3 proper frames for each of the 8 children; census digit 0 is the centre child. Rules 937 and 938 **differ only in the centre child**:
- 937 has π₀ = (1,2,0) and 938 has π₀ = (2,0,1).
- These are the rotations by +120° and −120° about the chair's symmetry axis (1,1,1).
- The seven octant children are identical.
- The same rule is applied at every substitution step, so the difference recurs at every level of the hierarchy.

**Same geometry.** The chairs are identical. After tiles are matched by their cube sets, the panel lists coincide. The frames differ on 14 % of the tiles.

**The four possibilities in the brief.**

| possibility | answer | how it is decided |
|---|---|---|
| related by a symmetry, relabelling or orientation reversal | **no** | Any such relation preserves the spectrum, and the certified level-3 bottoms differ (§4.2). Directly: S₃ acts on decorations by G ↦ QGQᵀ, T ↦ QT; an improper Q acts on the operator by complex conjugation, so spectra are preserved. orbit(937) = {937, 1190, 3943, 4142, 4502, 4951} and orbit(938) = {938, 1189, 3944, 4141, 4501, 4952} are different orbits, and they are exactly the census's two families with Y₃ = 8.4910 and 8.2134 |
| distinct under the permitted gauge transformations | **yes** | The tree-gauge holonomies (BFS tree from tile 0, tiles matched by cube sets) are not related by any global conjugation in the binary octahedral group, the normaliser of Q₈ in SU(2). The spectra differ in any case |
| equivalent in local geometry but distinct in link correlations | **yes** | Same chairs, panels and plaquettes. Their counts agree class by class, but their arrangements differ (§4.2) |
| another feature explains the difference | a single substitution choice | The chirality of the centre child's rotation, repeated at every level. §4.5 locates where in the hierarchy it acts |

### 4.2 Exact comparison table

| statistic | gauge status | level 3 | level 4 | level 5 |
|---|---|---|---|---|
| tiles / panels | geometric | 512 / 5 376 | 4 096 / 46 080 | 32 768 / 380 928 |
| plaquettes (lattice-edge 4-cycles with ≥ 2 owners) | geometric | 7 728 | 67 680 | 565 440 |
| plaquette class counts (+1, −1, i, j, k) | Q₈-gauge invariant; the axis split is not SU(2)-invariant | **equal**: 4072, 467, 1239, 802, 1148 | **equal**: 35912, 4551, 10253, 6794, 10170 | **equal** |
| the same counts split by number of owners (2, 3, 4) | invariant | **equal** in every split | — | — |
| plaquettes whose **trace** differs (W = 1, W = −1, or traceless) | SU(2)-invariant field | 1 116 (14.4 %) | 8 908 (13.2 %) | 71 280 (12.6 %) |
| plaquettes whose class differs (including the i/j/k axis) | Q₈-invariant field | 2 058 (27 %) | 16 443 (24 %) | 131 583 (23 %) |
| the trace field of 938 as an axis-permuted image of 937's | — | no: the best of the 6 permutations is the identity, 86 % agreement | no (87 %) | — |
| two-cycles (tile pairs sharing panels with two normals): class counts | invariant | **equal**: 216, 192, 375, 375, 375 | **equal** | **equal** |
| two-cycles whose trace differs | SU(2)-invariant field | 756 (49 %) | 6 036 (49 %) | 48 288 (49 %) |
| two-cycles whose class differs | Q₈-invariant field | 1 464 (95 %) | 11 703 (95 %) | 93 645 (95 %) |
| spectral moments tr Aᵖ, A = 24 − H | unitary invariant | **equal for p = 1, 2, 3**; first difference at p = 4 (§4.4) | — | — |
| finite-volume spectral measure | unitary invariant | same mean; Kolmogorov distance 0.0098 | — | — |
| lowest Kramers pairs | unitary invariant | 937: 8.4910, 8.6395, 8.8992, then 9.5619. 938: 8.2134, 8.3163, 8.4905, then 9.4047 | — | — |
| **Y_L = λ_min(H_pin(T_L))** | unitary invariant | **8.4910257 vs 8.2134341**: certified enclosures [8.4910240, 8.4910257] and [8.2134323, 8.2134341], **separation ≥ 0.27759** [C] | **8.0357096 vs 7.7854826**: certified [8.0357080, 8.0357096] and [7.7854810, 7.7854826], **separation ≥ 0.25023** [C] | 7.9728402 vs 7.7285379 (Δ 0.2443) [E] |
| surface response R₂(E): softest pairs at E = 6 | unitarily covariant | 937: 5.861, 6.179, 6.920, 7.261. 938: 5.771, 6.171, 6.582, 7.594. Traces **equal** | — | — |
| surface response R₃(E) at E = 6 / 8 | same | traces differ by 0.417 / 5.30 | — | — |
| level-5 edge eigenvector | unitary invariant | — | — | 937: depth-1 seam weight 0.53, IPR·n 120, child weights 0.33 (the centre child) and 0.65 (child 1). 938: seam weight 0.33, IPR·n 93, child weights 0.19 and 0.80 |

Certificates:
- the upper ends are exact rational Rayleigh quotients;
- the lower ends come from a floating Cholesky of the real form of H − μ, with μ a 20-bit dyadic, and Higham's Thm 10.3 rounding bound (the routine of Phase VII);
- `tests/test_phase9.py` recomputes both.

### 4.3 What is gauge-invariant, and what is an artifact

**SU(2)-gauge invariant (and so meaningful for the spectrum):**
- the trace class of every closed-walk holonomy (W = 1, W = −1, or traceless);
- all spectral moments and spectra;
- the spectra of R_m(E).

**Q₈-gauge invariant only:** the axis label i, j or k of a traceless holonomy.
- An SU(2) gauge transformation can rotate the axes.
- The census's axis-resolved counts n_i, n_j, n_k are of this kind. S₃ permutes them.

**Coordinate artifact:** V-B's 2×1-loop fractions (`loop21_f_m1`, `loop21_f_trl`) are not constant on S₃-orbits. Their definition depends on orientation, so they are not invariants of the decorated tiling. All other V-B statistics are constant on the 937 orbit.

### 4.4 The smallest invariant that distinguishes them, and why it does not explain the edge [P + C]

**The first difference is at order 4.** The exact integer moments of A = 24 − H at level 3 (`phase9_moments.json`) are:

| p | 1 | 2 | 3 | 4 | 5 | 6 | 12 |
|---|---|---|---|---|---|---|---|
| tr Aᵖ (937) − tr Aᵖ (938) | 0 | 0 | 0 | **+2 976** | −438 840 | −5 773 824 | −3.47·10¹⁴ |

tr A⁴ is a sum of holonomy traces over closed walks of length 4. Split by the pattern of the walk a → b → c → d → a (`phase9_loops.json`):

| pattern | 937 | 938 | difference | kind of information |
|---|---|---|---|---|
| a = c, b = d (two tiles) | 668 944 | 668 944 | 0 | squares of two-cycle classes |
| a = c, b ≠ d, and the rotated pattern (two pair-blocks at one tile; counted twice) | 2 952 104 | 2 953 640 | **2 × (−1 536)** | **Abelian.** B_ab B_ab† is a scalar matrix whose value is fixed by the two-cycle traces, so this term measures how two-cycle traces *co-occur at a tile* |
| all four tiles distinct | 227 136 | 221 088 | **+6 048** | traces of tile 4-cycles. These are products of panel links around one or several lattice edges, including loops that are not single plaquettes |
| total | 6 800 288 | 6 797 312 | **+2 976** | |

**The smallest distinguishing invariant** is therefore the fourth spectral moment of the finite-volume spectral measure. It consists of a co-occurrence term for two-cycle traces and a tile-4-cycle holonomy term. Every simpler candidate tested agrees between the two rules:
- the class counts, overall and split by number of owners;
- the two-cycle counts;
- the moments of order ≤ 3.

**It does not explain the edge.**
- **Wrong sign.** The fourth moment is larger for 937, but 937 has the *higher* bottom, i.e. the smaller largest eigenvalue of A. The moments favour 938 only from p = 5 on.
- **Long walks carry the gap.** Write l_p = (1/p) log(tr A₉₃₈ᵖ / tr A₉₃₇ᵖ). As p → ∞ this tends to log(λ_max ratio) = 0.0177. It reaches 50 % of that value at p ≈ 16, 81 % at p = 32 and 93 % at p = 48 (level 3).
  - So the edge difference is carried by closed walks of length ≳ 16, comparable to the diameter of T₃.
  - No statistic of bounded loop length explains it. This is the moment problem: finitely many moments do not fix an extreme eigenvalue.

### 4.5 Where in the hierarchy the difference acts [exact construction, E]

**The construction.** The centre-child choice can be made separately at each substitution step: step 1 creates the depth-1 children of the root, step L the individual tiles.
- Links depend only on relative frames. So the link across a seam that separates two subtrees at depth k depends only on the choices at steps k, …, L.
- The choice at step j therefore acts only on links across seams of depth ≤ j.
  - Step 1 acts only on the depth-1 seams: the mid-planes, where the edge states live.
  - Step L acts on every link that touches a centre-child tile. That is the local frame arrangement, everywhere.

All 2^L sequences were computed for L = 3, 4, 5 (`phase9_steps.json`):

| L | 937 → 938 | flip only the finest step | flip a single coarser step | main effect of the finest step | largest main effect of a coarser step |
|---|---|---|---|---|---|
| 3 | −0.2776 | **−0.3212** | −0.016 to −0.007 | **−0.2900** | 0.0139 |
| 4 | −0.2502 | **−0.2622** | −0.009 to −0.0006 | **−0.2513** | 0.0011 |
| 5 | −0.2443 | **−0.2564** | −0.003 to +0.007 | **−0.2489** | 0.0041 |

**The whole difference is produced by the choice at the last substitution step**, i.e. by the frame of each tile relative to its own level-1 parent.
- Choices at the coarse steps change only the large-scale seams. They move the bottom by less than 0.016, at most 3 % of the difference at L4 and L5.
- This holds even though the 937 edge state straddles exactly the seam that the step-1 choice changes: the seam between the centre child and child 1 (§4.2).

Together with the ladder of §7 (74 % of the difference on the bare 1-stars, 94 % after one inflation), this places the matched pair's spectral difference in the **radius-1 arrangement of frustration**.

*Caveats.*
- Step-mixed sequences are finite-volume constructions, not substitution rules with a hull.
- Some of them change the class counts: there are 3 distinct count vectors among the 8 sequences at L3, and 5 among the 16 at L4.

---

## 5. The minimal predictive state (Part IV)

**Two properties, tested separately.**
- *Predictive sufficiency:* does the summary predict the spectral bottom of decorations it has not seen?
- *Renormalization closure:* is the summary at level m + 1 a function of the summary at level m?

**Data.** The complete census of the 3⁸ = 6561 proper decorations (`phase5b_sweep.json`, Phase V-B):
- Y₃ for all of them;
- Y₄ for the 296 decorations of the pre-registered sample that have a stored level-4 value;
- 45 level-4 plaquette statistics.

New here (`audit/phase9_state.py`, `phase9_state.json`):
- **Equivalence classes.** The S₃ of rigid axis permutations acts on decorations. There are 1125 orbits: 1076 of size 6, 8 of size 3, 40 of size 2 and 1 fixed point.
  - Fourteen sets of orbits are isospectral at level 3, and every one of them is **gauge-equivalent**: the tree-gauge holonomies agree, after matching tiles by their cube sets.
  - So the census has **1098 gauge classes**, and the level-3 spectrum separates all of them. No isospectral but inequivalent pair occurs.
- **Grouped validation.** Every held-out evaluation holds out whole gauge classes, so that no copy of a test decoration sits in a training fold.
  - Phase V-B's folds were not grouped. For its linear models this changes nothing: the class-fraction OLS has RMSE 0.242 either way.
  - A flexible model is badly inflated without grouping. k-nearest-neighbour regression on the same two features gives 0.060 (R² 0.99) ungrouped against 0.319 grouped: it simply finds the symmetric copies.
- **New local spectral summaries** for every class: Y₁ and Y₂ (the pinned level-1 and level-2 supertiles), and the four softest Kramers pairs of the level-2 surface response R₂(E₀) at E₀ = 6.

**Results** (10-fold cross-validation grouped by gauge class; OLS and 5-nearest-neighbour regression; FR30 held out entirely and predicted from all other classes; sd(Y₃) = 0.536, sd(Y₄) = 0.560):

| summary | exact collisions with different Y₃ | Y₃ CV-RMSE: OLS (R²) / kNN | Y₄ CV-RMSE: OLS (R²) / kNN | FR30 Y₃ = 9.378, predicted OLS / kNN | FR30 Y₄ = 8.920, predicted OLS / kNN |
|---|---|---|---|---|---|
| class fractions f₋₁, f_trl | **1** (the 937/938 classes) | 0.242 (0.80) / 0.319 | 0.264 (0.77) / 0.347 | 8.74 / 8.41 | 8.11 / 8.20 |
| + 2×1 and 2×2 Wilson-loop fractions | 0 | 0.217 (0.84) / 0.321 | 0.242 (0.81) / 0.337 | 8.93 / 8.64 | 8.24 / 8.07 |
| + all 41 local correlation statistics | 0 | **0.198 (0.86)** / 0.325 | **0.198 (0.87)** / 0.309 | 8.89 / 9.23 | 8.19 / 8.84 |
| local spectra Y₁, Y₂ | 0 | 0.284 (0.72) / 0.403 | 0.308 (0.69) / 0.332 | 8.29 / 9.06 | 7.63 / 7.59 |
| surface response R₂(6), 4 pairs | 0 | 0.299 (0.69) / 0.416 | 0.333 (0.64) / 0.364 | 8.43 / 9.23 | 7.96 / 7.88 |
| Y₁, Y₂ + class fractions | 0 | 0.235 (0.81) / 0.339 | 0.250 (0.80) / 0.302 | 8.62 / 8.46 | 7.96 / 7.74 |
| R₂(6) + class fractions | 0 | 0.238 (0.80) / 0.359 | 0.232 (0.83) / 0.324 | 8.76 / 8.98 | 8.33 / 7.74 |

**Reading the table.**
- **No summary predicts to better than about 0.2 on unseen classes.** That is 37 % of the census spread (sd 0.54), and comparable to the whole 937/938 gap (0.24).
  - The best summary is the full set of local correlation statistics, linear model: 0.198.
- **FR30 is underpredicted by every summary, by 0.15 to 1.33.**
  - FR30 is extreme: only 0.8 % of decorations have a higher Y₃, and 1 % of the sample a higher Y₄.
  - So the census-trained local models regress it toward the mean. Its edge is not explained by its local statistics as a typical member.
- **"No collision" is not sufficiency.**
  - Y₂ alone has no collision: it separates all 1098 classes, so Y₃ is a function of Y₂ by lookup. Yet as a predictor it is among the worst (0.28–0.40).
  - Injectivity on a finite family says nothing about prediction.
- **The loop and correlation statistics contain a coordinate artifact.**
  - V-B's 2×1-loop fractions are not constant on S₃-orbits; they depend on orientation. That is why these summaries take 6429 values on 1098 classes.
  - The axis-resolved counts n_i, n_j, n_k are Q₈-gauge invariant but not SU(2)-gauge invariant, and are permuted by S₃. They were excluded from every summary above.

**Renormalization closure.**

| summary | closes from level m to m + 1? | sufficient for the spectral bottom? |
|---|---|---|
| plaquette class counts | **yes, on the census**: level-3 counts determine level-4 counts across all 1125 orbits (1097 distinct level-3 vectors, none with two level-4 images; `phase9_count_closure.json`). Exactly, counts of local patch types evolve linearly under the substitution matrix, and class counts are linear functions of them | **no**: the 937/938 counterexample (§4, Theorem 9.1) |
| Y_L (the bottom itself) | **no**: of 378 distinct Y₁ values, 364 are shared by decorations with different Y₂ | not a summary of the parent |
| local correlation statistics | linear in patch-type counts, so they close in the same way as the counts | **no collision, but not predictive** (RMSE 0.2) |
| environment-selected fiber (FR30 only) | approximately: the converged T₃ fiber is stable from level 6 to level 7 (Phase VIII §4c) | to +0.0085 / +0.0021 at level 6 (d = 58 / 114), level 7 in progress at this commit; one-sided (Ritz) |
| exact labelled response R_m(E) | **yes, exactly** (Prop. 8.1) | **yes, exactly**; its dimension grows like 4ᵐ |

**Conclusion of Part IV.**
- Within this model class, every bounded-size summary tested is either closed but insufficient (counts), or not closed and insufficient (scalar bottoms, local spectra). Each is predictive only to about 0.2.
- The objects that are both closed and sufficient are the exact response, which grows, and its numerical fiber truncation, which closes only approximately and is FR30-specific.
- No finite-dimensional, gauge-invariant state with a rigorous error bound was found. Nor was the class of finite summaries proved insufficient in general: the obstruction is the explicit counterexample of §4 for the class-count family, together with the moment argument of §4.4 for any bounded-length loop family.

---

## 6. Is the edge selected by a new law? (Part V)

**The target quantity, kept distinct from its relatives.**

| quantity | definition | relation to E_\* |
|---|---|---|
| **E_\*** | inf σ(H_Y), Y ∈ Ω_FR30, infinite volume | the target |
| Y_L = E_L | λ_min of the *pinned* supertile, i.e. the compression of H_Y to T_L | E_L ≥ E_\* and E_L ↓ E_\* |
| U_m(τ) | λ_min of the compression to the legal patch σᵐ(τ) | ≥ E_\*, and ↓ E_\* along self-loops |
| bulk band edge | not defined: the spectral type near E_\* is unknown | not used |
| boundary-localised eigenvalues | the *free* (Neumann) supertile operator has a surface band near 5.25 with vanishing density (Phase V-A) | **not** E_\*. Pinning removes it: the level-7 edge state has weight 10⁻⁶ on the outer wall |

**Candidate laws.** A law must state its inputs, form, domain, error and held-out predictions, and name controls it should fail if the hierarchy matters.

| | L-A: localization (support) law | L-B: selection-chain law | L-C: environment-fiber law | L-D: local-statistics law |
|---|---|---|---|---|
| inputs | the set of gauge classes of legal radius-R balls, fixed by the radius-1 local rules | the 72 legal 1-star types and σ | low states of the 72 patches σ³(τ) (≤ 13 824 tiles) and a fiber dimension d | the 41 local curvature statistics, or the class fractions |
| form | E_\* ∈ [Λ_R, D_R], with D_R − Λ_R ≤ ε(ρ) ≤ K(ρ) S₁/ρ², ρ = R − 311/175 | E_\* = lim_m U_m(τ₅₉); U_m − E_\* ≈ C rᵐ, r ≈ 0.16 | E_L ≈ the root of λ_min[I ⊗ m(E) + Off_W] on the level-L copy lattice | Y_L ≈ a linear or kNN function of the statistics |
| domain | any decoration with a minimal hull: the proof uses only legality, minimality and geometric constants | FR30 | FR30 pinned supertiles, L ≥ 4 | all 6561 decorations |
| error | **rigorous**, O(R⁻²); ε(12) = 1.51 | upper side rigorous; the rate is a fit | one-sided (Ritz) plus measured | grouped CV-RMSE ≈ 0.2 |
| held-out prediction | none needed: it is a theorem | U₅ predicted from U₁…U₄ = 8.7641066; actual 8.7642270, **error −1.2·10⁻⁴** (the ratio drifted from 0.163 to 0.154) | E₆: **+0.0085** (d = 58), **+0.0021** (d = 114). E₇ (d = 58): in progress at this commit | FR30's Y₃/Y₄ underpredicted by 0.15–1.33 |
| strongest simple baseline | — | generic legal balls of equal size: D₁₂ = 8.857 (≈1 000 tiles) against U₂ = 8.861 (≤ 1 728 tiles), i.e. equal | last-ratio extrapolation of E₃…E₅: E₆ −0.0059, E₇ −0.00067. Dirichlet ratio ¼: E₆ −0.0038, E₇ −0.0015 | (the baseline itself) |
| controls it should fail if the hierarchy matters | none: it holds for every minimal hull, and its only hierarchy input is *which* balls are legal | χ₂ has no stable selected type, so the premise fails; χ₁/χ₃ select the same types as FR30, so selection is not specific to the non-Abelian connection | — | the 937/938 pair: identical class fractions, different bottoms |
| verdict | a **theorem** of standard type (IMS localization, A/B) | convergence is a standard theorem; the rate is a **phenomenological fit** | a **variational approximation scheme**, not a law. Its point accuracy is matched by a two-parameter extrapolation, which, however, has no one-sided guarantee | **falsified** as a sufficient description |

**Conclusion of Part V.**
- The only statement with rigorous predictive content is L-A, together with the compression upper bounds.
  - Both are consequences of standard spectral theory: the variational principle, IMS localization and minimality.
  - In L-A the hierarchy enters only through the *set* of legal local patterns. Their frequencies, and their large-scale arrangement, play no role.
- The selection chain, the fiber and the ratio law are, respectively:
  - an organisation of upper bounds that is no better than generic balls of equal size;
  - an approximation scheme;
  - a fit that already drifts.
- None predicts an unseen observable better than a two-parameter extrapolation of the same sequence.
- **No new law is supported.**

---

## 7. Null model versus hierarchy model (Part VI)

**The comparison.** It uses the closest matched control that exists: rules 937 and 938.
- They share the graph, the hierarchy, the plaquette class counts, the two-cycle class counts and the moments of order ≤ 3.
- Their pinned bottoms differ by Δ\* = Y₅(938) − Y₅(937) = −0.2443, certified at levels 3 and 4.
- Periodic controls were not run (Phase VIII §6f), and nothing here relies on them.

**The two explanations.**
- **Null model** (local frustration + graph geometry + boundary): the difference is already carried by the radius-1 environments of the tiles.
- **Hierarchy model** (longer-range substitution correlations or recursive interface structure): the difference is absent at the radius-1 scale and appears only in patches of supertile size.

**Observable.** U_m(r) = min over the legal 1-star types τ of rule r of λ_min(H|σᵐ(τ)): the lowest energy of the m-times-inflated radius-1 environments.
- U_m(r) is an upper bound on rule r's hull floor (a compression of a legal patch).
- For FR30 it decreases to the floor along self-loops (Theorem 8.3). For 937 and 938, self-loops and the minimality of their hulls were not checked, so only the finite-volume comparison is claimed.
- Δ_m = U_m(938) − U_m(937).

**Decision rule.** Fixed in `phase9_preregistration.json` (15:08:36) before any ladder output existed:
- *null supported, hierarchy model falsified for this pair* if sign Δ₁ = sign Δ\* and |Δ₁ − Δ\*| ≤ 0.10;
- *hierarchy supported, null falsified* if |Δ₁| ≤ 0.05 and |Δ₃ − Δ\*| ≤ 0.10;
- otherwise inconclusive.

**Result** (`phase9_ladder_m01.json`, `phase9_ladder.json`):

| m | patch size (tiles) | U_m(937) | U_m(938) | Δ_m | fraction of Δ\* |
|---|---|---|---|---|---|
| 0 (the 1-star itself) | 9–27 | 10.5459 | 10.3649 | −0.1810 | 74 % |
| 1 | 72–216 | 8.5958 | 8.3667 | **−0.2291** | **94 %** |
| 2 | 576–1 728 | 8.0345 | 7.8281 | −0.2064 | 84 % |
| 3 | 4 608–13 824 | 7.9759 | 7.7479 | −0.2280 | 93 % |
| pinned T₅ | 32 768 | 7.9728 | 7.7285 | −0.2443 (Δ\*) | 100 % |

Notes on the table:
- Each rule has 185 legal 1-star types occurring in its level-5 supertile; FR30 has 72.
- m = 0, 1, 2 are minima over all of them. m = 3 is the minimum over the 20 types with the lowest U₂: a minimum over legal patches is an upper bound on the floor whichever subset is used, and both rules are treated alike.
- The independent code reproduces Phase VIII's FR30 chain exactly: U₁, U₂, U₃ = 9.3484266, 8.8607858, 8.7795327.

**Verdict.** |Δ₁ − Δ\*| = 0.015 with the same sign. **The null model is supported, and the hierarchy model is falsified for this pair.**
- The edge difference between two rules indistinguishable by every frequency-type curvature statistic is already present, at 74 %, in the bare radius-1 environments of 9–27 tiles. It is present at 94 % after one inflation.
- It stays at 84–93 % for m = 2, 3: it neither appears nor grows as the patches reach supertile scale.
- Their local frustration differs in *arrangement* even though the counts agree (§4.2), and that local arrangement is what sets the energies.

**The same test on FR30 versus its Abelian shadow χ₁.** This is post hoc, not pre-registered: the data are from Phase VIII.
- Δ₁ = U₁(χ₁) − U₁(FR30) = 8.2266 − 9.3484 = −1.122, against Δ\* = Y₅(χ₁) − Y₅(FR30) = −1.097.
- The certified non-Abelian contribution of Phase VII is also local: it is present in radius-1 environments.

**What the test does and does not establish.**
- *Does:* for this matched pair, local frustration accounts for the finite-volume edge difference, with no residual that needs the recursion.
- *Does not:* settle the infinite-volume floors, which are not certified to differ (§8). It concerns one pair, not every possible matched pair.
- *Would have falsified the null:* Δ₁ ≈ 0 with Δ₃ ≈ Δ\*. That did not occur.
- *Interpretable even though the hierarchy model failed:* the result locates the matched pair's spectral difference in the radius-1 arrangement of frustration. This is consistent with the Phase VII localization theorem (L-A), under which the floor is a function of the set of legal local patterns.

### 7.1 Equal-size comparison for FR30 itself

The self-similar patches are no better than generic legal balls of the same size:
- D₁₂ = 8.857, from balls of 1 009–1 072 tiles;
- U₂ = 8.861, from patches of 576–1 728 tiles;
- at small size, D₆ = 9.417 (118–145 tiles) against U₁ = 9.348 (72–216 tiles).

Selection along the hierarchy organises the upper bounds but does not improve them beyond what patch size alone provides.

---

## 8. The theorem (Part VII)

**Selection.** Of the four forms offered, only the necessity form (B) is supported by a rigorous construction that is new here.
- Sufficiency (A) holds only in the support form already proved in Phase VII (L-A, §6). There is no finite gauge-invariant state of *frequency* type.
- Hierarchical prediction with a certified error (C) was not achieved: the fiber law is one-sided, and its errors are measured, not bounded.
- "No additional hierarchy law" (D) is the scoped conclusion of §6–§7. It is not a theorem.

> **Theorem 9.1 (frequency-type summaries do not determine the spectral bottom) [P + C].**
>
> *Setting.*
> - Chair44 with proper frames. A decoration is d ∈ {0, …, 3⁸ − 1}, encoded as in the Phase V-B census.
> - Links come from the Pauli formula U_f(a→b) = (σ·M_aᵀn_f)(σ·M_bᵀn_f) ∈ Q₈. The pinned operator is H_L(d) = 24 − A_U on the level-L supertile T_L.
> - Y_L(d) = λ_min H_L(d), the compression of the hull operator of d.
>
> *Statement.* Decorations 937 and 938 satisfy all of the following.
> 1. They have the same tiles, panels and plaquettes, and differ only in the frame of the centre child (rotation by +120° vs −120° about (1,1,1)).
> 2. For L = 3, 4, 5, they have equal counts of
>    - plaquette conjugacy classes (+1, −1, i, j, k), also when split by the number of owner tiles (computed at L = 3);
>    - two-cycle conjugacy classes.
> 3. They have equal spectral moments tr A^p for p = 1, 2, 3 (L = 3).
> 4. They are not gauge-equivalent, and are not related by any symmetry of the geometry (axis permutations, with or without orientation reversal).
> 5. **Y₃(937) − Y₃(938) ≥ 0.27759** and **Y₄(937) − Y₄(938) ≥ 0.25022**, rigorously. Numerically, Y₅(937) − Y₅(938) = 0.2443.
>
> Hence no function of these statistics determines Y_L. The first invariant of the moment hierarchy that separates the two operators is tr A⁴, through the two-cycle co-occurrence and tile-4-cycle terms of §4.4. The bottom itself is separated only by closed walks of length ≳ 16.

**Proof and certificates.**
- **(1)** The two decorations are read off the census encoding.
  - The equality of the cube partitions is asserted in `phase9_pair.build`: tiles are matched by cube sets.
  - The panel lists are then compared element by element.
- **(2, 3)** Exact integer counts, and exact integer moments in int64 with no overflow (|Aᵖ| ≤ 24ᵖ < 2⁶²).
- **(4)** For gauge transformations, the tree-gauge holonomies are compared under all 48 elements of the binary octahedral group, which normalises Q₈ in SU(2). Every relation of the listed kinds preserves the spectrum, and (5) shows the spectra differ.
- **(5)**
  - *Upper ends:* exact rational Rayleigh quotients of integer vectors. H has Gaussian-integer entries, so the arithmetic is exact.
  - *Lower ends:* λ_min(H) ≥ μ − γ_{N+1}‖L̂‖_F², where L̂ is the floating Cholesky factor of the real form of H − μ, μ is a 20-bit dyadic, and the bound is Higham 2002 Thm 10.3. This is the routine used for Phase VII's Λ_R.
  - Level 3: [8.4910240, 8.4910257] and [8.2134323, 8.2134341]. Level 4: [8.0357080, 8.0357096] and [7.7854810, 7.7854826] (`phase9_cert4.json`). ∎

**Counterexamples**, as they bear on Part IV:
- the pair itself, for class counts, owner-resolved counts and two-cycle counts;
- for any statistic built from closed walks of bounded length: the moment argument of §4.4 (the edge gap is carried by walks of length ≳ 16 at level 3), as evidence, not proof.

**Scope and what is not claimed.**
- The infinite-volume floors E_\*(937) and E_\*(938) are **not** certified to differ. Their supertile sequences differ by 0.278, 0.250 and 0.244 at L = 3, 4, 5 [E].
- Certifying it needs a lower bound on E_\*(937) above 7.7285, the certified level-5 upper bound for 938. With the localization method that would require R ≫ 12.

**Reproduction.**

```bash
python -u -I audit/phase9_pair.py pair moments loops edge cert4
```
```bash
python -m pytest -q tests/test_phase9.py
```

**Comparison with known theory.**
- That trace invariants of closed-walk holonomies determine a connection up to gauge, and that coarser statistics need not, is classical [R20, R21, R22].
- Cospectral but switching-inequivalent gain graphs are known [R22].
- That class-frequency statistics need not determine the spectrum is therefore expected. Theorem 9.1 supplies an explicit, certified instance inside the Chair44 family: equal in every frequency-type class statistic tested, with certified spectral separation.
- Its content is that example, together with the location of the first distinguishing invariant. Category **B**.

---

## 9. Corrected central paragraph

> For the Clifford–Q₈ connection FR30 on the three-dimensional chair substitution, the bottom of the spectrum of H = 24 − A_U satisfies 7.954292 ≤ E_\* ≤ 8.7642270381; both bounds are computer-assisted proofs. E_\* is determined by the legal local patterns of the tiling. It is the limit, at the explicit rate O(R⁻²), of the lowest ground-state energies of legal radius-R patches, and the substitution hierarchy enters only through which patterns are legal, which a radius-1 matching rule fixes. Frequency-type summaries of the curvature do not determine the spectral bottom. Two decorations of the same geometry with identical plaquette and two-cycle conjugacy-class counts have rigorously different bottoms of their level-3 and level-4 supertiles, and that difference is already present in their radius-1 environments. These statements follow from the variational principle, Schur complements and IMS localization applied to this geometry. No further spectral law has been established.

## 10. Next step

One substantive mathematical question remains: **a rigorous lower bound on a hull floor that is sharp to O(10⁻²)**.
- It would decide whether Theorem 9.1 holds for the infinite-volume floors of 937 and 938, which are not certified to differ.
  - That needs E_\*(937) > 7.7285, the certified level-5 upper bound of 938, so the bound must lose < 0.24.
  - The IMS bound at R = 12 loses ≈ 0.9.
- The same tool would narrow the FR30 enclosure from width 0.81.
- Two candidate routes:
  - a Temple/Lehmann–Goerisch bound around the D_R minimisers, combined with the exact localization identity;
  - a lower bound propagated through the exact Schur recursion by its comparison principle (Prop. 8.1b).

## Reproduction

**Phase IX scripts.** All read only committed inputs; outputs go to `audit/results/phase9_*.json`.

```bash
python -u -I audit/phase9_pair.py pair moments loops edge cert4
```
```bash
python -u -I audit/phase9_pair.py steps ladder01 ladder
```
```bash
python -u -I audit/phase9_state.py
```
```bash
python -u -I audit/phase9_state.py closure
```
```bash
python -u -I audit/phase9_ledger.py
```
```bash
python -m pytest -q tests/test_phase9.py tests/test_phase8.py
```

Approximate running times (24 threads, shared with other jobs):
- `pair` 1 min, `moments` and `loops` seconds, `edge` 1 min, `cert4` 6 min;
- `steps` ≈ 50 min, `ladder` 80 s, `ladder01` 25 s;
- `phase9_state.py` 1 min, after a one-time 10 s cache of local features in `phase9_local_features.json`.

**Pre-registration.** `audit/results/phase9_preregistration.json` fixes the Part VI decision rule. It was written at 15:08:36 local time, before any ladder output (`phase9_ladder_m01.json`, `phase9_ladder.json`) existed.

**Phase VIII completion** (Part I):

```bash
python -u -I audit/phase8_copy_rg.py 6 114 env
```
```bash
python -u -I audit/phase8_copy_rg.py 7 58 env
```
```bash
python -u -I audit/phase8_copy_rg.py 7 58 deep67
```
```bash
python -u -I audit/phase8_diagnostics.py poles dos
```
