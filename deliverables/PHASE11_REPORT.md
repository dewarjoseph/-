# Phase XI — The spectral frustration principle: what survives outside Chair44, what is certified, and where the obstructions are

**Repository state.**
- Branch `claude/fervent-fermi-e2wi4y`, cut from `main` at 2241b88 (PR #10, Phase X, merged).
- Prior phases and frozen artifacts are untouched. Everything new is under `audit/phase11_*`, `audit/results/phase11_*`, `tests/test_phase11.py`, this report and `deliverables/PHASE11_STRONGEST_THEOREM.md`.
- The protocol for every new evaluation was frozen in `audit/results/phase11_preregistration.json` and committed (c4a75b9) before any new deep value was computed.

**Labels** (as in Phase X).
- [P] proved;
- [C] computer-certified: exact rational arithmetic, or a floating-point Cholesky with Higham's rounding bound;
- [E] floating-point evidence;
- [X] conjecture;
- [F] falsified.

**Notation.**
- G = (V, E) is a graph with degrees ≤ d (multi-edges allowed). U is a unitary connection of rank n, with U(w→v) = U(v→w)⁻¹.
- H_U = D_U†D_U = Deg − A_U, with quadratic form q_U(ψ) = Σ_e |ψ(v) − U(v→w)ψ(w)|².
- **E_\*(U) = inf σ(H_U).** For Chair44, H = 24 − A_U on a tiling, as in Phase X.
- For a finite K ⊂ V: H^D_K = P_K H_U P_K is the Dirichlet (pinned) operator, a compression. H^N_K keeps only the edges inside K (Neumann, free).
- An **environment** of radius R about x is the rooted ball B_R(x) with its degrees and its connection, up to rooted isomorphism and gauge. 𝓛_R(U) is the set of environments that occur.
- D_R = inf over 𝓛_R of λ_min(H^D). Λ_R is the IMS-amplified version (Theorem XI.B).

---

## 0. Answer

**The question.** Can the support-sensitive spectral-frustration principle be proved for a broad class of geometric gauge connections, and can its extremal problem be solved, or sharply bounded, without exhaustive diagonalization?

**1. Yes, the principle is a theorem in full generality, and most of it is established mathematics.**
- For every graph with bounded degree and every unitary connection of any rank, E_\* is the limit of the Dirichlet ground energies of the legal environments. It depends only on *which* environments occur, never on how often, and adding environments can only lower it (Theorem XI.A) [P].
- Two-sided certificates with an explicit O(R⁻²) error hold uniformly over all connections:
  - on graphs with a Euclidean realisation: K_D(ρ)S_c/ρ²; Phase X's chair constant is the case D = 3;
  - on uniformly doubling graphs: 16dC_D²/R² (Theorem XI.C) [P].
- **The exact hypotheses are sharp.**
  - Uniform localisation ⟺ property A (a restatement of known characterisations).
  - R⁻² cannot be improved (ℤ^D).
  - Bounded degree plus IMS do *not* give R⁻²: lamplighter graphs have rate R^{−2/k}.
  - Dirichlet boundary conditions are essential: free windows converge to the wrong limit (2 − √2 against 3 − √5 on the π-flux ladder).
  - Complete legal-environment coverage is essential: an enumeration of only the visible environments produced a **false** certificate.

**2. Quantitatively: support-type curvature data bound the floor; frequency-type data cannot; no finite-scale datum determines it.**
- *Positive theorem* (XI.F). If every legal r-ball carries a loop whose holonomy has all eigenvalue angles ≥ θ₀, then E_\* ≥ 2 sin²(θ₀/2)/((2r + 1)N_r).
  - A flat legal ball forces E_\* below its trivial Dirichlet value. So on amenable-type graphs, E_\* > 0 ⟺ the flatness radius is finite.
  - The angle gap is necessary. It fails in rank ≥ 2 without fixed-point-freeness, and for continuous groups E_\* ∝ θ².
- *No-go* (XI.G). No lower-semicontinuous function of environment frequencies is a non-trivial lower bound, even at vanishing defect density.
- *Obstruction* (XI.I). For every R, connections with identical radius-R languages have certified different floors.
- *Representation theory* (XI.H3). For a finite group, every non-spinor representation's floor is a function of the plaquette class field. **The Phase X ℤ³ counterexample lives entirely in the spinor component.** A ladder version needs only a non-Abelian *structure* group, not non-Abelian holonomy.

**3. Phase X, audited.**
- **All four localisation certificates were re-certified by an independent implementation:** FR30 R = 12; 1387 R = 14 and **R = 15**; twin R = 14. This covered enumeration, completeness test, symbolic derivation of the overlap function and banded Higham certificates.
- The R = 14/R = 15 inconsistency between report, ledger and tests is resolved in favour of R = 15: **E_\*(1387) ≥ 8.7999990**.
- The comparison E_\*(1387) > E_\*(FR30) no longer depends on any unstored artifact.
- One Phase X certificate was reclassified as evidence: the ℤ³ trace-pair shadow bound.
- One Phase X statement was corrected: the "mirror twin" is not a function of the gauge class.
- The proof-obligation table (§1.2) separates proofs, exact arithmetic, rounding-bounded floating point, and evidence.

**4. The extremal problem: a certified frontier, not an optimum.**
- **Proper rules.** 1095 of the 1098 gauge classes are proven inferior to 1387 by exact rational upper bounds, so the maximiser is one of 1387, 1389 and 1391 [C].
  - E_\*(1389) > E_\*(FR30) is now certified without any stored-only artifact.
  - ⟨T1391_SHORT⟩
- **All 6⁸ frame rules.** An exhaustive certified funnel proves every rule outside six explicit rules inferior to 1387 [C]: exact Y₃ for all 280 332 S₃-orbit representatives, then Y₄, Y₅, D₈ and Y₆ for the survivors.
- **The frontier is a single orbit.** Right-multiplying every child frame by the chair's own point group S₃ acts on rule space. **The orbit of 1387 is {1387, 1389, 1391, 539311, 539291, 539288}**, exactly the six largest level-5 bounds known. The remaining extremal question is which member of one orbit is highest.
- The mirror twin of FR30 obtained through 1386 is FR30's exact mirror image, with **E_\* equal to FR30's** (proved via Phase VII's radius-1 matching rule).
- **The six certified intervals all overlap** (independent bounds; §2.1):

  | member | certified E_\* interval |
  |---|---|
  | 539311 | [8.7999990, 9.3885937] |
  | 1387 | [8.7999990, 9.3679502] |
  | 539291 | [7.1408386, 9.2499400] (lower bound from Phase X) |
  | 1389 | [8.7644993, 9.2104998] |
  | 1391 | [⟨L1391⟩, 9.1104007] |
  | 539288 | [6.8499994, 9.0982534] |

  No member is proven superior, so no optimum is claimed.
- **How far certification can go** (§2.4).
  - Sampled probes bound what any IMS certificate can reach: Λ_R(1387) ≤ 9.1675 and Λ_R(539311) ≤ 9.1851 for R ≤ 22.
  - So **no certificate at R ≤ 22 separates the two co-leaders**, or 1387 from 1389 and 539291. The preregistered R = 20 target for 1387 could at most remove 1391 and 539288.
  - The cost grows like R^{11–12}: R = 18 took ⟨T18⟩ on 4 cores; R = 20 would take ≈ ⟨T20⟩.

**5. Why 1387 is strong.**
- The one-child intervention from FR30 changes the gauge class of every environment (0 shared of 72 at radius 1 and of 415 at radius 8). It keeps all geometric configurations and every localisation constant.
- **It raises the worst local energy on every one of the 16 geometric 1-star configurations.** It also removes the three FR30 tile types whose two-cycles are all trivial; FR30's weakest R = 8 environment is centred on one of them.
- Absence of such tiles is strongly associated with high floors on Phase X's preregistered random sample: median Y₅ 7.553 against 6.915, p = 4·10⁻¹¹ (post hoc, [E]).
- Every preregistered prediction (P1–P3) passed. On single-child neighbourhoods U₁ ranks Y₅ with Spearman 0.88–0.92 and 100 % sign accuracy. No single-child change of 1387 raises Y₅. The twin criterion holds in 31/40 cases: a correlation, and ill-posed on gauge classes.

**6. The second geometry.**
- The substitution ladders are defined independently of Chair44: quasi-one-dimensional, degree 3, any finite subgroup of SU(2).
- Every general theorem was tested there with certified enclosures to 10⁻⁵.
- What does **not** transfer is Chair44-specific and named in the dependency table:
  - positivity of every rule needs the chair's forced rotations;
  - the angle gap needs a finite group;
  - fixed-point-freeness needs the spinor representation.

**7. The abstraction.**
- The **certified local frustration profile** Π_R = [L_R, U_R] is gauge- and symmetry-invariant, nested, two-sided with a proved rate, and computable from the finite legal data.
- It passes both mandatory falsification tests. It separates the ℤ³ pair at R = 5 (certified gap 0.61, up from 0.18), where every plaquette-class invariant fails. It does not falsely separate 937/938.
- No compact abstraction closes: Π_{R+1} is not a function of Π_R, and no fixed radius determines E_\*. This is stated and proved as an obstruction.

**8. Novelty.**
- Categories 1–2 dominate.
- New in the weak sense of not found in the literature:
  - the discrete flatness-radius dichotomy with explicit constants;
  - the localisation of X.5 to the spinor component;
  - the exact Neumann-window counterexample;
  - the finite-radius obstruction with certified pairs;
  - the right-S₃ orbit structure of the Chair44 frontier.
- No physical claim is made.

**The strongest theorem that survives independent verification** is stated on one page in `deliverables/PHASE11_STRONGEST_THEOREM.md`.
- Its scope: all bounded-degree graphs and all unitary connections for (1); property-A, doubling or Euclidean graphs for the rates; finite-group, fixed-point-free connections for the frustration bound.
- It establishes positivity and two-sided certificates, not extremality.
- **The next experiment** (§12): find a localisation certificate for Chair44 that converges faster than R⁻². Only that can separate 1387 from its mirror twin; plain IMS would need R ≈ 63.

---

## 1. The Phase X baseline, audited (Part I)

**Independence.**
- The audit re-implements the Chair44 objects from the written definitions (`PHASE7_DEFINITIONS.md` §1–5) in `audit/phase11_chair.py`, which imports no Phase V–X code. This covers:
  - the index maps, tiles and supertiles, panels and Pauli links;
  - the pinned and free operators;
  - the 1-star types and the Φ-closure;
  - the ball enumeration and its completeness test;
  - the overlap function and the certificate.
- Phase X code is used only in tests, to compare outputs.
- The certificate path is also different: reverse Cuthill–McKee ordering and banded LAPACK `dpbtrf` on the CPU, with u = 2⁻⁵². Phase X used dense cuSOLVER on a GPU with u = 2⁻⁵¹.
- The banded path is 16× faster than dense on an R = 15 ball (0.23 s against 3.6 s). That is what made CPU-only re-certification possible here.

**Agreement on shared intermediate objects** (all exact):
- index maps on all 6561 proper decorations and the extended sample;
- level-3 pinned spectra of 4752, 1387 and 937 (difference 0.0);
- Φ-closed type sets of 4752, 1387, 1389 and 1391 (72, 90, 102, 104; identical keys);
- ball counts 747 / 1450 at R = 8;
- the radius-1 data of FR30 (U₀, U₁, μ₀ to 10⁻¹³).

### 1.1 The R = 14 / R = 15 reconciliation

**What was inconsistent in Phase X.**
- The report cites both certificates for class 1387.
- The ledger (`phase10_ledger.json`, written at 529bba9) and the tests stop at R = 14.
- Several report sections (§3.2, §6, §7) still use the R = 14 value.

**All four localisation certificates were re-certified independently** (`audit/results/phase11_cert.jsonl`):

| certificate | Phase X / VII value | balls (Phase X) | Phase XI value (independent) | balls (Phase XI), rejected | all pass |
|---|---|---|---|---|---|
| FR30, R = 12 | 7.954292265 | 2315 | **7.954291278** (μ chosen 10⁻⁶ lower) | 2315, 0 | yes |
| 1387, R = 14 | 8.764499373 | 7527 | **8.764499519** | 7527, 0 | yes |
| **1387, R = 15** | **8.799998780** | 10321 | **8.799999009** | 10321, 0 | **yes** |
| twin 539311, R = 14 | 8.764499373 | 7527 | **8.764499519** | 7527, 0 | yes |

**Resolution.**
- The R = 15 certificate is independently verified. The ledger and tests now carry it.
- The certified enclosure of class 1387 is **E_\*(1387) ∈ [8.7999990, 9.3679502]**.
- **The comparison with FR30 no longer depends on the Phase VIII bound.** Phase VIII's 8.7642270 comes from a 1.77M-dimensional eigenvector that is not stored. FR30's exact level-5 bound Y₅(FR30) = 8.7970113 (exact rational 3070587004765936/349048886578754) < 8.7999990, recomputed independently, already gives a certified separation ≥ 0.0029876.
- With FR30's inflated-star bound, now recomputed independently (U₅ = 8.7642271, §2.1), the separation is ≥ 0.0357719.

### 1.2 The proof-obligation table

A passing regression test only shows that an implementation is consistent; it is not a proof. Each Phase X claim is therefore split into obligations, and each obligation is discharged by the means appropriate to it (`phase11_ledger.json:proof_obligations`).

| # | obligation | nature | how Phase XI discharged it | status |
|---|---|---|---|---|
| O1 | Pauli links lie in Q₈; the reverse crossing gives the inverse; the sign of n is irrelevant | algebra | (σ·u)² = 1; independent implementation agrees entrywise | **proved** |
| O2 | Deg ≡ 24 on every tiling, so H_Y = 24 − A_U = D†D | geometry | 24 unit boundary faces (7 cubes, 9 internal adjacencies; exact count), each shared with exactly one tile | **proved** |
| O3 | the pinned operator on a legal patch is a compression, so λ_min ≥ E_\* | variational | min–max, plus occurrence (minimality) or the language definition of E_\* | **proved** |
| O4 | exact rational Rayleigh quotients are rigorous upper bounds | exact arithmetic | recomputed independently: Y₃ for all 280 332 extended orbit representatives, Y₄ for every survivor, Y₅ for the preregistered lists, and **Y₆ for the six orbit members** (reproducing Phase X's stored-only values to ≤ 10⁻⁹) and for 515963. Phase X's other Y₆ values (e.g. 901) remain recorded rationals whose vectors are not stored | proved for L ≤ 5 and for the orbit at L = 6; artifact-only for the other Y₆ values |
| O5 | the free supertile bottom F_k bounds E_\* below (X.2) | proof | every hull tiling is σᵏ of a hull tiling (compactness), so it is partitioned into level-k supertiles. Links are invariant under global frames, proper or improper. Dropping the inter-supertile panels lowers the form. Recognizability is not used | **proved** |
| O6 | the IMS identity with amplified links | algebra | Theorem XI.B1; randomized identity test, error 4·10⁻¹⁵ | **proved** |
| O7 | c(η) is the overlap of the 3D Dirichlet ground state | analysis | **derived symbolically** (`phase11_proofs.overlap3d`): equals the Phase VII closed form, and equals 1 − π²η²/6 + O(η³). Phase X had only asserted it; quadrature agrees to 10⁻¹⁰ | **proved** |
| O8 | r_c = √619/14 ≤ 311/175 | exact | r_c² = 619/196 exactly, and (311/175)² − r_c² = 9/122500 > 0 | **proved** |
| O9 | the Φ-closure of the T₅ types is the set of all legal 1-star types | proof plus per-instance checks | closure lemma asserted on every Φ step; the frame digraph is a Cayley digraph, hence irreducible (XI.D) | **proved** |
| O10 | every enumerated ball is complete | exact geometric check | independent criterion: nearest unowned cube centre at ≥ R + √3/2. 0 rejections at R = 8, 12, 14, 15 | **verified** |
| O11 | the Higham certificate is implemented soundly | floating point with rounding bound | different factorization, ordering and code, with a two-ulp unit | **verified** |
| O12 | rounding of the amplification factors | error bound | 60-digit evaluation; 24·max amp·2⁻⁵² subtracted | **verified** |
| O13 | E_\*(1387) ≥ 8.7999988 (R = 15) | certificate | table 1.1 | **verified** |
| O14 | E_\*(FR30) ≤ 8.7642270 (Phase VIII) | rational of an unstored vector | **re-derived independently**: U₅ = 8.7642270435 (`phase11_fr30_upper.py`), 5·10⁻⁹ above Phase VIII's value. It is load-bearing only for 1389 > FR30 (§2.1) | **verified** |
| O15 | the twin's floor exceeds FR30's | certificate + upper bound | twin R = 14 re-certified (8.7644995); Phase X's comparison used Phase VIII's 8.7642270 (artifact). **The twin is now certified at R = 15** (8.7999990 > Y₅(FR30) = 8.7970113, both independent) | **verified without artifacts** (§2.2) |
| O16 | ℤ³ class-field-matched pair (X.5) | exact plus certificate | independent rebuild: identical classes on all 24 plaquettes; shadow ratio connections flat for k = 1, 2, 3; upper bound 0.404134696 exact (θ = 0); lower bound 0.585785866 (free cell). **Separation 0.18165, confirmed** | **verified** |
| O17 | ℤ³ trace-matched pair: two shadows certified above the non-Abelian floor | floating point with heuristic margin | Phase X's Lipschitz branch-and-bound uses float eigenvalues with a 1.2·10⁻⁹ margin. This is strong evidence, **not a strict certificate** | **reclassified [E]** |
| O18 | census-wide E_\* ≥ 3.788 and 806 classes rigorously below FR30 | certificates | independent recomputation of free-T₃ Higham bounds and exact Y₄ for all 1098 classes: minimum certified free-T₃ bound **3.7882948** (Phase X: 3.7882948); **806** classes with exact Y₄ < 7.954291 (identical to Phase X); all 1098 exact Y₄ rationals recomputed | **verified** |
| O19 | primitivity of every proper rule; period 2 for the twins | exact | recomputed independently. A bug in Phase XI's own irreducibility flag (integer overflow) was found and fixed; the affected record carries a note. The certificate does not use the flag | **verified** |
| O20 | periodic-approximant floors (Phase X §9, row 11) | floating point | unchanged | **[E]** |

**Which bounds are which.**

| kind | instances |
|---|---|
| exact rational certificates | every Y_L upper bound (L ≤ 6); D_R upper bounds; the ℤ³ upper bound at θ = 0; ladder D_W bounds |
| floating point with a proved rounding bound (Higham) | every Λ_R; every free-supertile or free-cell lower bound; the Y₄ enclosures; ladder Λ_W |
| floating-point evidence | float eigenvalues (with residuals); Bloch minima of periodic approximants; the ℤ³ trace-pair shadow branch-and-bound; extrapolated (last-ratio) floors, which are conjectures [X] |

**The two proofs singled out by the brief.**
- **Free cell below** (O5): correct as stated in X.2. The proof needs only σ-surjectivity on the hull and invariance of the Pauli links under global frames, including mirrors.
- **Pinned Rayleigh above** (O3, O4): correct. A Rayleigh quotient of any integer vector on a legal patch bounds the compression from above, which bounds E_\* from above. No eigenvector accuracy is needed.

## 2. The extremal frontier (Part II)

**The rule** (frozen in the preregistration before any value was computed).
- A rule r is **proven inferior** to 1387 iff an exact rational upper bound satisfies U(r) < L_ref = 8.7999987.
  - U(r) is a Rayleigh quotient on a pinned legal supertile or ball.
  - L_ref lies below the independently verified Λ₁₅(1387) ≥ 8.7999990.
- Nothing else eliminates a rule: no screening score, prediction or extrapolation.
- With E_\* defined through the language (Theorem A), the bound U(r) ≥ E_\*(r) needs neither minimality nor primitivity. It holds for all 6⁸ decorations.

### 2.1 Proper rules: the interval leaderboard

`audit/results/phase11_leaderboard.json` / `.csv`; every interval endpoint carries its source and certificate type.

| rank by L | class | certified lower L (source) | exact upper U (source) | status |
|---|---|---|---|---|
| 1 | **1387** | **8.7999990** (IMS R = 15, 10 321 balls, independent) | 9.3679502 (Y₆; Phase X's stored-only value, now recomputed independently) | **leader** |
| 2 | 1389 | **8.7644993** (IMS R = 16, 12 193 balls, new) | 9.2104998 (Y₆, recomputed independently) | contender |
| — | 1391 | ⟨L1391⟩ | 9.1104007 (Y₆, recomputed independently) | contender |
| — | 1386 (FR30) | 7.9542923 (Phase VII R = 12; independent 7.9542913) | 8.7642270 (σ⁵ of a self-loop type; Phase VIII value reproduced independently, §2.1) | proven inferior |
| — | 901 | 6.5510740 (R = 8) | 8.6366663 (Y₆, artifact) | proven inferior |
| — | 1144 | 5.4726372 (R = 8) | 8.1414086 (D₈, exact) | proven inferior |
| — | every other class | free-T₃ Higham bound (min 3.7882948, independent) | exact Y₄, Y₅ or D_R | proven inferior |

**Classification against the leader** (L_best = 8.7999990; `phase11_leaderboard.json`):
- **1095 classes proven inferior**. Each has an exact rational upper bound below 8.7999987. Phase X's count is confirmed with the independent R = 15 certificate.
- **2 contenders**, 1389 and 1391. Their intervals overlap the leader's.
- **No class is proven superior.**
- **Hence the maximiser of E_\* over all 6561 proper Chair44 rules is one of the classes 1387, 1389 and 1391** [C].
- Census side-results, recomputed independently:
  - every class has E_\* ≥ 3.7882948;
  - **809** classes are rigorously below FR30 using every available upper bound. Phase X's 806 used Y₄ alone, and is reproduced exactly with Y₄.

**The preregistered certificate targets.**
- **1389, R = 16**: all 12 193 legal balls (no rejections, m = 4) pass at μ = 2297561/262144. So **E_\*(1389) ≥ 8.7644993**.
  - This exceeds FR30's Phase VIII bound 8.7642270 (artifact), but **not** FR30's independent bound.
  - To make the comparison artifact-free, FR30's inflated-star chain was re-implemented (`phase11_fr30_upper.py`). It reproduces Phase VIII's U₃ = 8.7795327 and gives an exact U₄ = 8.7662711, which is not yet low enough.
  - **U₅ = 6534049968655174/745536364613169 = 8.7642270435** (σ⁵ of the minimising self-loop type, 884 736 tiles, exact rational Rayleigh quotient). It reproduces the Phase VIII artifact 8.7642270381 to 5·10⁻⁹.
  - **Hence E_\*(1389) ≥ 8.7644993 > 8.7642271 ≥ E_\*(FR30), with no stored-only artifact** [C]. The separation is ≥ 0.000272.
- **1391, R = 18**:
  - At m = 4 the completeness check rejected balls, and the run stopped as designed.
  - Two m = 5 runs ran out of memory. The first, with unchunked neighbourhood queries, was stopped. The second was killed by the kernel when one worker held 12.5 GB of balls.
  - Before the third run, a probe showed the target was not excluded (§2.4). The certificate now streams (§2.4).
  - ⟨T1391⟩
- **1387, R = 20** (μ = 9.1105): ⟨T1387_R20⟩

### 2.2 The extended space: a certified funnel instead of a screen

Phase X computed Y₂ for all 6⁸ decorations, Y₃ for the top half by Y₂, and Y₄ for the top 10 % by Y₃. That is a screen with calibrated recall, not a proof. Phase XI replaces it with an exhaustive certified funnel over all 280 332 S₃-orbit representatives. Y_L is constant on S₃-orbits: conjugation by an axis permutation rotates every supertile rigidly, and rigid motions preserve the Pauli links.

| stage | evaluated | proven inferior (exact U < 8.7999987) | surviving | cost (4 cores) |
|---|---|---|---|---|
| X3: exact Y₃ | 280 332 (all) | **235 644** | 44 688 | 30 min |
| X4: exact Y₄ | 44 688 | **44 650** | 38 | 34 min |
| X5: exact Y₅ | 38 | **30** (FR30 and its mirror 539315 at Y₅ = 8.7970113 among them) | 8 | 2 min |
| X6: exact D₈ (all legal 8-balls) | 2 outside the orbit: 515983 = 1144·(x y), 515963 = 901·(y z) | **515983**. A rare legal environment again: 476 legal 1-star types, only 265 visible in T₅. D₈ = 8.1678858 against Y₅ = 8.8090 | 7 | 15 min |
| X7: exact Y₆ (262 144 tiles) | 515963 | **515963** (Y₆ = 8.7812558 against Y₅ = 8.8961) | **6** | 2 min |

- Every flag was rechecked from the stored rationals (`tests/test_phase11.py`).
- **The certified statement** (`phase11_frontier_summary.json`) [C]:
  - every one of the 1 679 616 frame rules of the extended space outside the six rules {1387, 1389, 1391, 539311, 539291, 539288} has an exact rational upper bound on E_\* below 8.7999987 ≤ E_\*(1387);
  - **so the maximiser of E_\* over the whole extended space lies in this set of six.**
  - The set is exactly the right-S₃ orbit of 1387 (§2.3).
  - The maximal floor satisfies 8.7999990 ≤ max E_\* ≤ 9.3885937, the independent exact Y₆ of 539311.

**The orbit leaderboard** (`phase11_leaderboard.json:orbit_1387`; independent bounds unless marked):

| member (P applied to 1387's child frames) | certified lower L (source) | exact upper U (source) | status |
|---|---|---|---|
| 539311 = 1387·(x y) | **8.7999990** (IMS R = 15, 10 321 balls) | 9.3885937 (Y₆) | co-leader |
| 1387 (identity) | **8.7999990** (IMS R = 15, 10 321 balls) | 9.3679502 (Y₆) | co-leader |
| 539291 = 1387·(y z) | 7.1408386 (IMS R = 8, Phase X) | 9.2499400 (Y₆) | contender |
| 1389 = 1387·(2 0 1) | 8.7644993 (IMS R = 16, 12 193 balls) | 9.2104998 (Y₆) | contender |
| 1391 = 1387·(1 2 0) | ⟨L1391⟩ | 9.1104007 (Y₆) | contender |
| 539288 = 1387·(x z) | 6.8499994 (IMS R = 8, 829 balls, new) | **9.0982534** (Y₆, new) | contender |

- Every interval overlaps the co-leaders' [8.7999990, 9.3679502]. **No member is proven inferior or superior within the orbit.**
- The Y₆ recomputations reproduce Phase X's stored-only values to ≤ 10⁻⁹ where they exist. The bound for 539288 is new, and it moves 539288 to the bottom of the orbit.
- The **mirror twin 539311** is certified at R = 15 as well: all 10 321 balls pass, E_\*(539311) ≥ 8.7999990. This makes "the twin is above FR30" independent of the Phase VIII artifact (Y₅(FR30) = 8.7970113 < 8.7999990).
- **Cost.** The whole extended-space certification took about 1.5 CPU-hours per core on 4 cores. It used only small exact eigenproblems (≤ 262 144 tiles) and needed no screening assumption.
  - Phase X's screen had missed nothing: its top-10 list contained all six orbit members.
  - But the screen gave no proof that nothing else competes; the funnel does.

### 2.3 Mirror twins and handedness: the criterion question is ill-posed, and what replaces it

**"The mirror twin of a class" is not well defined.**
- Right-multiplying every child frame by a transposition τ gives a rule d·τ. There are three transpositions.
- Conjugating d by an axis permutation conjugates τ, so different members of one gauge class give different twins.
- Within FR30's class {1386, 3690, 4752}: 1386·(x y) = 539315, but 4752·(x y) = 3690·(x y) = 539287 (`phase11_mechanism.json:twins_by_member`).
  - **539315 is FR30's exact mirror image.** Its legal 1-star types coincide with FR30's (72 = 72, same keys) and its R = 8 environment fingerprints coincide (415 = 415). Its Y₃, Y₄ equal FR30's to 10⁻¹².
  - By Phase VII Theorem 6.2 (FR30's radius-1 matching rule), every tiling of its hull is, after a global mirror that leaves every link unchanged, a tiling of FR30's hull. Hence **E_\*(539315) = E_\*(FR30) exactly** [P + C].
  - Phase X's "FR30's twin is lower" refers to 539287, a different rule (Y₄ = 8.70178).
- Within 1387's class, the six members give **three** twins: 539311 (1387, 1388), 539291 (3692, 4753) and 539288 (3691, 4754). Phase X attributed these to classes 1387, 1389 and 1391 respectively.

**The well-defined object.**
- Let the chair's point group S₃ act on rule space by right multiplication of all child frames, d ↦ d·P.
- The geometry is unchanged. The hull, the links and E_\* change.
- Even P (3-cycles) maps proper rules to proper rules; odd P (transpositions) gives the twins. The triple of twins, up to S₃, is a class invariant.

| right-S₃ orbit of | P = identity | 3-cycle (1 2 0) | 3-cycle (2 0 1) | (x y) | (y z) | (x z) |
|---|---|---|---|---|---|---|
| **1387** | 1387 | **1391** | **1389** | **539311** | **539291** | **539288** |
| FR30 (1386) | 1386 | 1390 | 1390 | 539315 (= mirror of FR30) | 539287 | 539287 |
| 1144 | 1144 | 1382 | 903 | 515983 | 539261 | 539941 |
| 901 | 901 | 1384 | 1146 | 539276 | 515963 | 539936 |
| 937 | 937 | 941 | 942 | 516812 | 516791 | 516793 |

**The finding.**
- Among all rules with a computed level-5 bound (Phase X), the six largest are 539311 (9.4159) > 1387 (9.3928) > 539291 (9.2718) > 1389 (9.2187) > 1391 (9.1221) > 539288 (9.1124).
- **These are exactly the right-S₃ orbit of 1387.** The next value is FR30's 8.7970.
- Whether any other rule of the 6⁸ space can compete is decided by the certified funnel (§2.2), not by this list.
- The extremal problem, the three "unresolved contenders" 1389 and 1391, and the twins all reduce to one question: **which member of one orbit is highest.**
- In the census index the proper part of the orbit is a cyclic shift of every child's frame choice. Classes 1387, 1389 and 1391 differ only in the first two digits.

**The preregistered twin criterion.** On the 40 classes with the largest Y₄, with twins taken via each class's representative, the sign of ΔU₁ is used to predict the sign of ΔY₅ (`phase11_analysis.json:twins`).
- **31/40 correct (77.5 %, exact 95 % interval [0.62, 0.89])**. The Spearman correlation of ΔU₁ with ΔY₅ is 0.43.
- Three of the correct cases are exact ties. In 1386, 63 and 954 the representative's twin is the class's own mirror image (equal U₁, equal Y₅). Excluding them, 28/37 (76 %) are correct.
- The twin is higher at level 5 in 16 of the 40 pairs.
- Among the 9 failures, ΔU₁ and ΔY₅ have opposite signs with |ΔY₅| up to 0.60 (classes 1149 and 1150).

**Criterion.**
- No criterion of the form "reflection raises (or lowers) the floor of a class" can exist, because the reflected rule is not a function of the class.
- At the decoration level the effect of a reflection is that of moving within a right-S₃ orbit.
- Its sign is predicted by the radius-1 environment minimum with the accuracy reported above. That is a correlation, not a theorem.

### 2.4 How far certification can go, and at what cost

**What a certificate at radius R can reach: probes** (`phase11_chair.py probe`; `phase11_probe_{1387,1391,539311}.json`) [E].
- Every legal, complete ball B gives Λ_R ≤ λ_min of the amplified operator on B, which is ≤ the Rayleigh quotient of any vector. So the minimum over a sample of legal balls is an **upper bound on the best certificate possible at radius R**.
- The values are float Rayleigh quotients (eigsh, tolerance 10⁻¹¹). An exact rational version would not change the digits shown.
- Sample: six random legal centres (seed 0) in each of the ten legal 1-star types with the lowest U₁, inside σ⁵ of the type. That is 60 balls per radius.

| rule | Λ₁₆ ≤ | Λ₁₈ ≤ | Λ₂₀ ≤ | Λ₂₂ ≤ |
|---|---|---|---|---|
| 1387 (4753) | 8.97335 | 9.06194 | 9.12509 | 9.16748 |
| 1391 | — | 8.80367 | — | — |
| 539311 | — | — | 9.14201 | 9.18506 |

**Consequences** (exact, given the probe values):
- **The 1391 target (R = 18, μ = 8.7645) is not excluded** (8.8037 > 8.7645). It was run (§2.1).
- **The 1387 target (R = 20, μ = 9.1105) is not excluded** (9.1251 > 9.1105), but the margin is 0.015 over a 60-ball sample.
  - If it passed, E_\*(1387) > 9.1105 would exceed the independent Y₆ of 1391 (9.1104007) and of 539288 (9.0982534, new), removing both from the frontier.
  - It would not touch the other three members.
- **No certificate of 1387 at R ∈ {16, 18, 20, 22} exceeds 9.1675.** The exact upper bounds of 1389 (9.2104998), 539291 (9.2499400) and 539311 (9.3885937) lie above that. With these upper bounds, no certificate of 1387 at these radii separates it from them.
  - A smaller upper bound for one of them would require a smaller E_\* for it, which nobody knows.
- **The same holds in the other direction for the co-leader:** Λ_R(539311) ≤ 9.1851 < 9.3679502 = U(1387) at R ∈ {20, 22}.
- **So the comparison of the co-leaders 1387 and 539311 is out of reach of IMS certificates at R ≤ 22, in both directions.**

**Cost model** (`phase11_costs.json`: one R-ball of 1387 per radius, timed under load; ball counts from `phase11_cert.jsonl`):

| R | tiles per ball | RCM bandwidth | Cholesky per ball | distinct legal balls | certificate, 4 cores |
|---|---|---|---|---|---|
| 14 | 1 640 | 641 | 0.11 s | 7 527 (1387) | 4.4 min (measured, m = 4) |
| 15 | — | — | — | 10 321 (1387) | 16 min (measured, m = 4) |
| 16 | 2 509 | 892 | 0.24 s | 12 193 (1389) | 17 min (measured, m = 4) |
| 18 | 3 507 | 1 213 | 1.5 s | ⟨N18⟩ (1391) | ⟨T18⟩ (measured, m = 5) |
| 20 | 4 808 | 1 405 | 1.9 s | ≈ ⟨N20⟩ (1387, estimate) | ≈ ⟨T20⟩ (estimate) |
| 22 | 6 376 | 1 638 | 3.6 s | ≈ ⟨N22⟩ (estimate) | ≈ ⟨T22⟩ (estimate) |

- The Cholesky cost grows like N·b², about R⁷: N ∝ R³ unknowns and RCM bandwidth b ∝ R². Above R = 16 the band (≥ 100 MB) leaves cache, and the measured cost grows faster.
- The number of distinct legal balls grows roughly like R^4.6 at these radii [E]. Together that is about R^{11–12} per certificate.
- From R = 18 on, the enumeration needs level-5 inflations: at m = 4, 50 441 centres of 1391 are rejected as incomplete.
  - Every level-5 type contains nearly every distinct ball, so holding them per worker exhausted 15 GB (a first R = 18 attempt was killed by the kernel).
  - The certificate therefore streams. Pass 1 deduplicates on zlib-compressed canonical keys; zlib is lossless and deterministic, so the equality is exact and no hash is assumed. Pass 2 re-inflates each type and certifies the balls it owns.
  - The output is identical to the one-pass path on test cases (`test_streaming_enumeration_matches`).

**Extrapolation [X]: a model, not a bound.**
- Fitting Λ_R = E − C/ρ² to the R = 20 and R = 22 probes of 1387 gives C ≈ 75 and E ≈ 9.351. This is consistent with E_\* ≤ Y₆ = 9.368.
- Under that model a certificate of 1387 reaches the present U(1389) = 9.2105 at ρ ≈ 23 (R ≈ 25, ≈ ⟨T25⟩ on 4 cores).
- It resolves a gap of 0.02, the level-6 gap between 539311 and 1387, only at ρ ≈ 61 (R ≈ 63). That is out of reach for this method.

## 3. The general support-sensitive theorem (Part III)

**Setting S.** G = (V, E) is countable, with multi-edges allowed and no loops, and deg(v) ≤ d < ∞. U is a unitary connection of any rank n. Then 0 ≤ H_U ≤ 2d. G need not be connected, and no group action, repetitivity or embedding is assumed unless stated.

### Theorem XI.A (support principle) [P]
Under S:
- **(A1)** D_R(U) = inf{λ_min H^D_B : B ∈ 𝓛_R(U)} is non-increasing in R, satisfies D_R ≥ E_\* for every R, and **D_R → E_\***.
- **(A2) Antitonicity.** If every environment of U′ (on any graph satisfying S) is an environment of U, at every radius, then E_\*(U′) ≥ E_\*(U). In particular E_\* is a function of the environment language (𝓛_R(U))_R alone.
- **(A3) Families.** For a family Ω (a hull), E_\*(Ω) := inf_{Y∈Ω} E_\*(U_Y) = lim_R inf over ∪_Y 𝓛_R(U_Y). It is constant on Ω when all members share their languages (a minimal hull). It is also constant when Ω is a finite union of minimal components permuted by maps that preserve H up to unitary equivalence (Chair44 with an imprimitive frame substitution: Theorem XI.D(iv)).

*Proof.*
- Balls are nested, and the least eigenvalue of a compression can only increase when the subspace shrinks (min–max). λ^D(K) is the minimum of q_U(ψ)/‖ψ‖² over ψ supported in K, hence ≥ E_\*.
- H_U is bounded, so finitely supported vectors are dense in form sense. Given ε, take a finitely supported ψ with q(ψ) < (E_\* + ε)‖ψ‖².
- q and ‖·‖² are additive over connected components, so one component part ψ_C ≠ 0 has the same property. Its support is finite and lies in one component, hence in a ball. So D_R < E_\* + ε for R large.
- (A2) is the inclusion D_R(U′) ≥ D_R(U), followed by the limit. (A3) exchanges two infima. ∎

**What (A1) does and does not give.**
- The upper side converges with **no rate** and no hypothesis beyond bounded degree. Theorem C(iv)–(v) shows that no universal rate exists.
- "min" in the brief's formula is a minimum when the language is finite at each radius (finite local complexity). Otherwise it is an infimum.
- Dirichlet (pinned) boundary conditions are essential. **Neumann (free) windows do not converge to E_\*, under any geometric hypothesis.**
  - On the π-flux ladder (§6), E_\* = 3 − √5 = 0.763932 exactly, but the free windows converge to 2 − √2 = 0.585786.
  - With flux π/2 they converge to (3 − √5)/2 = 0.381966, against E_\* = 3 − √6 = 0.550510.
  - End states sit below the bulk floor: a lattice analogue of the de Gennes surface-state constant Θ₀ < 1.
  - The Chair44 saturation of F_k observed in Phase X is the same phenomenon.
- Free *partitions* still give valid lower bounds (Theorem X.2). They are simply not sharp.

### Theorem XI.B (the exact IMS identity in amplified-link form) [P]
- Let {χ_j} (j in a countable set, or a σ-finite measure space with integrals and essential infima) be real functions with Σ_j χ_j(v)² = 1 for every v, each supported in a finite set K_j.
- For an edge e = {v, w}, let c_e = Σ_j χ_j(v)χ_j(w), so that g_e := Σ_j(χ_j(v) − χ_j(w))² = 2 − 2c_e. Assume c_e > 0.
- Let Ã_U be A_U with each edge's link divided by c_e.

Then:
- **(B1)** q_U(ψ) = Σ_j ⟨χ_jψ, (Deg − Ã_U)χ_jψ⟩ exactly, for finitely supported ψ.
- **(B2)** E_\*(U) ≥ Λ(χ) := (ess) inf_j λ_min P_{K_j}(Deg − Ã_U)P_{K_j}.
- **(B3)** Λ(χ) ≥ inf_j λ^D(K_j) − ε(χ), with ε(χ) := sup_v Σ_{e∋v}(1/c_e − 1).

*Proof.*
- (B1): per edge, Σ_j[χ_j(v)²|ψ(v)|² + χ_j(w)²|ψ(w)|² − (2/c_e)χ_j(v)χ_j(w)Re⟨ψ(v), Uψ(w)⟩] = |ψ(v)|² + |ψ(w)|² − 2Re⟨ψ(v), Uψ(w)⟩. The sums converge absolutely by Cauchy–Schwarz.
- (B2): each term is ≥ λ_j‖χ_jψ‖², and Σ_j‖χ_jψ‖² = ‖ψ‖².
- (B3): Schur test on Ã − A, whose blocks have norm 1/c_e − 1 ≥ 0 because c_e ≤ 1. ∎

**Remarks.**
- This is the IMS double-commutator formula, H = Σχ_jHχ_j − ½Σ[χ_j,[χ_j,H]], with the error term redistributed into the pieces. The redistribution removes the loss of the estimate |Re⟨a, Ub⟩| ≤ ½(|a|² + |b|²).
- Phase VII introduced it for the chair. A randomized check confirms (B1) to 4·10⁻¹⁵ (`phase11_proofs.ims_random`).

### Theorem XI.C (the rate) [P; (v) assembled from cited results]
Let ε_G(R) be the infimum of ε(χ) over partitions as in B with every K_j inside some graph ball of radius R. Then for every unitary connection U of every rank:

  **(C0)  D_R(U) − ε_G(R) ≤ E_\*(U) ≤ D_R(U).**

- **(i) Property A.** ε_G(R) → 0 if and only if G has Yu's property A.
  - Proof: χ_x(v) := ξ_v(x) is a bijection between ℓ²-partitions of unity supported in R-balls and Higson–Roe ℓ²-maps ξ: V → ℓ²(V) with ‖ξ_v‖ = 1 and supp ξ_v ⊆ B_R(v). Under it, g_e = ‖ξ_v − ξ_w‖², so ε ≤ dδ²/(2 − δ²) when every g_e ≤ δ², and g_e ≤ 2ε/(1 + ε) in the other direction. For bounded degree, scale 1 suffices by the triangle inequality along geodesics.
  - This is a restatement of the partition-of-unity characterisation of property A (Higson–Roe 2000; Willett's notes; Špakula–Willett 2017), not a new theorem.
  - The operator-norm-localisation property, equivalent to A (Chen–Tessera–Wang–Yu 2008; Sako 2014), gives uniform *upper* bounds only.
- **(ii) Doubling.** If |B_{2r}(v)| ≤ C_D|B_r(v)| for all v and all integer r ≥ 1, then **ε_G(R) ≤ 16 d C_D²/R² for R ≥ 4C_D.**
  - Construction: χ_j = φ_j/√N with φ_j(v) = f(d(j, v)/R), f = 1 on [0, ½], 2(1 − t) on [½, 1], and 0 beyond.
  - Estimates: ‖a/|a| − b/|b|‖ ≤ 2‖a − b‖/|a| and |B_{R+1}| ≤ C_D²|B_{⌊R/2⌋}|. The constant was re-derived independently (§1).
- **(iii) Euclidean realisation.** Let c: V → ℝ^D be **proper** (finite preimages of bounded sets) with S_c := sup_v Σ_{w∼v}|c(v) − c(w)|² < ∞ and h := sup_{v∼w}|c(v) − c(w)|. Take the continuous partition χ_x(v) = φ((c(v) − x)/ρ)/(ρ^{D/2}‖φ‖), x ∈ ℝ^D, with φ the Dirichlet ground state of the unit ball (eigenvalue j_D²; j₁ = π/2, j₃ = π). Then
  - **g_e ≤ (j_D²/D)|c(v) − c(w)|²/ρ²** exactly, not only to leading order. By Plancherel, ∫|φ(y + t) − φ(y)|² ≤ ∫(k·t)²|φ̂|² = |t|²‖∇φ‖²/D for radial φ.
  - Hence **ε ≤ K_D(ρ)S_c/ρ², with K_D(ρ) = (j_D²/(2D))/(1 − j_D²h²/(2Dρ²))**.
  - The pieces are c⁻¹(B_ρ(x)). To enter (C0) they must lie in balls of bounded graph radius. For a tiling with centroid map c they lie in {a : |c(a) − c(t)| < ρ + r_c}, where t is the tile containing x.
  - For D = 3 this is exactly Phase X's Theorem X.7 constant K = (π²/6)/(1 − π²h²/(6ρ²)), with S₁ = 4734/49 and h = 15/7. The overlap function is now derived symbolically (`phase11_proofs.overlap3d`).
  - Existence of such a c with bounded pieces forces polynomial growth.
- **(iv) Sharpness.** On ℤ^D with the trivial connection, D_R − E_\* = λ^D(B_R) ≥ 2D(1 − cos(π/(2R + 2))) ≥ 2D/(R + 1)². So **no rate faster than R⁻² holds uniformly over connections**, and (ii), (iii) are optimal in their exponent.
- **(v) Bounded geometry alone does not give O(R⁻²).**
  - Take the Cayley graph of the lamplighter ℤ₂ ≀ ℤ^k with k ≥ 2. It is amenable, so E_\*(trivial) = 0, and it has property A.
  - Erschler's isoperimetric profile (Følner function ≍ exp(n^k)) gives inf_{|K|≤v}|∂K|/|K| ≥ c(log 2v)^{−1/k}.
  - The Dirichlet Cheeger inequality gives λ^D(K) ≥ h(K)²/(2·deg). With |B_R| ≤ (deg + 1)^R this yields **D_R − E_\* ≥ c_k R^{−2/k}**, hence ε_G(R) ≥ c_k R^{−2/k}.
  - So the rate is a large-scale geometric invariant of G, not a consequence of bounded degree and IMS.
- **(vi) Non-amenable graphs.** Kato's inequality ||ψ(v)| − |ψ(w)|| ≤ |ψ(v) − Uψ(w)| gives E_\*(U) ≥ λ₀(G) > 0 for every U. On such graphs positivity of the floor carries no information about frustration.

**Every dependence of the constants.**
- In (ii): only the degree bound d and the doubling constant C_D.
- In (iii): only D, S_c and h.
- None of them depends on the connection, its rank, the structure group, or the legal-environment set.
- The legal-environment set enters only through *which* balls the minimum runs over. That is Theorem D.

### Theorem XI.D (completeness of the legal environments of a frame-decorated chair substitution) [P + C]
Let r be any Chair44 decoration, proper or extended.
- **(i) Irreducibility.**
  - The frame-substitution digraph on the frames reachable from I is the Cayley digraph of the finite group generated by the child frames. It is therefore strongly connected (irreducible).
  - Its period is 1 for all 6561 proper rules (primitive, M² > 0 or M³ > 0; Phase X, re-checked) and 2 for the mirror twins 539311, 539291 and 539288 [C] (`phase11_chair.frame_graph`, recomputed independently).
- **(ii) Legal 1-star types.** Suppose the closure lemma holds on every type of the Φ-closure 𝒯 of the 1-star types of T₅: every child's 1-star lies inside σ of its parent's 1-star. This is asserted on every Φ step [C]. Then 𝒯 is the set of all legal 1-star types, with types taken up to global frames, mirrors included.
  - Proof: as in X.7. A legal patch lies in σᵏ(t). Irreducibility reaches t's frame from any frame, and the ancestor chain of a tile gives a Φ-chain of 1-stars.
- **(iii) Legal R-balls.** Every legal R-ball is the R-ball of a tile of the central level-m supertile of σᵐ(τ), τ ∈ 𝒯, provided the completeness check accepts that ball.
  - The check used here: the nearest cube not owned in the patch lies at distance ≥ R + √3/2 from the centroid. A centroid lies in a cube of its own tile, within (3/7)√3 < √3/2 of that cube's centre.
- **(iv) Imprimitive substitutions.** With period p > 1, the hull is the union of p minimal components related by global frames. Global frames preserve every link, since (gM)ᵀ(gn) = Mᵀn. So all components have the same language up to that equivalence, and E_\* is the same on all of them.
- **(v) Necessity of complete coverage.**
  - Enumerating only the environments *visible* in a finite supertile can produce a **false certificate**.
  - On the substitution ladder a → dd, b → cb, c → aa, d → bc (§6), the flat seam "cc" is legal but absent from σ¹⁰(a), which has 1024 letters.
  - The "certificate" computed from the visible environments claims E_\* ≥ 0.52194. A legal environment from the complete enumeration has exact upper bound 0.40789.
  - In Chair44, 1086 of the 1098 classes have legal 1-star types missing from T₅ (Phase X).

### Required distinctions: what determines what

| datum | determines E_\*? | gives a positive lower bound? | determines the density of states near E_\*? | proof |
|---|---|---|---|---|
| support (the environment language) | **yes**, in the limit R → ∞ (A1), monotonically (A2) | yes, when every legal environment of some radius is frustrated with an angle gap (Theorem F) | no | A, F |
| support at one fixed radius R | **no**, for any R (Theorem I) | yes under F's hypothesis | no | I |
| frequencies (any invariant measure) | **no**: E_\* does not depend on them (A2) | **no lower-semicontinuous functional of them can** (Theorem G) | they enter the IDS: for uniquely ergodic hulls the IDS is a frequency-weighted limit (Shubin; Lenz–Peyerimhoff–Veselić 2007) | A, G |
| spatial correlations (joint frequencies) | no (frequency-type) | no (Theorem G applies verbatim) | they enter the IDS moments | A, G |
| holonomy classes on plaquettes | no (X.5, and Theorem H on the ladder) | yes if no plaquette class is trivial (Theorem E), but the bound cannot distinguish connections sharing the class field | no | E, H, X.5 |
| complete holonomy representation of every ball | yes (it is the environment up to gauge: H1) | as for support | no | H |
| spectral floor E_\* | — | — | no: two hulls with equal languages but different invariant measures have equal E_\* and different IDS | A |
| density of states near E_\* | no: its edge is inf supp dN = E_\* only when the measure has full support (minimality) | — | — | A3 |

---

## 4. Quantitative curvature theorems and sharp obstructions (Part IV)

### Theorem XI.E (cycle-cover bound) [P]
Let 𝒞 be a family of simple cycles with weights w_C ≥ 0. Let θ_C ∈ [0, π] be the **minimal |argument| of an eigenvalue** of the holonomy of C, ℓ_C its length, and λ_C := 2(1 − cos(θ_C/ℓ_C)). Then

  **E_\*(U) ≥ inf_v Σ_{C∋v} w_Cλ_C / sup_e Σ_{C∋e} w_C.**

*Proof.*
- The free operator of an ℓ-cycle with holonomy W has spectrum {2 − 2cos((φ + 2πm)/ℓ)} over the eigenvalues e^{iφ} of W. Gauge all links but one to 1 and diagonalise W.
- Hence H^N_C ≥ λ_C.
- Then Σ_C w_C q_C ≤ (sup_e Σ_{C∋e} w_C)·q, and Σ_C w_C q_C ≥ Σ_v (Σ_{C∋v} w_Cλ_C)|ψ(v)|². ∎

Checked numerically for ℓ = 2, 3, 5, 8 with random U(2) holonomy, multi-edge two-cycles included (independent referee).

**A finite support statistic that gives a universal positive bound.**
- On ℤ³ every vertex lies in 12 plaquettes and every edge in 4.
- So for every Q₈-valued connection (spinor representation) **with no plaquette equal to +1**, E_\* ≥ 6(1 − cos(π/8)) = **0.456723**. The traceless class has angle π/2 and −1 has angle π.
- Among 20 000 random period-2 Pauli-frame fields, 8 789 have no trivial plaquette. The 60 that were evaluated have floors (Bloch, float) of at least 0.698, all above the universal bound 0.4567. The bound is valid and loose. The X.5 pair (8 trivial plaquettes per cell) gets the *same* cover bound 0.3045 for A and B: a valid bound that, being a function of the class field, cannot separate them.
- The statistic is support-type: *no trivial plaquette occurs*. Its frequency version fails (Theorem G).

### Theorem XI.F (loop transport and the flatness radius) [P]
- **(F1)** For each vertex v, let γ_v be a closed walk of length ℓ_v based at v whose holonomy W_v has θ_v := min|arg(eigenvalue)| > 0. Let m_e(γ) be the number of traversals of e. Then

  **E_\*(U) ≥ 1/κ,  κ := sup_e Σ_v m_e(γ_v) ℓ_v / (4 sin²(θ_v/2)).**

  *Proof.*
  - With the transports T_i along the walk, ψ(v) − W_vψ(v) = Σ_i T_i(ψ(x_i) − U(x_i→x_{i+1})ψ(x_{i+1})) by telescoping.
  - |(1 − W)ψ(v)| ≥ 2 sin(θ/2)|ψ(v)|.
  - Apply Cauchy–Schwarz, then sum over v. ∎
  - On 200 random graphs the ratio λ_min/bound is ≥ 1.0003 (`phase11_proofs.transport`): **the bound is attained up to 3·10⁻⁴ on single cycles.**
- **(F2) Flatness radius.** Suppose every ball B_r(v) is non-flat (the connection on the induced subgraph is not gauge-trivial), and every non-trivial holonomy of the fundamental loops of a breadth-first tree of B_r(v) has θ ≥ θ₀ > 0. Then

  **E_\*(U) ≥ 2 sin²(θ₀/2) / ((2r + 1) N_r),  N_r := sup_v |B_r(v)|.**

  - The fundamental loop has length ≤ 2r + 1 and traverses each edge at most twice.
  - The angle hypothesis holds for the spinor representation of a finite subgroup of SU(2), where θ₀ is the least non-identity angle: π/2 for Q₈, π/3 for the binary tetrahedral group, π/4 for the binary octahedral, π/5 for the binary icosahedral. It also holds for U(1) with finitely many legal environments.
  - **It fails in rank ≥ 2 without fixed-point-freeness.** On ℤ², U = diag(1, π-flux) has every 2-ball non-flat but E_\* = 0. The Q₈ adjoint representation fails the same way (§7).
- **(F3) Converse and the dichotomy.**
  - A flat ball B_R(x) gives E_\* ≤ λ^D_trivial(B_R(x)).
  - Let ω(R) := sup_x λ^D_trivial(B_R(x)). If ω(R) → 0 (ℤ^D; amenable Cayley graphs, since a Følner set F lies in B_{diam F} and λ^D(F) ≤ |∂F|/|F|), then for connections with an angle gap:

    **E_\* > 0 ⟺ r_flat := sup{r : some r-ball is flat} < ∞.**

  - Both directions are quantitative: 2 sin²(θ₀/2)/((2r + 1)N_r) ≤ E_\* ≤ ω(r_flat) for every r > r_flat.
  - On non-amenable graphs "⇒" fails (C(vi)).

**Chair44 application** (`phase11_local`, all 1098 classes):
- On the 292-class sample (the 100 classes with the largest Y₄ plus Phase X's preregistered random sample of 200; `phase11_local_census.jsonl`):
  - every legal centre of every sampled class has a frustrated two-cycle or triangle, so **E_\* ≥ 1/(3·25) = 0.0133** for each, by F2 with r = 1 and N₁ ≤ 25;
  - 202 classes have a frustrated two-cycle at *every* legal centre, so **E_\* ≥ min sin²(θ₂/2) = 1/2** by F1. These include 1387, 1389 and 1391, but not FR30 (three two-cycle-flat types).
- These closed-form bounds are valid but lose a factor ≈ 8–700 against the certified floors. Curvature-type bounds certify positivity, not extremality.

### Theorem XI.G (no lower bound from frequencies, at vanishing density) [P]
Let 𝒰 be the periodic Pauli-frame Q₈ connections on ℤ³. Two facts are used:
- constant frames give trivial links, since (σ·n)² = 1;
- 𝒰 is closed under replacing the frames on a cube.

The same holds for any class of periodic Γ-connections on ℤ^D that is closed under inserting a trivial patch, with constant 2D in place of 6.
- For every U ∈ 𝒰 and every r there are U_s ∈ 𝒰 such that:
  - the frequency vector p_r(U_s) of radius-r environments tends to p_r(U) in total variation;
  - **E_\*(U_s) ≤ 6(1 − cos(π/(s + 1))) → 0.**
- *Construction:* constant frames on one s-cube per period cell of side s²·per(U).
- *Consequence:* let F be lower semicontinuous in total variation, with E_\* ≥ F(p_r) on 𝒰. Then F ≤ 0 at every p_r(U). Every frequency-type lower bound is trivial.
- Measured (`phase11_z3.islands`): island sides s = 2, 3, 4, 6 at periods 6, 10, 16, 30. The total-variation distance of the radius-1 plaquette-environment frequencies from the base connection is 0.236, 0.117, 0.048, 0.018, while E_\* ≤ 3.000, 1.757, 1.146, 0.594 (exact product-sine Rayleigh quotients, equal to the closed form 6(1 − cos(π/(s + 1)))).
- Theorem F escapes this because its hypothesis, *no flat r-ball*, is discontinuous in the frequencies at frequency 0.

### Theorem XI.H (what holonomy data determine) [P]
- **(H1)** On a connected graph, U and U′ are gauge-equivalent iff their based holonomy representations π₁(G, x) → U(n) are conjugate. An environment up to gauge is therefore the ball together with the conjugacy class of its holonomy representation.
- **(H2)** For an Abelian structure group, holonomies on a family 𝒫 that generates H₁(G; ℤ) **over ℤ** determine U up to gauge.
  - Generation mod 2 is not enough: a U(1) connection twisted by a k-th root of unity on one cycle is invisible to a sublattice of odd index k.
  - On ℤ³, plaquettes generate over ℤ.
- **(H3)** For finite Γ and any unitary representation π, π∘U ≅ ⊕_ρ m_ρ(ρ∘U), so E_\*(π∘U) = min_{m_ρ>0} E_\*(ρ∘U).
  - For Q₈, Irr = {1, χ₁, χ₂, χ₃, spin}, and **the adjoint (SO(3)) representation is χ₁ ⊕ χ₂ ⊕ χ₃** (`phase11_proofs.q8`).
  - On ℤ³ every non-spinor representation's floor is therefore a function of the plaquette conjugacy-class field. **The X.5 phenomenon lives entirely in the spinor component.**
  - Verified on the X.5 pair: the adjoint floors are equal (both 0, since the shadow χ₃ is flat). The spinor floors differ by a certified 0.18.
- **(H4)** Plaquette conjugacy classes cannot distinguish an element from its conjugates. The ladder realises X.5 with two connections whose holonomy *groups* are both Abelian: a Fibonacci word of q₁ and −q₁, against constant q₁ (§6).
  - What the phenomenon needs is a non-Abelian **structure group**, where q₁ ~ −q₁, not non-Abelian holonomy.

### Theorem XI.I (no finite radius determines the floor) [P + C]
- On the ladder with Z₂ ⊂ Q₈ links, let A_m be the periodic plaquette word (aᵐb)^∞, with a = +1 and b = −1.
- A radius-R environment is a window of 2R plaquettes. For m ≥ 2R all A_m share the same radius-R language: every 2R-letter word with at most one b, in every position.
- Each E_\*(A_m) > 0 by F2: balls of radius ⌈(m + 3)/2⌉ are non-flat.
- E_\*(A_m) ≤ 2(1 − cos(π/(m + 2))) → 0, by the sine bump on the flat stretch, equal on both rails.
- **So for every R the radius-R language does not determine E_\*.**
- Certified instance: A₂₄ and A₃₂ have the same radius-12 language, and E_\*(A₂₄) ≥ 0.013200 > 0.008176 ≥ E_\*(A₃₂) (§6).
- Phase X's question "which finite list of local curvature statistics suffices" therefore has answer *none* for determination. For a *positive lower bound*, the answer is support-type statistics with an angle gap (F) and never frequency-type ones (G).

## 5. Why the best candidate is strong (Part V)

**Method** (`audit/phase11_mechanism.py`, `audit/phase11_local.py`).
- For each rule, the legal 8-balls are enumerated and each gets its plain bottom (D₈) and its amplified bottom (Λ₈).
- The minimising balls are analysed through gauge-invariant data:
  - the holonomy angles of the two-cycles and triangles at the centre;
  - the two-cycle and plaquette class counts of the ball;
  - a *fingerprint* (geometric configuration, Dirichlet spectrum). Equal fingerprints are necessary for gauge equivalence.
- Every rule's tilings have the undecorated chair geometry, because frames only relabel. So environments of different rules on the same geometric configuration can be compared.

### 5.1 The weakest legal environments

| rule | legal 8-balls (gauge-distinct) | D₈ | Λ₈ | centre of the minimising ball: largest two-cycle angle θ₂, triangle angle θ₃ | radius-1 types whose centre has **no non-trivial two-cycle** |
|---|---|---|---|---|---|
| FR30 (4752) | 747 (415) | 9.05152 | 6.56278 | **θ₂ = 0**, θ₃ = π | **3** |
| 1387 (member 4753) | 1450 (1450) | 9.72987 | 7.31150 | θ₂ = π/2, θ₃ = π | **0** |
| 1389 | 1431 | 9.46211 | 7.00915 | θ₂ = π/2, θ₃ = π | 0 |
| 1391 | 1614 | 9.40093 | 6.91984 | θ₂ = π, θ₃ = π | 0 |
| 539311 (twin) | 1450 (1450) | 9.75356 | 7.33782 | θ₂ = π, θ₃ = π | 0 |
| 539315 (FR30 mirror) | 747 (415) | 9.05152 | 6.56278 | identical to FR30 | 3 |
| 937 | 3576 (3562) | 8.28032 | 5.62961 | θ₂ = π/2 | 0 |
| 938 | 3576 (3562) | 8.04612 | 5.38273 | θ₂ = π | 0 | | | | | |

**Answers to the brief's questions.**
1. **Which environment attains the localisation minimum?**
   - For FR30, the same ball minimises both D₈ and Λ₈. Its centre is one of the three tile types whose two-cycles all have trivial holonomy: a tile frustrated only through triangles.
   - For 1387 the minimising ball's centre carries a traceless two-cycle.
2. **Its local holonomy structure.** FR30's minimising 8-ball (291 tiles):
   - two-cycle classes +1 : traceless : −1 = 2790 : 183 : 55;
   - plaquette classes 2222 : 1503 : 353.

   1387's minimising ball (314 tiles):
   - two-cycles 3040 : 262 : 43;
   - plaquettes 2297 : 1690 : 357.

   The frequencies differ little, and frequencies cannot bound the floor in any case (Theorem G). What differs is support: **no tile of 1387 lacks a frustrated two-cycle.**
3. **How does the one-child intervention change the environment** (centre child of FR30 reframed, 4752 → 4753)?
   - The geometric configurations are unchanged: 16 one-star shapes and 153 eight-ball shapes in both rules.
   - **Every gauge class changes**: 0 of FR30's 72 radius-1 environments and 0 of its 415 radius-8 environments occur in 4753.
   - **On every one of the 16 geometric 1-star configurations, both the worst local energy U₀ and the worst inflated energy U₁ rise.** For example, U₁ goes from 9.3484 to 10.0583 on FR30's U₁-minimising configuration, and from 9.3587 to 10.0160 on its two-cycle-flat configuration (table in `phase11_mechanism.json:compare_4752_4753.per_shape`).
4. **Raise, removal, or localisation correction?**
   - **Raise.** The minimum environment energy rises uniformly over the geometric configurations.
   - Formally every environment is "removed", because its gauge class is replaced. That is a relabelling, not the deletion of one rare weak environment.
   - The localisation correction is **unchanged**. The IMS constants depend only on the geometry (S₁ = 4734/49, h = 15/7, r_c), which is identical for every decoration.
   - The preregistered prediction P4 ("removal rather than a raise") is therefore **true in its literal gauge-class sense and uninformative**. The informative description is the uniform raise.
5. **Which mechanism generalises?** Tested on the preregistered neighbour sets and the census sample:
   - *Tiles without a frustrated two-cycle* (post hoc). On Phase X's preregistered random sample of 200 classes, which was not used to form the hypothesis:
     - 69 classes have such tiles. Their median Y₅ is 6.915, against 7.553 for the 131 classes without, Mann–Whitney p = 4·10⁻¹¹.
     - The Spearman correlation of the flat-type fraction with Y₄ is −0.45.
     - Around FR30 the flat-type count correlates with Y₅ at −0.58. Around 4753 it correlates at +0.32: locally the association is not robust.
     - **It is an association, not a criterion.** FR30 has such tiles and lies just outside the frontier. Among the top 20 classes by Y₄, four have them (1386, 1390, 900, 1147).
   - *The uniform raise of the worst local energy.* It generalises in the sense of P1–P2 below: the radius-1 worst energy U₁ orders single-child neighbours almost perfectly.
   - *The orbit structure.* It generalises to every class: each class has a right-S₃ orbit (§2.3). The frontier is one such orbit.
6. **Can the candidate be predicted before the global eigensolve?** Scored against the preregistered predictions. The predictors U₁, θ₂ and type counts were committed (6dea96b) before any Y₅ outcome was computed. Neighbours in the base's own gauge class are isospectral and are compared as ties (tolerance 10⁻⁸, fixed and committed before the outcomes: 159ff0f).

   | prediction | FR30 neighbourhood (22 rules) | 4753 neighbourhood (39 rules) | verdict |
   |---|---|---|---|
   | P1: Spearman(U₁, Y₅) ≥ 0.8 | **0.883** | **0.915** | pass |
   | P2: sign(ΔU₁) = sign(ΔY₅) for ≥ 80 % | **100 %** | **100 %** | pass |
   | P3: the best-Y₅ neighbour is among the top 3 by U₁ | the best neighbour is **1387** (184323), first by U₁ | the best neighbour is a member of 4753's own class (isospectral, a tie). The best other-class neighbour is 1391 (184342), second by U₁ | pass (trivially for 4753) |
   | P4: the intervention removes FR30's weak environment rather than raising it | — | — | literally true but uninformative (every environment's gauge class changes); the informative description is the uniform raise (item 4) |

   **A finding outside the predictions.**
   - Only 2 of FR30's 22 single-child neighbours have a higher Y₅: 1387 and 1389.
   - **None of the 38 non-trivial single-child changes of 4753, proper or improper, raises Y₅.** The rule 1387 is a local maximum of Y₅ in the single-child neighbourhood (finite level, exact bounds).

### 5.2 The three outcomes, separated

- **A correlation that identifies promising candidates:**
  - U₁: Spearman 0.88–0.92 on single-child neighbourhoods, 100 % sign accuracy, 77.5 % on twins.
  - The absence of two-cycle-flat tiles: p = 4·10⁻¹¹ on the random sample.
  - The right-S₃ orbit, which contains the whole certified frontier.
- **A sufficient criterion that guarantees a lower bound:** only the certified ones (Λ_R; the closed-form bounds E, F). These are sufficient but far from sharp: Theorem F certifies E_\*(1387) ≥ 1/2 (two-cycle transport) against the true floor ≈ 9.36.
- **A necessary-and-sufficient characterisation of the extremiser:** **not obtained, and not claimed.** Theorem I shows that no fixed-radius datum can provide one in general.

## 6. A second geometry: substitution ladders (Part VI)

**The system** (`audit/phase11_ladder.py`). It is defined without reference to Chair44.
- **Graph:** the ladder ℤ × {0, 1}, with rails and rungs; degree 3; quasi-one-dimensional; bipartite. The plaquettes generate H₁ over ℤ.
- **Connection:** a bi-infinite word x over an alphabet and a map X from letters to U(k), for k = 1, 2, 3. The bottom rail and the rungs carry the identity; the top link (n, 1) → (n + 1, 1) is X(x_n).
  - Every connection on the ladder is gauge-equivalent to one of this form.
  - Two such connections are gauge-equivalent iff their words agree up to one global conjugation.
- **Words:** fixed points of substitutions (Fibonacci a → ab, b → a; others below) or periodic words.
- **Legal environments of radius W:** the factors of length 2W, enumerated completely by the 2-letter closure, the ladder analogue of the Φ-closure.
- **IMS:** D = 1, c(n, s) = n, cutoff cos(πy/2). Its overlap C(t) = (1 − t/2)cos(πt/2) + sin(πt/2)/π is derived symbolically. Rails are amplified by 1/C(1/W); rungs are not, since |Δc| = 0.
  - Hence Λ_W ≤ E_\* ≤ D_W, with D_W − Λ_W ≤ 2(1/C(1/W) − 1) ≈ π²/(4W²).
- **Certificates:** banded Higham Cholesky for Λ_W; exact rational Rayleigh quotients (Gaussian-integer entries) for D_W.

**What differs from Chair44.**
- Dimension 1 against 3; degree 3 against 24.
- No frames and no Pauli formula: the links are prescribed directly.
- Any finite subgroup of SU(2), or U(1).
- A different substitution, with legal environments that are words.

**Results** (`audit/results/phase11_ladder.json`).

| test | result | status |
|---|---|---|
| support principle and rate (Fibonacci; link assignments (q₁, q₂), (q₁, −q₁), (q₁, q₁), (−1, q₁); W = 4 … 512) | 2W + 1 legal environments at every W (Sturmian complexity, complete by the closure). **The certified width D_W − Λ_W falls by a factor 3.9–4.0 per doubling of W (W ≥ 8), at 0.77–0.94 of the proved bound π²/(4W²)**, so the constant of C(iii) is essentially attained. At W = 512: E_\*(q₁, q₂) ∈ [0.3486180, 0.3486265] and E_\*(q₁, −q₁) ∈ [0.2535155, 0.2535243], widths 8.5·10⁻⁶ and 8.9·10⁻⁶. The upper side D_W − E_\* also decays like W⁻², a quadratic band edge. The Chair44 supertile and ball sequences approach faster, with exponents ≈ 2.4–2.8 (§12) | [C] |
| **class-field insufficiency** (the analogue of X.5): Fibonacci word with X(a) = q₁, X(b) = −q₁, against the constant q₁ ladder. Every plaquette is in the Q₈ class {±q₁} in both, and the shadows χ_k coincide letter by letter | E_\*(Fib q₁/−q₁) ∈ [0.2535055, 0.2535409], E_\*(const q₁) ∈ [0.5504947, 0.5505254], **certified separation 0.29695**. Both holonomy groups are Abelian (⊂ ⟨q₁⟩ ≅ ℤ₄) | [C] |
| **no finite radius determines E_\*** (Theorem I) | A_m = (aᵐb)^∞, a = +1, b = −1. Certified enclosures at W = 64: m = 1: [0.585613, 0.586124], m = 2: [0.410878, 0.411394], …, m = 24: [0.013200, 0.013795], m = 32: [0.007579, 0.008176], m = 64: [0.001617, 0.002216]. A₂₄ and A₃₂ share the radius-12 language | [P + C] |
| **Π has no closed recursion** | A₆, A₉: identical radius-3 languages, so identical Π₃ (D₃ = 0.1522409 in both); radius-4 languages differ; D₄ = 0.1300649 against 0.0978870 (exact) | [C] |
| **Neumann windows fail** (A1 remark) | π-flux ladder: free windows → 2 − √2 = 0.585786 < 3 − √5 = 0.763932 = E_\*. π/2-flux: → (3 − √5)/2 < 3 − √6 | [P + C] |
| **legal-patch coverage is necessary** (D(v)) | a → dd, b → cb, c → aa, d → bc: 'cc' is legal, first appearing in σ¹¹(a). With a, b, d = −1 and c = +1, the visible-only "certificate" from σ¹⁰(a) (1024 letters) claims Λ ≥ 0.4905, 0.5142, 0.5204, 0.5219 at W = 8, 16, 32, 64. The complete enumeration has a legal environment with exact bound ≤ 0.40789. **Each visible-only certificate is false.** With a, b, d = q₁ the visible certificate is false at W ≥ 16 | [C] |
| **minimality** (A3) | a → aab, b → bb (reducible), a = +1, b = −1: E_\* ≤ 0.40816 on the fixed point's orbit closure, while b^∞ ∈ Ω has E_\* = 3 − √5 = 0.76393. E_\* is not constant on a non-minimal hull | [C] |
| **representation** (H3) | Fibonacci (q₁, q₂): spinor E_\* ∈ [0.348565, 0.348699]. The adjoint (SO(3)) floor ∈ [0.393406, 0.393537] equals the χ₁-shadow floor [0.393406, 0.393537], the smallest of the three shadows (χ₂: 0.49515…, χ₃: 0.76393…). **Here the non-Abelian floor lies below every shadow**, the opposite of FR30 | [C] |
| **group (angle gap)** | X(a), X(b) = rotations about x and y with holonomy angle θ: E_\* ≈ 0.7639, 0.3486, 0.1049, 0.0272, 0.0068 for θ = π, π/2, π/4, π/8, π/16 (certified enclosures of width ≤ 1.5·10⁻⁴). **E_\* ≈ cθ² → 0 continuously.** Without a finite group's angle gap, no frustration bound of the form of F survives | [E]: the link entries are irrational and rounded to double, so these enclosures are certified only for the rounded matrices |

**Transfer theorem** (what depends on what). Each row is backed by a proof, or by a certified counterexample on one of the two geometries.

| result | depends on the chair geometry and degree 24? | on Q₈? | on the 2-dim spinor representation? | on the substitution rule? | on minimality or irreducibility? | on the particular legal set? |
|---|---|---|---|---|---|---|
| support principle A | no (bounded degree only) | no | no | no | E_\* constant on the hull: minimality, or components permuted by symmetries of H (ladder counterexample a → aab) | E_\* is a function of it (A2) |
| rate C | through D, S_c, h only (or C_D); R⁻² needs polynomial-growth-type geometry (lamplighter counterexample) | no | no | no | no | no |
| completeness D | the closure lemma is a geometric check | no | no | the Φ-closure is per substitution | irreducibility (automatic for frame substitutions; Cayley digraph) | the enumeration must be complete: a false certificate otherwise |
| positivity of every rule (Phase X X.3 census) | **yes**: the chair forces rotated children. On ℤ³ the frame substitution with identity children gives constant frames, trivial links and E_\* = 0; a ladder word aᵐ gives E_\* = 0 | partly (via the angle gap) | yes: in the adjoint representation a non-flat Q₈ connection can have a zero mode (H3) | — | — | — |
| frustration bounds E, F | no; constants through N_r and the cycle cover | **angle gap needed**: θ² scaling for SU(2) letters | **fixed-point-freeness needed** (diag(1, V) counterexample) | no | no | via the flatness radius of the legal set |
| frequency no-go G | needs a flexible class (islands insertable) | no | no | does not apply inside a rigid substitution family | — | — |
| class-field insufficiency (X.5) | no (ℤ³ and ladder) | needs a non-Abelian structure group (classes ≠ elements) | **confined to the spinor component** (H3); fails in the adjoint representation | no | no | no |
| X.5 needs non-Abelian holonomy? | — | — | — | — | — | **no**: the ladder pair has Abelian holonomy groups |

**A universality claim is not made from these examples.**
- The universal statements (A–I) are proved, and the examples only test them.
- The Chair44-specific statements (census-wide positivity, the extremal frontier, the mechanism) are not claimed to transfer. The table records which hypothesis each one uses.

## 7. The abstraction: the certified local frustration profile (Part VII)

**Definition.** For a connection (or hull) with environment language 𝓛, its **certified local frustration profile** is the nested sequence of intervals

  **Π_R := [L_R, U_R],  U_R = min_{R′≤R} D_{R′},  L_R = max_{R′≤R} Λ_{R′},**

where:
- D_R is the minimum, over legal R-environments, of the Dirichlet bottom;
- Λ_R is the minimum of the IMS-amplified bottom (Theorem B), for a fixed admissible partition family: graph partitions as in C(ii), or the Euclidean family of C(iii);
- each endpoint carries its certificate (exact rational, or Higham-bounded).

It stores two numbers per scale, not the operator, the spectrum, or the environments themselves.

| property | holds? | proof or evidence |
|---|---|---|
| 1. gauge-invariant | **yes** | local operators change by unitary conjugation |
| 2. invariant under graph and geometric symmetries | **yes** | environments are taken up to rooted isomorphism (for Chair44: global frames, mirrors included) |
| 3. monotone under enlargement | **yes**, the intervals are nested by construction. D_R is intrinsically non-increasing (A1). Λ_R itself need not be monotone, because the cutoff changes with R | A1 |
| 4. sufficient for the finite-level spectrum | **no** | two numbers per scale. The finite-level bottoms Y_L of 937/938 are certified different (Phase IX), and Π distinguishes them only through D_R. Nothing in Π recovers Y_L |
| 5. bounds the infinite-volume floor | **yes, two-sided**, E_\* ∈ Π_R for every R, with width ≤ ε_G(R) → 0 under property A, O(R⁻²) with explicit constants under C(ii)/(iii) | C |
| 6. stable under substitution | **refinement rule yes; finite-dimensional closure no.** For a substitution hull every Π_R is computed from the finite Φ-closed set 𝒯 by inflating m = ⌈log₂R⌉ (or +1) times (D). But no map Ψ satisfies Π_{R+1} = Ψ(Π_R): A₆ and A₉ on the ladder have identical radius-3 languages and therefore identical Π₃, while D₄ = 0.130065 against 0.097887 (exact rationals) | D, I, `phase11_ladder.json:profile_no_recursion` |
| 7. computable without the global eigenproblem | **yes**: #legal balls × one banded Cholesky. On the chair, #balls ∝ R³ and the cost per ball ∝ R⁷ (bandwidth ∝ R², size ∝ R³), so R¹⁰ in total. Measured: 7527 balls at R = 14 in 4.4 min and 10 321 at R = 15 in 16 min on 4 cores | §2 |

**The equivalence relation.**
- Call r ≈ r′ when 𝓛(r) = 𝓛(r′) up to gauge and rigid motion. ≈ preserves E_\* (A2).
- Π-equivalence at all R (equal limits) is exactly E_\*(r) = E_\*(r′), the coarsest relation that preserves E_\*.
- At a fixed R, Π_R-equivalence does **not** preserve E_\* (Theorem I).

**The mandatory falsification tests.**
- **ℤ³ pair (X.5).** Identical Q₈ class on every plaquette, so every class-field invariant is constant on the pair.
  - Π separates them at R = 5: Λ₅(B) ≥ 1.014237 (certified) > 0.404135 ≥ E_\*(A).
  - This improves the Phase X separation from 0.18 to **0.61** (`phase11_z3.json:profile`).
  - Any abstraction built from plaquette data fails this test. Π passes.
- **937/938.**
  - The pair has identical plaquette and two-cycle class counts, and certified different finite-level bottoms (Phase IX).
  - Π separates their radius-8 environment minima: Π₈(937) = [5.6296, 8.2803] against Π₈(938) = [5.3827, 8.0461] (float endpoints). The radius-1 data separate them as well (U₁ = 8.5958 against 8.3667). They share all 153 geometric 8-ball shapes and none of their 3562 gauge-distinct 8-environments.
  - Their intervals overlap at feasible R. E_\*(937) ≠ E_\*(938) is **not** known, and Π does not claim it.
- **The ladder pair (q₁, −q₁) versus constant q₁.** Identical class field and identical shadows; Π separates them at W = 8 already (§6).

**The obstruction, stated precisely.**
- (a) No functional of the environment language at one fixed radius determines E_\* (Theorem I).
- (b) No lower-semicontinuous functional of environment frequencies bounds E_\* below (Theorem G).
- (c) No map carries Π_R to Π_{R+1} (property 6).
- So a compact abstraction that determines the floor **does not exist** at any fixed scale.
- What exists is a refinement rule with a proved rate (C). On families with local matching rules the radius-1 language determines the hull, and hence E_\*, *informationally* (FR30: Kamenetsky's Theorem A). Even there, E_\* is only reached as the limit of Π.
- The profile is therefore the right object: it is the minimal certified interval-valued invariant compatible with (a)–(c), and it is falsified by neither mandatory test.

## 8. Novelty and physical scope (Part VIII)

**Primary-literature check.** A separate search was run (results summarised here).
- WebFetch and direct downloads were blocked from this container, so statements were checked against search extracts of arXiv abstract pages and journal records.
- Theorem numbers marked † were seen only as citations in later papers.

| Phase XI result | closest known result | exact difference | category |
|---|---|---|---|
| XI.A support principle: D_R ↓ E_\*, antitone in the language | the variational principle. Spectra of operators on subshifts depend only on the subshift and vary continuously with it (Beckus–Bellissard–De Nittis, JFA 275 (2018) 2917; Beckus–Bellissard–Cornean, AHP 20 (2019) 3603). Right limits (Last–Simon, J. Anal. Math. 98 (2006) 183) | an elementary statement for inf σ of connection Laplacians on arbitrary bounded-degree graphs. The content is the explicit separation of support from frequencies | **1** |
| XI.B exact IMS identity, amplified-link form | the IMS formula (Simon, Ann. IHP A 38 (1983); Cycon–Froese–Kirsch–Simon ch. 3). Metric partitions of unity (Špakula–Willett, Trans. AMS 369 (2017) 263) | an algebraic rewriting of the double commutator that removes one inequality loss. Introduced for the chair in Phase VII | **1** |
| XI.C(i) uniform two-sided localisation ⟺ property A | Higson–Roe, J. reine angew. Math. 519 (2000); Willett, "Some notes on property A" (2009), the list of equivalences in §1.2†; Špakula–Willett Def. 6.1. ONL ⟺ A: Chen–Tessera–Wang–Yu, Adv. Math. 218 (2008); Sako, J. reine angew. Math. 690 (2014) | a restatement of the ℓ² partition-of-unity characterisation in spectral-floor form. **Not new** | **1** |
| XI.C(ii)–(iii) O(R⁻²) with explicit constants | standard Lipschitz partitions; the Phase VII chair constant | general D and explicit K_D(ρ). The Fourier bound has no higher-order term | **1** (constants: 2) |
| XI.C(iv)–(v) R⁻² is sharp; lamplighters give R^{−2/k} | Erschler, Geom. Dedicata 100 (2003) (isoperimetric profile of wreath products, via later citations); Dodziuk, Trans. AMS 284 (1984); Pittet–Saloff-Coste, Ann. Probab. 30 (2002); Coulhon–Grigor'yan–Pittet, Ann. Inst. Fourier 51 (2001) | assembled consequence: bounded degree plus IMS does not yield O(R⁻²) | **1** (assembly: 2) |
| XI.C(vi) E_\*(U) ≥ λ₀(G) | Kato / diamagnetic inequality (Dodziuk–Mathai, Contemp. Math. 398 (2006)) | — | **1** |
| XI.D completeness via Φ-closure, and its necessity | collared tiles (Anderson–Putnam); Phase VII §6.1 | the demonstration that a visible-only enumeration yields a false certificate | **1** (method), **2** (demonstration) |
| XI.E cycle-cover bound | frustration-index Cheeger inequalities: Lange–Liu–Peyerimhoff–Post, Calc. Var. PDE 54 (2015) 4165 (finite graphs, U(1), normalised); Bandeira–Singer–Spielman, SIMAX 34 (2013) 1611 (λ₁ ≤ η ≤ 44√λ₁, finite graphs) | infinite graphs, closed form in holonomy angles and loop lengths, any rank. Elementary; possibly folklore | **2** |
| XI.F loop transport and the flatness-radius dichotomy | continuum: Kondratiev–Maz'ya–Shubin, Comm. PDE 34 (2009) (strict positivity of magnetic operators via a uniform condition on cubes). Discrete: Bonnefont–Golénia–Keller–Liu–Münch, AHP 21 (2020) (magnetic sparseness: form domain and discreteness, not positivity) | **no discrete "positive floor iff uniformly non-flat balls" statement was found**. The explicit constant 2 sin²(θ₀/2)/((2r+1)N_r), the angle-gap hypothesis, and the rank ≥ 2 counterexample to its removal. The proof is elementary | **3 (weak)**: likely new as stated, but elementary |
| XI.G frequency no-go at vanishing density | Lifshitz tails and the rare-region mechanism; Phase X X.4 | density → 0 and the lower-semicontinuity formulation | **2** |
| XI.H3 representation reduction; X.5 lives in the spinor component | representation theory of Q₈ | the consequence for X.5 is new to this project | **1** (fact), **2** (consequence) |
| XI.H4 / ladder: X.5 with Abelian holonomy groups | — | explicit certified example | **2** |
| XI.I no finite radius determines E_\*; Π has no closed recursion | elementary | explicit certified pairs | **2** |
| free (Neumann) windows saturate below E_\* (π-flux ladder: 2 − √2 against 3 − √5) | de Gennes / surface superconductivity Θ₀ < 1 (Fournais–Helffer, *Spectral Methods in Surface Superconductivity*, 2010; continuum) | **no lattice analogue was found in the search**. Exact closed forms on a graph | **2** |
| Chair44 frontier: 1387 certified above FR30 and 1095 classes, independent re-certification, the extended-space certified funnel | none: no spectral study of Chair44 rules exists. Kamenetsky (arXiv:2610.00916) studies matching rules, not spectra | new computation | **2** |
| the 1387 mechanism (every geometric 1-star configuration raised; two-cycle-flat tiles eliminated) | none | structural observation, tested against preregistered predictions | **2 / [E]** |
| Kenyon, Ann. Probab. 39 (2011) 1983 (Theorems 8, 9†) | determinant of the connection Laplacian over cycle-rooted spanning forests weighted by Π(2 − tr w) | context for why plaquette data cannot suffice | context |
| Lieb–Loss, Duke 71 (1993) 337 | extremises the half-filled band energy and the determinant, not λ_min | context | context |

**Category summary.**
- *Established machinery*: A, B, C(i)–(vi) as mathematics; D as a method.
- *New application to a specified family*: every Chair44 statement, and D(v).
- *Genuinely new theorem or counterexample, in the weak sense of not found in the literature*: F's discrete dichotomy with explicit constants; the representation-theoretic localisation of X.5; the Neumann-window counterexample with exact values; the finite-radius obstruction with certified pairs.
- *Numerical discoveries*: the extended-space frontier and the mechanism.
- *Physical conjecture*: **none**.

**Physical scope.**
- A positive floor of a covariant graph Laplacian is a statement about one discrete operator.
- No quantum dynamics, field theory, particle spectrum or physical law follows from it.
- A physical proposal would need an independently specified dynamical model, a continuum or thermodynamic limit, and observables with testable consequences. None is proposed here.

## 9. Failed conjectures, corrections and negative results

| # | statement | verdict | evidence |
|---|---|---|---|
| 1 | "bounded geometry plus an IMS identity give an O(R⁻²) floor approximation" | **[F]** | lamplighter ℤ₂ ≀ ℤ^k: rate ≥ c R^{−2/k} (C(v)). R⁻² needs doubling or a Euclidean realisation |
| 2 | "Neumann (free) local operators converge to the floor" | **[F]**, exactly | π-flux ladder: limit 2 − √2 against E_\* = 3 − √5 |
| 3 | "environments visible in a large training supertile suffice for a certificate" | **[F]** | a false certificate on the ladder (0.522 claimed, ≤ 0.408 true) |
| 4 | "a non-flat SU(2)/U(n) connection on every ball has a positive floor" | **[F] in rank ≥ 2** without fixed-point-freeness | ℤ², diag(1, π-flux); the Q₈ adjoint representation |
| 5 | "some finite list of local curvature statistics determines the floor" | **[F]** | Theorem I (any fixed radius), X.5, and H4 (plaquette classes) |
| 6 | "frequency-type statistics give a positive lower bound" | **[F]** | Theorem G (vanishing island density) |
| 7 | "X.5 needs non-Abelian holonomy" | **[F]** | the ladder pair has Abelian holonomy groups; a non-Abelian structure group suffices (H4) |
| 8 | "non-Abelian holonomy raises the floor above its shadows" | **[F]**, again | Fibonacci (q₁, q₂) ladder: spinor floor 0.3486 below every shadow (0.3934, 0.4952, 0.7639) |
| 9 | "every frame rule has a positive floor" as a geometric universal | **[F]** outside the chair | on ℤ³ the identity-frame cube substitution is flat. On the chair it holds because the geometry forces rotated children |
| 10 | Phase X ledger: the 1387 bound at R = 14 is the strongest | **corrected** | R = 15 independently verified (8.7999990) and carried into the ledger and tests |
| 11 | Phase X: the twin is certified above FR30 | **correct but conditional** | it used the Phase VIII bound (vector not stored). Made independent only by the twin's R = 15 certificate: **passed**: all 10 321 balls of 539311 at R = 15, E_\*(539311) ≥ 8.7999990 > 8.7970113 = Y₅(FR30), independent |
| 12 | Phase X: the ℤ³ trace-pair shadow bound is certified | **reclassified [E]** | the Lipschitz branch-and-bound uses float eigenvalues with a heuristic margin |
| 13 | Phase X X.7: "O(R⁻²) uniformly in the rule" | **correct, now general** | a special case of C(iii), with every constant now derived symbolically |
| 14 | preregistered P1–P4 (Part V) | **P1–P3 pass**; P4 is literally true and uninformative | §5 |
| 15 | preregistered twin criterion | 31/40 correct (77.5 %, 95 % CI [0.62, 0.89]): a **correlation**, and the criterion is ill-posed on gauge classes (§2.3) | §2.3 |

## 10. Decision table

| claim | status | where |
|---|---|---|
| XI.A: E_\* = lim D_R over legal environments; antitone in the language; frequency-free (bounded degree only) | **proved** | §3 |
| XI.B: exact IMS identity in amplified-link form; Λ ≤ E_\* ≤ D | **proved** (randomized identity check 4·10⁻¹⁵) | §3 |
| XI.C(i): uniform IMS localisation ⟺ property A | **proved** (a restatement of known characterisations) | §3 |
| XI.C(ii)–(iii): O(R⁻²) with explicit constants (doubling 16dC_D²/R²; Euclidean K_D S_c/ρ²) | **proved**; independent referee rechecked every constant | §3 |
| XI.C(iv): R⁻² is optimal (ℤ^D) | **proved** | §3 |
| XI.C(v): bounded geometry + IMS do not give R⁻² (lamplighter, R^{−2/k}) | **proved from cited results** (Erschler 2003, Dodziuk 1984) | §3 |
| Neumann windows do not converge (π-flux ladder: 2 − √2 ≠ 3 − √5) | **proved + certified** | §3, §6 |
| XI.D: completeness of Φ-closed enumerations; necessity (a false visible-only certificate) | **proved + certified** | §3, §6 |
| XI.E: cycle-cover bound; ℤ³ with no trivial Q₈ plaquette has E_\* ≥ 0.4567 | **proved** | §4 |
| XI.F: loop-transport and flatness-radius bounds; E_\* > 0 ⟺ finite flatness radius (angle gap, amenable-type graphs) | **proved**; rank ≥ 2 counterexample to removing the angle gap | §4 |
| XI.G: no lower-semicontinuous frequency functional bounds E_\* | **proved** (vanishing density) | §4 |
| XI.H3: non-spinor floors are functions of the plaquette class field; X.5 lives in the spinor component | **proved**, verified on the X.5 pair | §4 |
| XI.I: no fixed radius determines E_\*; Π has no closed recursion | **proved + certified** (A₂₄/A₃₂; A₆/A₉) | §4, §7 |
| Phase X R = 15 certificate for 1387 (≥ 8.7999988) | **independently re-certified** (≥ 8.7999990) | §1 |
| Phase X R = 14 (1387, twin) and Phase VII R = 12 (FR30) certificates | **independently re-certified** | §1 |
| E_\*(1387) > E_\*(FR30) without unstored artifacts | **certified** (separation ≥ 0.0357719 with the independent U₅(FR30); ≥ 0.0029876 from Y₅ alone) | §1 |
| E_\*(539311) > E_\*(FR30) without unstored artifacts | **certified** (R = 15 twin certificate) | §2 |
| E_\*(1389) > E_\*(FR30) | **certified without artifacts** (R = 16 certificate against the independent exact U₅(FR30) = 8.7642270; separation ≥ 0.000272) | §2.1 |
| E_\*(1391) > E_\*(FR30) | ⟨D1391⟩ | §2 |
| the proper-rule maximiser is one of 1387, 1389, 1391 | **certified** (1095 classes proven inferior) | §2.1 |
| **the maximiser over all 6⁸ frame rules lies in the right-S₃ orbit of 1387** | **certified** (exhaustive funnel X3–X7) | §2.2 |
| 1387 (or its twin) is the maximiser | **open**: all six orbit intervals overlap; the co-leaders 1387 and 539311 share L = 8.7999990, with U = 9.3679502 and 9.3885937; no IMS certificate at R ≤ 22 separates them (probes) | §2.4 |
| sampled probes: no IMS certificate at R ≤ 22 separates 1387 from 539311 (in either direction), or 1387 from 1389 and 539291 | **evidence [E]** (float Rayleigh quotients on legal balls; a model extrapolation puts the co-leader separation at R ≈ 63 [X]) | §2.4 |
| Phase X's stored-only Y₆ bounds of the orbit and Phase VIII's U₅(FR30) | **reproduced independently** (to ≤ 10⁻⁹ and 5·10⁻⁹); Y₆(539288) = 9.0982534 is new | §2.1–2.2 |
| E_\*(539315) = E_\*(FR30) (FR30's mirror via 1386) | **proved + certified** (Theorem 6.2 of Phase VII + equal type sets) | §2.3 |
| "the mirror twin of a class" | **ill-defined** (member-dependent; corrected) | §2.3 |
| twin criterion: sign ΔU₁ predicts sign ΔY₅ | **correlation**: 31/40 | §2.3 |
| P1–P3 (U₁ orders single-child neighbourhoods) | **passed** (preregistered) | §5 |
| the 1387 mechanism: uniform raise on every geometric 1-star configuration; no two-cycle-flat tiles | **certified at radius 1** (exact local spectra); the association with high floors is **evidence** (post hoc, p = 4·10⁻¹¹) | §5 |
| 1387 is a local maximum of Y₅ under single-child changes | **certified at level 5** (finite level) | §5 |
| Π (certified local frustration profile) passes the ℤ³ and 937/938 tests | **certified** (ℤ³: separation 0.61 at R = 5) | §7 |
| ℤ³ trace-pair shadow bound (Phase X) | **reclassified [E]** | §1 |
| Chair44 edge exponent > 2 | **conjecture [X]** (three-point fits) | §12 |
| a physical law, quantum dynamics or particle spectrum follows | **not claimed** | §8 |

## 11. Corrected abstract

> **Spectral floors of geometric gauge connections: support, rates, obstructions, and a certified frontier for the 3D chair.**
>
> **General theory.**
> - For a covariant Laplacian H_U = D_U†D_U on any bounded-degree graph, with a unitary connection of any rank, the floor E_\* = inf σ(H_U) is the limit of the Dirichlet ground energies of the local environments that occur.
> - E_\* depends only on *which* environments occur, never on their frequencies, and adding environments can only lower it.
> - A partition-of-unity (IMS) identity gives two-sided certificates. Their error is O(R⁻²) with explicit constants on doubling graphs and on graphs with a Euclidean realisation, and R⁻² is optimal.
> - Uniform localisation is equivalent to property A. On lamplighter graphs the rate is no better than R^{−2/k}.
> - Free-boundary localisation converges to the wrong limit. Incomplete enumeration of environments can produce false certificates.
> - If every legal ball of radius r carries a loop whose holonomy has eigenvalue angles ≥ θ₀, then E_\* ≥ 2 sin²(θ₀/2)/((2r + 1)N_r). Conversely flat balls force small floors.
> - No frequency-type statistic bounds E_\*, and no fixed-radius datum determines it.
> - For finite structure groups, the failure of plaquette data is confined to the non-Abelian irreducible representation.
> - These are mostly established tools assembled for connection Laplacians. The discrete flatness-radius dichotomy and the explicit counterexamples were not found in the literature.
>
> **Chair44.**
> - For the 6⁸ frame rules of the three-dimensional chair substitution (Pauli-frame Q₈ connections), all Phase X localisation certificates were re-verified by an independent implementation. Class 1387 has E_\* ≥ 8.7999990.
> - An exhaustive certified funnel proves that every rule outside one six-element orbit has a smaller floor. The orbit is that of 1387 under right multiplication of the child frames by the chair's point group.
> - The extremiser is therefore one of six explicit rules. Which one remains open; sampled probes indicate that no localisation certificate up to radius 22 can decide between the two leading ones.
> - The leading rule differs from the matching-rule decoration FR30 by one child frame. That change raises the worst local energy on every geometric configuration.
>
> **Second geometry.** On substitution ladders every general statement is confirmed with certified enclosures of width 10⁻⁵.
>
> **Scope.** No physical interpretation is claimed.

## 12. The next experiment most likely to produce a new mathematical result

**Where the problem now stands.**
- Over all 1 679 616 frame rules, the extremal problem is reduced, with certificates, to one six-rule orbit O(1387) of the right action of the chair's point group (§2.2–2.3).
- Its members carry exact level-6 upper bounds, all recomputed independently in Phase XI (`phase11_orbit_Y6.jsonl`): 539311: 9.3886; 1387: 9.3680; 539291: 9.2499; 1389: 9.2105; 1391: 9.1104; 539288: 9.0983 (new; Phase X stopped at Y₅ = 9.1124 for it).
- Two members carry the certified lower bound 8.7999990.

**Experiment 1 (decisive, computational): certify the tail of the orbit.**
- **The only separation within reach** is 1387 > {1391, 539288}: the preregistered R = 20 certificate at μ = 9.1105, about ⟨T20⟩ on 4 cores. The probe margin is only 0.015.
- Separating 1387 from 1389 needs R ≈ 25 under the [X] model of §2.4 (≈ ⟨T25⟩). Separating it from 539311 needs R ≈ 63, beyond this method.
- **Outcome:** at best a four-member frontier {1387, 539311, 1389, 539291}. The rest needs Experiment 2.

**Experiment 2 (the one most likely to produce new mathematics): the edge exponent.**
- The IMS certificate converges like R⁻². That is optimal for statements uniform over all connections (Theorem C(iv)), and it is what the substitution ladders show on *both* sides.
- On Chair44 the upper sides converge faster at the radii reached:
  - FR30's supertile sequence decreases by a factor ≈ 0.19 per doubling, an exponent ≈ 2.4;
  - its ball minima give D₆, D₈, D₁₂ = 9.4166, 9.0515, 8.8570, an exponent ≈ 2.9 by a three-point fit [E].
- If the edge exponent α of D_R − E_\* ~ R^{−α} is genuinely larger than 2, the low-energy states are hierarchically localised near the spectral edge. A partition of unity aligned with supertile boundaries, where those states are small, could then beat the generic R⁻² loss on this specific family.
- **The precise question:**
  - Does some partition-of-unity (or Schur-complement) lower bound for a Chair44 hull converge at rate o(R⁻²)?
  - Or is R⁻² a lower bound for every localisation certificate of this operator?
- Either answer would be new. Only the first can separate 1387 from its mirror twin: their gap is 0.021 at level 6, and IMS would need ρ ≈ 60 for it.
- The concrete first step:
  - measure α for the orbit members from D_R at R ≤ 15 with the banded solver;
  - compute Y_L, L ≤ 7, for the orbit;
  - test whether supertile-aligned cutoffs reduce the measured localisation gap D_R − Λ_R below the R⁻² IMS bound at equal R.

---

## Reproduction

All commands run from the repository root (Python 3.13, numpy 2.5, scipy 1.18, sympy 1.14, mpmath 1.3), with `OMP_NUM_THREADS=1` unless stated. Wall times are on 4 CPU cores with no GPU, often under load.

| step | command | output | time |
|---|---|---|---|
| exact checks (overlaps, r_c, panels, Q₈, IMS identity, transport bound) | `python -u -I audit/phase11_proofs.py` | `phase11_proofs.json` | 1 min |
| independent re-certification | `python -u -I audit/phase11_chair.py cert <rule> <R> <m> <nproc> <mu> <tag>` (m ≥ 5 streams): `4752 12 4 4 7.9542922 audit_FR30_R12`; `x539288 8 3 1 6.85 audit_539288_R8`; `1387 14 4 4 2297561/262144 audit_1387_R14`; `1387 15 4 4 2306867/262144 audit_1387_R15`; `x539311 14 4 4 2297561/262144 audit_twin_R14`; `x539311 15 4 4 2306867/262144 target_twin_R15`; `1389 16 4 4 8.7645 target_1389_R16`; `1391 18 5 4 8.7645 target_1391_R18` | `phase11_cert.jsonl` | 2 min (R = 12) to 20 min (R = 15, 16); R = 18 at m = 5 ⟨T1391_TIME⟩ |
| ℤ³ audit and profile | `python -u -I audit/phase11_z3.py audit profile cover islands` | `phase11_z3.json` | 15 min |
| ladder (second geometry) | `python -u -I audit/phase11_ladder.py finite_radius insufficiency nonminimal rare rep_group support` | `phase11_ladder.json` | 1 h |
| radius-1 local data | `python -u -I audit/phase11_local.py twins|counterfactual|census 4` | `phase11_local_*.jsonl` | 10–60 min each |
| mechanism | `python -u -I audit/phase11_mechanism.py balls <rule> 8 2`; `... compare 4752 4753` | `phase11_mechanism.json` | 3–15 min per rule |
| extended-space funnel | `python -u -I audit/phase11_frontier.py reps`; `X3 4`; `X4 4`; `X5 4`; then `audit/phase11_d8stage.py x515983 x515963` and `audit/phase11_y6.py 515963` | `phase11_frontier_*.json(l)`, `_summary.json` (X3 committed gzipped) | 3 min, 30 min, 34 min, 2 min, 15 min, 2 min |
| preregistered lists | `python -u -I audit/phase11_frontier.py list twins 5 4`; `list counterfactual 5 4` | `phase11_frontier_{twins,counterfactual}_Y5.jsonl` | 15 min each |
| census brackets | `python -u -I audit/phase11_frontier.py census 4` | `phase11_frontier_census.json` | 8 min |
| FR30 inflated-star bound | `python -u -I audit/phase11_fr30_upper.py 5` | `phase11_fr30_upper.json` | 36 min (U₅ is a 884 736-tile eigsh on one core) |
| probes (upper bounds on Λ_R) | `python -u -I audit/phase11_chair.py probe <rule> <R,...> <out> <nproc>`: `4753 16,18,20,22 phase11_probe_1387.json 4`; `1391 18 phase11_probe_1391.json 2`; `x539311 20,22 phase11_probe_539311.json 1` | `phase11_probe_*.json` | 11 min (1387, 4 radii, 4 processes); 2 min (1391, 2 processes); 6 min (539311, 1 process) |
| certificate cost model | `python -u -I audit/phase11_costs.py "<load note>"` | `phase11_costs.json` | 1 min |
| orbit level-6 bounds | `python -u -I audit/phase11_y6.py --out=phase11_orbit_Y6.jsonl 184342 539288 184338 539291 184323 539311` | `phase11_orbit_Y6.jsonl` | 4–8 min per member |
| analysis, leaderboard, ledger | `python -u -I audit/phase11_analysis.py`; `audit/phase11_leaderboard.py`; `audit/phase11_ledger.py` | `phase11_analysis.json`, `phase11_leaderboard.*`, `phase11_ledger.json` | 1 min |
| tests | `python -m pytest -q tests/test_phase11.py` | — | ⟨TEST_TIME⟩ |
