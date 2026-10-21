# Phase V-A — The Critical Path: Dossier

**Scope.** Four parts of the Phase V-A brief (computational evidence reconstructed independently; the band edge near 8.76 defined and attacked as an infinite-volume object; the type recursion as a kernel-checked Lean theorem; physical realization with falsification criteria) plus the mandatory targets H1–H6, and the question added last: *is there a reproducible relationship between the spectral edge and the spatial organization of the decoration that survives controls with matched flux fractions?*

**Status vocabulary** (used for every claim): **[P]** proved in this repository with an explicit argument; **[K]** kernel-checked in Lean 4.34.1 without Mathlib; **[E]** reproduced computationally with reported residuals, by code written for this phase; **[C]** computationally supported conjecture; **[U]** unresolved; **[Cite]** depends on a cited theorem whose statement was checked only against metadata (no full text available in this environment).

Branch: `claude/phase5a-critical-path` (created from `claude/magical-euler-0vm2f8` at e2677db). Interim commits 1dd61cc, b337be7 (snapshots of agent outputs while runs were still in progress; two text outputs in those snapshots were partial and are superseded by the working-tree files committed below). Final commit(s): [[COMMITS]].

---

## 1. Provenance of the object

**Definitions (shared with production code because they define the object).** Chair prototile $C_3=[0,2]^3\setminus(1,2]^3$ (7 unit cubes $U_3=\{0,1\}^3\setminus\{(1,1,1)\}$), inflation 2, 8 children: the centre child $(P(\pi_0),(1,1,1))$ and seven octant children $(D_s(v)P(\pi_v),4v)$ in doubled coordinates, frames given by the FR30 permutation table; frames lie in $SO(3,\mathbb Z)$ and all 24 occur (7 at level 1, 24 at level 2). Links on the shared unit panel $f$ with normal $n$ between tiles $a,b$ with frames $M_a,M_b$: $C_{ab}=(\sigma\cdot M_a^T n)(\sigma\cdot M_b^T n)\in Q_8$, $C_{ba}=C_{ab}^\dagger$. Quaternion dictionary $e_m=-i\sigma_m$, so $C_{ab}=-(u_au_b)$.

**Source of the data under test.** The `measured` dictionary in `audit/phase4_type_substitution_proof.py` (class-resolved inter-tile plaquette counts at levels 1–5), the recursion data exported to `certificates/TypeSubstitutionCertificate.lean`, the Phase V pinned-patch bottoms 10.77695, 9.37847, 8.91963, 8.79701, 8.77013 (levels 2–6), and the Phase V participation ratios.

**Convention audit (A4) [E].** From the relations $i^2=j^2=k^2=ijk=-1$ alone the Q8 table is unique among $8^6$ candidates; the dictionary $e_m=-i\sigma_m$ is a homomorphism (64 products checked); the integer Q8 routine in the repository and the Lean `qmul`/`cliffordLink` agree on every product. One genuine convention defect was found: the numpy labeller `q8label` in `audit/independent_clifford_q8_audit.py` names the matrix $+i\sigma_m$ "$+m$", which is the quaternion $-m$; all signed histograms of traceless classes in `audit/results/phase3_*.txt` are therefore sign-flipped relative to the quaternion convention. No conjugacy-class count or frequency is affected (classes agree 36/36). A documentation error was found in Phase 2 §2.1: the panel count is $12(8^k-4^k)=48,576,5376,\dots$, not $48\cdot12^{k-1}$.

**Gauge content [E].** The five class frequencies $19/36,13/144,1/9,23/144,1/9$ are invariant under Q8-valued gauge transformations and under the local-frame convention, but the split of the traceless part into $i/j/k$ is *not* SU(2)-gauge-invariant (in the ambient spin-lift gauge the axis label of 17/60 level-1 and 253/792 level-2 plaquettes depends on the base tile). The SU(2)-invariant content is $(19/36,\;13/144,\;55/144)$ for classes $\{+1\},\{-1\},\{\text{traceless}\}$. Documents calling the $i/j/k$ split "gauge-invariant" should say "invariant under Q8 gauge transformations".

---

## 2. Independent verification (Part I)

### 2.1 Enumerator written without production imports (A1) [E]

`audit/phase5a_independent_enumerator.py` imports only the standard library and numpy. It represents frames as signed permutations (not matrices), Q8 as abstract (sign, basis) pairs with a table derived from the relations, generates tiles breadth-first with explicit ancestor tracking, parametrises plaquettes by lattice edge rather than by cube, and evaluates holonomies with two mutually checked evaluators (scalar and vectorised). Pauli-matrix cross-checks are run on every link at levels 1–2.

| level $m$ | $N_m$ | $\{+1\}$ | $\{-1\}$ | $\{\pm i\}$ | $\{\pm j\}$ | $\{\pm k\}$ |
|---|---|---|---|---|---|---|
| 1 | 60 | 26 | 3 | 12 | 7 | 12 |
| 2 | 792 | 385 | 42 | 124 | 117 | 124 |
| 3 | 7728 | 3945 | 530 | 1020 | 1213 | 1020 |
| 4 | 67680 | 35161 | 5394 | 8188 | 10749 | 8188 |
| 5 | 565440 | 296121 | 48146 | 65532 | 90109 | 65532 |

Every entry equals the recursion output recorded in `audit/results/phase4_type_substitution_proof.txt`, and $N_m=18\cdot8^m-24\cdot4^m+6\cdot2^m$ holds exactly. Straddling counts $B_m=24\cdot4^m-18\cdot2^m$ and their class resolution match the Phase 3 files at levels 3–5. A deliberate perturbation of two FR30 permutations keeps the geometry and $N_m$ but changes the class vector, so the enumerator is decoration-sensitive. Run time 0.96 s, 81 MB. Ten unit tests (`tests/test_phase5a_independent_enumerator.py`).

**Adversarial verification of A1.** Three independent referees re-derived the level-1 and level-2 geometry and links (one by a from-scratch matrix implementation, `audit/phase5a_referee_geometry.py`, `audit/phase5a_referee_links_check.py`; results in `audit/results/phase5a_referee_*.txt`). [[VERIFY_A1]]

### 2.2 Type-system audit (A2) [E]

`audit/phase5a_type_system_audit.py` (23 tests). All 49 panel and 108 plaquette representatives are valid, recompute to their keys and classes, are reconstructible from the key alone, and match the Lean certificate data byte for byte. Every inter-tile panel/plaquette of $T_1..T_5$ (up to 380 928 panels, 565 440 plaquettes) has a representative key; the class and the canonical link label are functions of the type on every instance; inflation images were verified on all 576 + 792 level-2 instances. 11 618 rigid-motion checks passed; the intrinsic key is in fact invariant under the full hyperoctahedral group $O(3,\mathbb Z)$ (harmless, since $\det=-1$ frames never occur). Eight loop orderings never change the class; reversal is inversion, base change is conjugation. Random Q8 and SU(2) gauges change most links but no class.

Two findings correct the brief rather than the code: reversing one tile's face normals is the central gauge transformation $-I$ and changes **zero** classes (the brief predicted a change); a plaquette key consisting only of relative frames does not determine the class (18 of 78 coarse keys at level 2 carry two classes), so the local cube positions in the key are essential.

### 2.3 Recursion as a theorem with explicit conventions (A3) [P + E]

`audit/phase5a_recursion_theorem_audit.py` and `deliverables/PHASE5A_RECURSION_THEOREM.md` (six numbered statements with hypotheses and proofs; 15 tests). Conventions fixed: vectors are columns, $S[r,c]$ counts outputs of type $r$ per input of type $c$, so the column sums are 4 (panels, $M$), 4 (panel→plaquette, $A$), 2 (plaquettes, $B$); row sums are not constant. The affine recursion $v_{m+1}=8^m f+Sv_m$ was proved coordinate-wise by parity category and checked exhaustively for $m=1,2,3$ (every inflated tile contributes exactly the forcing pair). Characteristic polynomials $\lambda^{44}(\lambda-4)(\lambda-1)^4$ and $\lambda^{103}(\lambda-2)(\lambda-1)^4$; nonzero part semisimple; nilpotency index 2 (ranks of $S,S^2,S^3$ are 27, 10, 10).

Correction to Phase V wording: FR30 has **no** self-reproducing panel type with $M[c,c]=4$. The stable interface object is a 7-type sink block $\{0,2,5,9,14,25,42\}$ of rank 2 with characteristic polynomial $\lambda^5(\lambda-4)(\lambda-1)$. The closed form $64v_m=8^mW_8+4^mW_4+2^mW_2+W_1$ holds for all $m\ge2$ (checked to $m=9$; the Lean base case at $m=3$ is therefore stronger than needed), and fails at $m=1$.

**Counterexamples bounding the general theorem [P + E]** (`audit/phase5a_counterexamples.py`): Fibonacci (irrational frequencies $1/\varphi,1/\varphi^2$); the non-primitive rule $a\to aa,\ b\to bb$ (seed-dependent limit); Thue–Morse 2-blocks (spectrum $\{2,1,-1,0\}$, the $-1$ is the non-clean eigenvalue); period doubling ($\{2,-1\}$). Rationality of limits needs primitivity plus a rational Perron data set; cleanness is not automatic.

### 2.4 Clean-spectrum criterion (H6) [P + E]

Condensation criterion: the substitution matrix is clean (spectrum $\subset\{K,1,0\}$ with $K$ the inflation count) iff every non-sink strongly connected component is a singleton with loop weight 0 or 1 and every sink component has non-Perron spectrum in $\{0,1\}$; then $\mathrm{mult}(K)=\#\text{sinks}$. Verified clause by clause on $M$ and $B$ for FR30 (clean), the achiral decoration (clean, three rank-1 sinks), and random decorations #0 and #1 (not clean: 3-cycles, an 11-type irreducible block, sink blocks with eigenvalues $2,-1,(-1\pm\sqrt{17})/2$).

**Outcome H6: proved theorem.**

---

## 3. Theorem audit: the infinite-volume framework (H1) [P unless marked]

Deliverable: `deliverables/PHASE5A_INFINITE_VOLUME_FRAMEWORK.md` (Task B3). Statements proved there, each with hypotheses:

1. **Hull.** $\Omega$ (tilings all of whose patches are legal) is a non-empty compact $\mathbb Z^3$-subshift of finite local complexity over 168 letters; a fixed point exists with $\sigma^2(\omega^*)=\omega^*+(2,2,2)$. Correction: the pose $(I,-(1,1,1))$ is not a valid seed (its inflations exhaust only an octant); the correct seed is the central word at $-(2/3)(1,1,1)$.
2. **Frame substitution.** $24\times24$ matrix with row and column sums 8, spectrum $\{8,2^{(20)},0^{(3)}\}$, uniform frame frequencies $1/24$, primitivity exponent 2.
3. **Notch rule and recognizability.** A chair is central in its supertile iff at least two (equivalently all seven) of its cubes are notches of other chairs. Unique composition follows; hence **aperiodicity** of every hull element. This closes the "external, unverified" aperiodicity item of the Phase V ledger.
4. **Repetitivity and minimality.** Every legal patch in $T_m$ occurs in every level-$(m+2)$ supertile of every $\omega$.
5. **Unique ergodicity [Cite]** (Solomyak 1997; Lee–Moody–Solomyak 2002).
6. **Operator.** $H_\omega=24-A_\omega$ on $\ell^2(\text{tiles})\otimes\mathbb C^2$: bounded, self-adjoint, $0\le H\le48$, $\langle\psi,H\psi\rangle=\sum_f|\psi_a-C_f\psi_b|^2$; gauge, translation and $SO(3,\mathbb Z)$ covariance (no spin rotation); quaternionic symmetry $J^2=-1$, Kramers doublets.
7. **Constancy of the spectrum** on the hull (direct Weyl-sequence proof using minimality); $E_{\rm bulk}=\inf\sigma(H_\omega)$ is well defined.
8. **Compression theorem.** $H^{\rm pin}_m=24-A$ on $T_m$ is exactly the compression of $H_\omega$; $\lambda_{\min}(H^{\rm pin}_m)$ is non-increasing and converges to $E_{\rm bulk}$.
9. **Certified bounds [P + E].** Exact rational Rayleigh quotients: $E_{\rm bulk}\le10.776950512,\ 9.378470210,\ 8.919634360,\ 8.797011333$ (levels 2–5). The level-6 value 8.77013 is a floating-point Rayleigh–Ritz value, not a certificate.
10. **Positive lower bound [P + E].** $E_{\rm bulk}\ge3137451/2000000=1.5687255$, via the plaquette decomposition $H=\tfrac14\sum_e h_e$, the closure of the 72 legal vertex-star types under the collared substitution (two seeds give the same 72; complete stars of $T_5$ are exactly these 72), and exact rational $LDL^*$ pivots for all 207 plaquette signatures. [[C2]]
11. **The gap is a flux effect [P].** For the trivial connection on the same hull $\inf\sigma=0$.
12. **IDS [P].** $\|N^{\rm pin}_m-N^{\rm free}_m\|_\infty\le24\cdot2^{-m}$; both converge uniformly to one $N_\infty$ (identification with the hull IDS is [Cite]).
13. **Effective mass [P, conditional].** Any hull-covariant effective-mass tensor is isotropic (Schur, $SO(3,\mathbb Z)$ with trivial spin action).

**Outcome H1: proved theorem** (items 1–4, 6–13), with unique ergodicity cited.

---

## 4. Spectral result (Part II, H2–H5)

### 4.1 What the two bottoms are (H2) [P + E]

The free-boundary bottom $5.25$ is the energy of a state localized on the patch boundary (boundary weight 0.93 at levels 3–5 while the boundary fraction falls 0.56→0.17; participation 87–104 tiles independent of $n$). It is a surface artefact of the reduced diagonal. The pinned bottom is the compression of the bulk operator; its limit **is** the infinite-volume edge $E_{\rm bulk}$. Reproduced at levels 2–6 by an independent Chebyshev-filtered subspace solver and by matrix-free LOBPCG: 10.776951, 9.378470, 8.919634, 8.797011, 8.770134 (residuals $10^{-14}$ to $7\cdot10^{-8}$; level 6 Kramers doublet, next doublet 8.770242). Decrements 1.399, 0.459, 0.123, 0.027 with ratios 0.33, 0.27, 0.22.

Rigorous bracket: $1.5687\le E_{\rm bulk}\le8.7970$ (certified), $\le8.77013$ (IEEE). $E_{\rm bulk}\approx8.76$ is **[C]** (geometric decay of decrements unproved).

**Outcome H2: proved theorem for the bracket and the identification; conjecture for the value 8.76.**

### 4.2 Extended or localized (H3) [E → C]

Pinned ground-state tile participation $\mathrm{IPR}\cdot n=2.39,\,6.42,\,9.15,\,19.93,\,42.79$ at levels 2–6 (level 6 recomputed, not quoted). Two-point exponents $\alpha$ in $\mathrm{IPR}\sim n^{-\alpha}$: 0.52, 0.83, 0.63, 0.63. For the lowest eight states: 0.56, 0.77, 0.56, 0.55. The extended control (trivial links, same graph) gives $\mathrm{IPR}\cdot n=2.26,2.89,3.26,3.47$, $\alpha\to1$. Boundary weight of the pinned states is $\le0.001$ at level 5 and 0.0000 at level 6.

Spatial organization: depth-1 interface weight 0.78, 0.66, 0.58, 0.57 (levels 3–6) against interface tile fractions 0.53, 0.31, 0.17, 0.09 (enrichment 1.5→6.3); participation is 0.26–0.35 of the interface-network size $T_L=8,53,269,1277,5597,23453$ (growth →4, i.e. two-dimensional surfaces, predicted asymptotic $\alpha=2/3$). Generalized dimension $D_2=2.49,1.88,1.90$ from consecutive level pairs; box-counting local dimensions 1.7–2.5 at fine scales (uniform state: 3; trivial control: 2.0→3.0). The lowest ≈75 states per patch form an interface band of width 0.44 (level 4) → 0.11 (level 5).

Controls at levels 3–5 (`audit/results/phase5a_scaling_controls.txt`; criterion $|\alpha_{4\to5}-0.625|\le0.10$ shares, $\ge0.25$ does not): unit cube with the FR30-type decoration 0.75 (ambiguous); random admissible substitution decorations seeds 1, 2 → 0.09, 0.11 (localizing; do not share), seed 3 → 0.65 (shares); sign-stripped links 0.89, i.i.d. random Q8 links $-0.25$, trivial links 0.94 (do not share). [[C3L6]]

**Outcome H3: computationally supported conjecture** — the edge states are neither extended nor localized at accessible sizes; they live on the hierarchical interface network with $D_2\approx1.9$. The exponent is not stable over the window (0.52–0.83), so no clean power law is claimed. [[SKEPTIC_B1]]

### 4.3 Homogenization (H4) [U with obstruction stated]

No Floquet decomposition exists on $\Omega$; periodic approximants necessarily carry illegal seams (aperiodicity, item 3 above). The exact obligations are stated in the framework document §5.3 (strong resolvent convergence of approximants, uniform non-degeneracy of the edge, convergence of the Hessians). IDS counting exponents near the edge (B4, `audit/results/phase5a_ids_edge.txt`): calibration controls show that a true parabolic edge appears at these sizes with local exponents 1.65–1.93 because of the Dirichlet surface term, so $3/2$ is not the right finite-size benchmark; FR30 at level 4 gives 1.32–1.39 in the two upper windows (bootstrap median 1.34 [1.31, 1.37]), far below the matched trivial control (1.88–1.93), inconsistent with a Dirichlet-sampled parabolic edge at this size; level-5 FR30 did not finish. **Outcome H4: unresolved, leaning anomalous; obstruction identified.**

### 4.4 Effective mass (H5) [P conditional + E]

If an effective mass exists it is a scalar (item 13). For periodic Q8 decorations with $2L\subset L'$ the Richardson finite-difference and degenerate-perturbation-theory Hessians agree to $2\cdot10^{-6}$ and are scalar to $4\cdot10^{-14}$ (e.g. the natural FR30 bijection on $2\Lambda_7$: $E_{\rm per}=10.644234$, Hessian eigenvalues 11.45, 26.62, 26.94); at band touchings no effective-mass description exists. For the aperiodic operator no construction is available. **Outcome H5: unresolved for the hull; the only unconditional statement is the isotropy theorem.**

### 4.5 The relationship asked for: spectral edge versus spatial organization at matched flux

**Periodic census (B2a) [E].** The $\Lambda_7$ chair crystal ($\phi(x,y,z)=x+2y+4z \bmod 7$ is a bijection on $U_3$, so chairs at $\ker\phi$ tile $\mathbb Z^3$; 24 panels per chair, 14 neighbours; 18 inter-tile plaquettes per chair, so FR30's limit 18 is geometric) was decorated with frame fields constant on cosets of sublattices of index 1, 2, 4, 8 and solved by exact Bloch theory with BFGS refinement (validated to $10^{-14}$ on 210 decorations; torus supercells reproduce Bloch spectra to $10^{-13}$).

| population | count | $E_{\rm per}$ range | median |
|---|---|---|---|
| all periodic decorations | 44 539 | 0 – 16.000 | — |
| $|f_{\rm nontriv}-17/36|<0.03$ | 4 411 | 3.65 – 15.25 | 5.87 |
| all three class fractions matched (±0.03, ±0.04, ±0.04) | 1 551 | 4.50 – **8.18** | 5.61 |
| FR30 frames on $\Lambda_7/2\Lambda_7$, all 40 320 bijections | 40 320 | 9.61 – 14.18 | 11.24 |
| FR30 (aperiodic), rigorous | — | $\le 8.7970$ (certified), $\le 8.77013$ | — |

Regression over the whole census: $E_{\rm per}\approx-1.904+14.303f_{\rm traceless}+30.696f_{-1}$ (rms 0.53, sd 2.75), predicting **6.33** at the FR30 fractions. 38.9 % of all periodic decorations exceed 8.770, so the value is reachable by periodic systems; but **no flux-matched periodic decoration reaches it** (maximum 8.18, 0.59 below the IEEE bound and 0.62 below the certified bound), and FR30 sits 4.5 rms above the flux regression. FR30 periodic approximants (level-$k$ supertile on $2^k\Lambda_7$) have band bottoms 8.33, 7.51, 8.25, 8.36 for $k=1..4$, but these are interface-defect states (level 4: lowest twelve states carry 80 % weight on the 32.5 % interface tiles, band width 0.006); the first extended approximant states start at 8.88 (level 4) and 9.40 (level 3), consistent with the pinned bracket. [[D2]]

**Aperiodic controls at matched flux (D1).** [[D1]]

**Statement of the relationship.** [[RELATIONSHIP]]

---

## 5. Lean status (Part III)

Toolchain: Lean 4.34.1 (commit 5045d005), x86_64 Linux, no Mathlib, binary at `/tmp/claude-0/-home-user--/3e28775d-be57-5932-b9d4-6e0f425b644f/scratchpad/leandl/lean-4.34.1-linux/bin/lean`. Command for the certificate: `lean certificates/TypeSubstitutionCertificate.lean`. The file contains no `sorry`, no `native_decide`, no `axiom`; 14 `decide +kernel` data checks.

Changes this phase (A5): a data-independent theorem `closed_form_general` (hypotheses: linear step on an arbitrary finite type system, eigen-identities, base case at $j=2$ — the redundant $u_0=f$ hypothesis is kept for the requested signature) proved by induction; `closed_form_all` is now its instantiation and the original direct induction is kept as `closed_form_all_direct`; a Q8 section with `q8_closed`, `q8_conj_is_inverse`, `q8_class_conj_invariant`, `q8_class_inverse_invariant`, all by `decide` with **no axioms**. No theorem was removed or changed in statement; the certificate data block is byte-identical to HEAD.

Compile records: a scratch copy with `decide +kernel` replaced by `native_decide` compiles with zero errors and warnings in 24.9 s (`audit/results/phase5a_lean_general_theorem_compile.txt`); a data-free extract compiles with the kernel in 2.6 s, `closed_form_general` depending on `[propext, Quot.sound]`.

**Full kernel compile of the real regenerated certificate:** [[LEAN]]

---

## 6. Physical prediction and falsification criterion (Part IV)

What is physical here is a tight-binding spin-½ hopping problem on the chair tiling with Q8 (π-flux-type) link phases, realizable in principle in photonic or microwave lattices, cold-atom optical tilings, or circuit-QED arrays where SU(2) link operators are engineered; no gravity prediction follows from any result in this dossier, and none is manufactured (the only gravity-adjacent statement is the isotropy of any covariant effective-mass tensor, item 13 of §3, which is a symmetry statement about the lattice, not a continuum derivation).

**Prediction P1 (edge position).** The bulk spectral edge of the pinned FR30 Clifford operator lies in $[1.569, 8.797]$ with the sequence of pinned-patch bottoms converging to it from above; numerically $8.76\pm0.01$. **Falsified** if a measurement or an exact computation of the hull spectrum finds spectral weight below 8.70 away from boundaries, or if the pinned-patch sequence turns out not to be non-increasing (that would contradict a proved theorem and indicate an implementation error).

**Prediction P2 (relative position at matched flux).** [[P2]]

**Prediction P3 (edge-state organization).** The lowest states of any sufficiently large legal patch concentrate on the hierarchical interface network with participation about 0.3 of the network size and $D_2\approx1.9$. **Falsified** by an extended ($\mathrm{IPR}\cdot n\to$ const) or exponentially localized ($\mathrm{IPR}\to$ const) ground state at level 7 or beyond.

---

## 7. Literature assessment

No network access to full texts was available; the Consensus search tool and metadata confirm existence of the cited works but not their exact statements. Cited: Solomyak 1997 (unique ergodicity of primitive substitution tilings), Lee–Moody–Solomyak 2002, Lenz–Stollmann 2005 and Lenz–Veselić 2009 (IDS and gap labelling for strictly ergodic Delone systems), Bellissard–Benedetti–Gambaudo 2006, Kaminker–Putnam 2003. Known theory covers almost-periodic/periodic homogenization (Kozlov; Jikov–Kozlov–Oleinik; Birman–Suslina; Allaire–Piatnitski), none of which covers a discrete aperiodic internal-type edge with Kramers degeneracy; this is the stated obstruction for H4.

Novelty, as far as can be assessed without full-text access: (i) a kernel-checked exact finite-state renormalization of holonomy classes for a 3D substitution tiling with a non-abelian (Q8) connection; (ii) a certified two-sided bracket for the bulk edge via vertex-star closure; (iii) the flux-matched periodic census showing the edge is a property of the frame *arrangement*, not of the flux density. Items (i)–(ii) are **[P/K]**; item (iii) is **[E]**.

---

## 8. Publication decision

**Decision:** publish the mathematics (Parts I–III) now; hold the spectral-edge/organization relationship as a computationally supported conjecture with the controls stated, not as a theorem; make no physical-realization claims beyond a tight-binding model.

**Title.** *Exact finite-state renormalization of a Q8 connection on the three-dimensional chair tiling, with a certified bracket for its bulk spectral edge*

**Abstract.** We decorate the FR30 chair substitution tiling of $\mathbb R^3$ with an $SO(3,\mathbb Z)$ frame field and a Q8-valued connection on shared panels. We prove that holonomy conjugacy classes of inter-tile plaquettes satisfy an exact affine recursion on 49 panel types and 108 plaquette types whose matrix has spectrum $\{8,4,2,1,0\}$ and is semisimple on its nonzero part, giving closed forms for all class counts and rational limit frequencies $19/36,13/144,1/9,23/144,1/9$; the recursion and a general closed-form theorem are kernel-checked in Lean 4 without external libraries. We establish aperiodicity, minimality and finite local complexity of the decorated hull, define the bulk operator $H=24-A$ on $\ell^2\otimes\mathbb C^2$, prove constancy of its spectrum and that pinned-patch compressions converge to the bulk edge, and certify $1.5687\le E_{\rm bulk}\le8.7970$ by exact rational arithmetic. A census of 44 539 periodic Q8 decorations of the chair crystal shows that the band bottom is not determined by flux-class fractions and that the FR30 edge exceeds every flux-matched periodic decoration; the edge states of finite patches concentrate on the hierarchical interface network with correlation dimension near 1.9. [[ABSTRACT_D1]]

---

## 9. Next three actions

1. [[NEXT1]]
2. Level-7 pinned computation (dim $4.2\cdot10^6$, matrix-free Chebyshev filtering, estimated 4–6 h on this machine) to extend the exponent window for H3 and test the predicted asymptote $\alpha=2/3$.
3. Replace the floating-point level-6 bound by a certified rational Rayleigh quotient, and tighten the lower bound by passing from vertex stars (radius 1) to radius-2 collared patches (closure census first; the 72-type census took 2 s, a radius-2 census is estimated at minutes).

---

## Appendix A. Changed files, tests, failures

[[APPENDIX]]
