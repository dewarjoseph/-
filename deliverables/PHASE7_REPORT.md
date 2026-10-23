# Phase VII (with VII-B closure) — local determinacy, spectral localization, and the non-Abelian comparison for Chair44/FR30

**Repository state.**
- Branch `claude/phase7-local-determinacy`. HEAD before this work was aed7bd1, a merge of the Phase VI branch (c3edc9b, PR #7) into the frozen Phase VII protocol commit 1073b26, on top of main 9b72690.
- The committing hash is given in the ledger (`audit/results/phase7b_ledger.json`).
- Definitions are frozen in `deliverables/PHASE7_DEFINITIONS.md`, and every number below refers to them.

**Labels.**

| label | meaning |
|---|---|
| [P] | proof written here |
| [L] | checked by the Lean kernel |
| [C] | certified computation: exact integer/rational arithmetic, or floating point with a rigorous error bound |
| [E] | floating-point evidence |
| [X] | added after the frozen protocol. The protocol's decision rule was not changed. |

**Scope.** Nothing here derives quantum mechanics. The object is one bounded self-adjoint operator family, H = 24 − A_U on ℓ²(tiles) ⊗ ℂ², and its spectrum.

---

## 1. Executive result

**The strongest theorem actually established.** (Each part has a separate proof; see the indicated section.)

> **Theorem (Chair44 / FR30).**
> 1. **Forced curvature** [P, L, C] (§4). Every geometry-compatible frame field, proper or improper, has at least 12 of the 21 centre–octant two-cycles of each level-1 supertile non-trivial. So no compatible frame field is pure gauge. The bound 12 is attained.
> 2. **Uniform gap** [C] (§5). For every compatible frame field (proper or improper) on any union of level-1 supertiles, including every infinite chair tiling with a level-1 composition: D_U†D_U ⪰ 41789/25000 and 24 − A_U ⪰ 41789/25000.
> 3. **Local rules** [P + finite checks C] (§6). A chair tiling with proper frames all of whose 1-stars are legal FR30 1-stars lies in the FR30 hull: **𝒯₁ = Ω_FR30**. Consequences:
>    - every such tiling is non-periodic;
>    - the radius-1 legality predicate (72 star types) determines the substitution hierarchy;
>    - E_inf(R) = E_FR30 for every R ≥ 1.
> 4. **Controlled local computation of the floor** [P + C] (§7). For R ≥ 6 and ρ = R − 311/175,
>
>    Λ_R ≤ E_FR30 ≤ D_R,   E_FR30 − ε(ρ) ≤ Λ_R,   D_R ≤ E_FR30 + ε(ρ),   ε(ρ) ≤ (π²S₁/6ρ²)/(1 − π²(15/7)²/(6ρ²)),
>
>    with S₁ = 4734/49. Λ_R and D_R are minima over the finitely many legal radius-R balls. **Certified: E_FR30 ∈ [7.954292, 8.7649120247].**
> 5. **Matched non-Abelian separation** [C] (§8). On the same graph and operator:
>    - E_FR30 ≥ 7.954292 > 7.6345317659 ≥ E(χ_k∘U_FR30) for k = 1, 3;
>    - E_FR30 > 5.3285882042 ≥ E(χ₂∘U_FR30);
>    - E_FR30 > 3.3573965495 ≥ E_Z₂ ≥ 41789/25000.
>
>    The χ_k are the three Abelian (Z₂) shadows of the FR30 connection. They have the same geometry, the same hierarchy and essentially the same Wilson action density (0.5596 vs 0.5602 at level 4).

**What is not established.**
- **Proposition 6** (a hierarchy-specific spectral signature beyond local frustration) is not established (§9).
  - The floor is a function of the *set* of legal local patches (item 4).
  - By item 3 that set already forces the hierarchy.
  - So, for the floor, "hierarchy" and "local data" are not separable quantities.
  - The one scale observable that separates the matched systems — FR30's persistent sub-1/4 finite-size approach ratio — is absent from FR30's own hierarchy-preserving Abelian shadows. It is therefore a non-Abelian effect, not a hierarchy effect.
- **"Q₈ is essential" is not established.**
  - The arrangement of the flux matters more than the group: Z₂ reflection and χ₁ have nearly equal action density but level-6 floors 3.36 and 7.63.
  - i.i.d. random Z₂ links give larger finite-volume floors than FR30, but have infinite-volume floor 0 almost surely.

---

## 2. Run closure

Every job launched in Phase VII and VII-B is listed. Logs are in the session scratchpad (`p7/*.log`); outputs are in `audit/results/`.

| job | command | status / exit | output | last completed unit |
|---|---|---|---|---|
| radius-2,3,4 block bounds + approximant legality | `python -u -I audit/phase7_local.py types bounds approximants` | done, 0 | `phase7_local.json` | P₄ at R = 4 (2058/4096 illegal) |
| level-1 adversarial (proper + improper, Bareiss) | `python -u -I audit/phase7_adversarial.py` | done, 0 (1417 s) | `phase7_adversarial.json` | improper certificate, 1 672 288 classes |
| IMS bound R = 6, 8, 10 | `IMS_PROCS=12 python -u -I audit/phase7_ims.py 6 8 10` | done, 0 (1251 s) | `phase7_ims.json` | R = 10 |
| IMS bound R = 12 | `IMS_PROCS=12 IMS_PLAIN_MAX=12 python -u -I audit/phase7_ims.py 12` | done, 0 (3304 s) | `phase7_ims.json` (merged) | R = 12: 2315 balls, Λ₁₂ = 7.954292 |
| radius ≥ 14 | — | **never launched** | — | — |
| 264-rule B₂ sweep (8 lanes) | `python -u -I audit/phase7_decoration_bounds.py <k> 8` | done: 8 lanes exited, 264/264 | `phase7_decoration_bounds_shard*.jsonl` | all 264 classes (FR30 = class 4752: B₂ = 4.008196) |
| periodic exact cover | `python -u -I audit/phase7_periodic_search.py 4` | m = 1, 2 exhausted for both lattices; m = 3 stopped at the 3 000 000-node cap for both lattices (**not exhausted**); m = 4 not run | `phase7_periodic_search.json` | m = 3, both lattices: 3 000 000 nodes, no solution |
| local-rules checks (grouped, canonical) | `python -u -I audit/phase7b_local_rules.py` | done, 0 (21 s) | `phase7b_local_rules.json` | check B: 72 configurations |
| local-rules checks (per-star, cross-check, 2 h cap) | `python -u -I audit/phase7b_local_rules.py --per-star` | stopped by hand at 2 112 542 configurations (2987 s), no result file | `phase7b_local_rules_perstar.json` | none (records only at completion) |
| gauge-class audit | `python -u -I audit/phase7b_consistency.py` | done, 0 | `phase7b_consistency.json` | — |
| independent V_R census | `python -u -I audit/phase7b_census.py` | done, 0 (564 s) | `phase7b_census.json` | R = 4: 762 types, sets equal |
| independent IMS check | `python -u -I audit/phase7b_ims_check.py` | done, 0 (766 s) | `phase7b_ims_check.json` | R = 8 census, 747 balls |
| matched controls L3–5 | `python -u -I audit/phase7b_controls.py` | done, 0 (67 s) | `phase7b_controls.json` | L5 random Z₂ |
| level-6 controls + r_L | `python -u -I audit/phase7b_scaling.py` | done, 0 (1269 s; restarted once, see below) | `phase7b_scaling.json` | FR30 L6 = 8.770133629 (exact Rayleigh ≤ 8.7701336301; V-E: 8.770133629) |
| Abelian check L2–5 | `python -u -I audit/phase7_abelian_check.py` | done, 0 | `phase7_abelian_check.json` | — |
| two-cycle formula | `python -u -I audit/phase7_twocycle_formula.py` | done, 0 | `phase7_twocycle_formula.json` | 35 271 936 two-cycles |
| rule table | `python -u -I audit/phase7b_rule_table.py` | done, 0 | `phase7b_rule_table.json`, `deliverables/PHASE7_RULE_TABLE.md` | — |
| Lean | `lean certificates/Phase7Counting.lean` | done, 0 (43 s) | — | — |
| tests (Phase VII) | `python -m pytest -q tests/test_phase7.py tests/test_phase7b.py` | **26 passed** | — | — |
| tests (whole repository) | `python -m pytest -q tests/` (with a Windows stub for the POSIX `resource` module on PYTHONPATH) | 338 passed, 7 failed, 12 errors | — | the 7 failures and 12 errors are **pre-existing**: they reproduce identically on a clean checkout of main 9b72690, and this branch modifies no existing file. They are Lean-toolchain/certificate-template checks of Phases V-A/V-B and one 1.8·10⁻¹² tolerance in `test_adversarial_chair44` |

**Runs restarted, failed or superseded.** All of these are recorded, and none of their outputs is used.

| run | what happened |
|---|---|
| `phase7_adversarial.py`, first run | two-cycle pairing bug (ordered owner keys), giving 9 configurations instead of 21. Log kept as `p7/adv_buggy_twocycle.log`. |
| `phase7_ims.py`, first version | Gershgorin form with discrete normalisation. Superseded by the exact identity before any number was reported. |
| `phase7b_local_rules.py`, first version | aborted: (i) a parent-alignment bug (parents at half-integer translations), then (ii) the false premise that every sibling lies in a 1-star. The per-star run was also stopped at 117 400 configurations for speed; the grouped run is canonical. |
| `phase7b_ims_check.py`, first version | float centroids, giving 3701 "distinct" R = 8 balls through rounding at \|x_a − x_t\| = R exactly. Killed and redone with exact integers. |
| `phase7b_scaling.py`, first run | complex Lanczos (ncv = 20) on the χ₁ shadow at L6 had not converged after about 22 min; killed. Restarted with the exact scalar form H = H_s ⊗ I₂ for ±1 links and ncv = 64. The trivial and Z₂ L6 results of the first run were reused unchanged. |
| `phase7_periodic_search.py 4`, first run | the m = 3 search ran about 1 h with no progress output under a 20M-node cap; stopped without a result. Rerun per torus with explicit 3M-node caps and logging (`one m a b c CAP` mode). m = 4 was not attempted. |
| `phase7b_controls.py`, first version | too-strict geometry assertion (tile labels differ between decorations), and plaquettes at coordinate 0 along the edge axis omitted. Fixed; the final flux fractions equal `phase5b_sweep.predictors` exactly. |

---

## 3. Corrections and errata

Corrections to committed Phase VI claims and to the uncommitted Phase VII draft:

| # | previous claim | correction |
|---|---|---|
| E1 | Phase VI Thm F′: "9 forced two-cycles per level-1 supertile" (proper frames) | **True for proper frames only.** It fails for 1 391 616 of the 1 673 055 improper assignments. Counterexample: π ≡ id, octant s = (−,+,+), m = 0 (Lean `forced_fails_improper`). "Not pure gauge" holds for all compatible frames through the weaker, sharp count "≥ 12 of 21" (§4), which supersedes the 9-list for that conclusion. |
| E2 | Phase VI: improper frames "sampled, 20 000, not proved" | **Closed**: exhaustive over all 6⁸ assignments, plus a proof. |
| E3 | Phase VI Thm F: 167/100, proper frames | **Valid.** Sharpened to 41789/25000 and extended to all compatible O(3) frame fields. The block method cannot exceed 1.6715740. |
| E4 | Phase VI Lemma K: "ker H_U ≠ 0 ⇔ pure gauge" | Valid only for the **free** operator on **finite connected** graphs. Fails for the pinned operator, whose kernel is always 0 on patches with boundary. Does not transfer to infinite volume in either direction (§5). |
| E5 | Phase VI Cor. F″: E(FR30) ≥ 4.008 > 3.8223 ≥ E(Z₂) | **Valid**, now with margins 7.954 vs 3.357. |
| E6 | Phase VI §9 decision rule: "approximants converge while bounds stall ⇒ hierarchy" | **Invalid inference.** Corrected in the frozen protocol, and the question is now settled by §6–7. |
| E7 | `phase7_recognizability.py` docstring: "the whole level-1 supertile lies inside the 1-star" | **False.** Children (2,7), (3,6) and (4,5) are at Chebyshev distance 2. The conclusion is recovered through the centre child (§6.3). |
| E8 | draft: one symbol "L_R" for the block bound and the IMS bound | **Renamed** B_R and Λ_R (definitions §6). |
| E9 | draft: "the unamplified ball minima are certified upper bounds on E_FR30" | **Wrong as stated.** D_R ≥ E_FR30 holds by interlacing, but its certificate is a *lower* bound on D_R. The certified upper bound on E_FR30 remains V-E's 8.7649120247. |
| E10 | draft: E(Z₂) ≤ 3.4545713639 (L5) | Valid; tightened to **3.3573965495** (L6). Both are compressions of the same infinite-volume operator (§8). |
| E11 | draft: the 1 672 288 vs 6⁸ discrepancy "explained by one-tile swaps" | **Incomplete.** The classes are 1 sextet (constant π: identical links), 48 one-tile swaps and 714 other pairs. Every equal-key pair differs by −1 on a coboundary (§5). |
| E12 | draft: the hierarchy question posed via E_inf(R) < E_FR30 | **Moot.** E_inf(R) = E_FR30 for all R ≥ 1 by Theorem 6.2. |
| E13 | draft: the periodic search "suggests aperiodicity" | It covers only the period lattices mΛ: m ≤ 2 exhausted for both index-7 lattices; m = 3 capped at 3M nodes, not exhausted. It corroborates, but does not prove; the proof is Theorem 6.2. |

---

## 4. Forced curvature (Proposition 1) — **proved** [P, L, C]

**Setting.**
- In parent coordinates, the centre chair has frame P(π_c), and the octant v chair has frame D_{s(v)}P(π_v), with s(v) = 1 − 2v.
- The incidence structure, derived from the 48 panels, has 41 fundamental cycles and exactly 21 two-cycles: centre × 7 octants × third axis m.

**Lemma 4.1 (two-cycle holonomy with det factors).**
- W ∼ det M_a det M_b (σ·M_aᵀe_m)(σ·M_bᵀe_m).
- Hence W = 1 ⇔ M_aᵀe_m ∥ M_bᵀe_m and det M_a det M_b s_a(m) s_b(m) = 1.
- *Proof.* The corner identity gives (σ·Mᵀe_k)(σ·Mᵀe_l) = i det M ε_klm σ·Mᵀe_m; apply it to both turns. ∎
- *Checked* against explicit Q₈ products on all 6⁸ × 21 = 35 271 936 two-cycles: 0 mismatches (`phase7_twocycle_formula.json`).

**Theorem 4.2.** For every compatible frame field, at least 12 of the 21 two-cycles are non-trivial.

*Proof.*
- Two permutations of three letters agree at 0, 1 or 3 points.
- If π_c ≠ π_v, octant v has at most 1 trivial two-cycle.
- If π_c = π_v, then det M_c det M_v = Π s(v), and the trivial two-cycles are those m with s_v(m) = Π s(v): three for v = 0, one otherwise.
- The total is at most 3 + 6 = 9 trivial. ∎

*Certification.*
- Lean `octant_bound`, `total_bound`, `bound_attained` (see the Lean audit below).
- Exhaustive count: the minimum over all 6⁸ assignments is exactly 12.

**Python ↔ Lean correspondence** (`test_lean_predicate_matches_explicit_holonomy`).
- The Lean predicate `trivial` agrees with the explicit holonomy in the real geometry for all 36 permutation pairs × 21 two-cycles.
- Lean's list p = [π0, π1, π2] corresponds to the frame D_s P with P[i, p⁻¹(i)] = 1. The relabelling p ↔ p⁻¹ preserves the sign, and every theorem quantifies over all permutations.

**Lean audit.**

| file | imports | theorems | axioms |
|---|---|---|---|
| `certificates/Phase7Counting.lean` | none (core Lean 4.35.0) | 6 | propext, Classical.choice, Quot.sound; no `sorry`, no `native_decide` |
| `certificates/Phase6Gauge.lean` | none | `corner_identity`, `straight_identity`, `two_cycle_classes` | **none** |

The kernel certifies the encoded finite propositions. That they model the geometry is established separately by the Python correspondence test above. Lean proves nothing about the tiling itself.

**Corollaries.**
- No compatible frame field is pure gauge, on any patch containing a level-1 supertile or on any infinite tiling with a level-1 composition.
- For proper frames, the 9 configurations with s_v(m) = −1 are never trivial (Phase VI F′, Lean `forced_proper`). The list fails for improper frames (E1).

**Why geometry compatibility is necessary.** Constant frame fields, for example M ≡ I, give U ≡ 1, which is pure gauge with floor 0. They are not compatible.

**Gauge invariance.**
- Holonomy classes are conjugation invariant.
- Global signed-permutation rotations M ↦ gM, n ↦ gn leave every link unchanged.

---

## 5. Uniform gap (Proposition 2) — **certified** [C]

**Operators.**
- Free: H_U = D_U†D_U = Deg − A_U. Pinned: H_pin = 24 − A_U = H_U + diag(24 − Deg).
- Both act on ℓ²(𝒫) ⊗ ℂ², and they coincide on infinite tilings, where Deg ≡ 24.

**Theorem 5.1.** For every compatible frame field (proper or improper) and every union 𝒫 of level-1 supertiles, including infinite tilings with a level-1 composition: H_pin ⪰ H_U ⪰ (41789/25000)·I.

*Proof.*
- Drop the inter-block panels, each term ≥ 0: ⟨ψ, H_Uψ⟩ ≥ Σ_B ⟨ψ_B, H_U^{(B)}ψ_B⟩.
- The blocks partition the tiles, so there are no overlaps and no multiplicity.
- Each block is unitarily equivalent, after relabelling and a global O(3) link-invariant rotation, to one of the 6⁸ level-1 configurations.
- Every configuration satisfies H_U^{(B)} − (41789/25000) ≻ 0.
- On infinite tilings the inequality holds for finitely supported ψ, which are dense; the operator is bounded. ∎

**Certificates.**
- Exact Sylvester/Bareiss over ℤ[i] (16 × 16 per gauge class).

  | frames | gauge classes | constant | failures |
  |---|---|---|---|
  | proper | 6561 | 167/100 and 41789/25000 | 0 |
  | improper | 1 672 288 | 41789/25000 | 0 |

- The minimum λ_min over all configurations is 1.6715739836. The test rejects min + 10⁻⁵, so the block method's best constant lies in [1.67156, 1.67158].

**Count reconciliation** (`phase7b_consistency.json`).

| set | assignments | distinct tree-gauge keys |
|---|---|---|
| proper | 6561 | 6561 |
| improper | 1 673 055 | 1 672 288 |
| proper ∩ improper | — | 0 |
| total | 6⁸ = 1 679 616 | 1 678 849 |

- The improper collisions are 1 sextet (π constant: every link equals s_a(k)s_b(k)·1, the Z₂ reflection connection), 48 one-tile swaps and 714 other pairs.
- Every pair has links differing by −1 on a set of panels and equal keys, so the two members are related by a central ±1 gauge transformation.
- Equal keys ⇒ gauge equivalence ⇒ unitarily equivalent operators. So one representative per key covers **every** assignment exhaustively.

**Reconciling the constants.** All are lower bounds on spectra of the same operator family, over different configuration spaces.

| number | operator | geometry / boundary | configuration space | meaning |
|---|---|---|---|---|
| 167/100, 41789/25000 | free H_U on one level-1 supertile (8 tiles, 48 internal panels) | Neumann block | all proper (or all compatible) frames | certified lower bound on every block's λ_min, hence on inf σ(H_U) for every compatible field on unions of level-1 supertiles |
| 1.6715739836 | same block | same | all compatible frames | the actual minimum λ_min (float), above both certified constants |
| B₂ = 4.008196 | 24 − A_U on the infinite tiling | infinite, Deg = 24 | FR30-decorated tilings with legal 2-stars (𝒯₂ = Ω_FR30) | certified lower bound on E_FR30, via radius-2 blocks |
| Λ₁₂ = 7.954292 | same | same | 𝒯₁₂ = Ω_FR30 | certified lower bound on E_FR30, via §7 |

**Zero modes (Lemma K, corrected scope) [P].**
- On a finite connected graph, ker H_U ≅ {v : Wv = v ∀ holonomies}, so dim ker ∈ {0, 2}, and it equals 2 iff the connection is pure gauge.
- H_pin ≻ 0 on every patch with a boundary tile, for every connection. Trivial level 1: λ_min = 11.21.
- **Infinite volume, direction 1.** inf σ = 0 does not imply an ℓ² kernel: trivial links have inf σ = 0 (pinned bottoms 0.139 at L5, 0.0365 at L6) and no ℓ² zero mode.
- **Infinite volume, direction 2.** "Not pure gauge ⇒ gap" is false: flux confined to a finite region leaves inf σ = 0.
- Hence the infinite-volume gap needs *uniform* frustration (Theorem 5.1).

---

## 6. Local determinacy (Proposition 4) — **proved** [P + C]

### 6.1 The legal types and their completeness

**Construction.** V₁ is the forward Φ-orbit of one legal 1-star; then V₂ = Φ₂(V₁), V₃ = Φ₃(V₂), V₄ = Φ₄(V₂).

**Closure lemma** [P]. *The r-star of a child a of A lies in σ(⌈r/2⌉-star of A).*
- *Proof.* Let c be a cube at Chebyshev distance ≤ r from a cube 2q + d of a, where q is a parent-level cube of A and d ∈ {0,1}³.
- Then c_i ∈ [2q_i + d_i − r, 2q_i + d_i + r], so ⌊c_i/2⌋ ∈ [q_i − ⌈r/2⌉, q_i + ⌊(r+1)/2⌋], and ⌊(r+1)/2⌋ = ⌈r/2⌉.
- So the parent-level cube ⌊c/2⌋ lies within ⌈r/2⌉ of q. Its owner B is in the ⌈r/2⌉-star of A, and c is owned by a child of B, since parent cubes are the aligned 2×2×2 blocks of their children. ∎
- Every application of Φ also asserts the instance computationally.

**Proof of completeness of V₁.**
- Every legal 1-star τ occurs as the complete 1-star of a tile b inside some σᵏ(t).
- The frame substitution is primitive: M² > 0 on the 24 frames, check P. So the seed's centre tile s has a level-j descendant t″ with the frame of t. Then σᵏ(t″) is a translate of σᵏ(t) and contains a copy of b with 1-star τ.
- That copy is a level-(j+k) descendant of s.
- The 1-star of a level-n descendant of s is reached from the seed by n applications of Φ (closure lemma, asserted instance by instance in `Phi_r`). So τ ∈ orbit.
- V₂, V₃, V₄ are complete because the r-star of a child lies in σ(⌈r/2⌉-star of its parent), each instance asserted. ∎

**Independent reconstruction** (`phase7b_census.py`: separate tile generator, distance-based star definition, raw-pose keys).
- Complete stars in T₆: 238 328 / 232 560 / 210 232 / 208 880 for R = 1 / 2 / 3 / 4.
- Types: 72 / 165 / 445 / 762.
- The census sets are *equal* to the Φ-generated sets: **equal for R = 1, 2, 3, 4**.

### 6.2 Theorem (local rules at radius 1)

> **Theorem 6.2.** Let Y be a tiling of ℤ³ by chairs with proper frames such that every 1-star of Y is a legal FR30 1-star (Y ∈ 𝒯₁). Then:
> - Y = σ(Y′) for a unique Y′ ∈ 𝒯₁;
> - Y ∈ Ω_FR30;
> - Y is non-periodic;
> - E(Y) = E_FR30.
>
> Hence 𝒯_R = Ω_FR30 and E_inf(R) = E_FR30 for every R ≥ 1.

**Finite checks** (`phase7b_local_rules.py`; all computed from the complete set V₁, not from a census).

| check | statement | result |
|---|---|---|
| **P** | primitivity of the frame substitution | M² > 0 |
| **R0** (recognizability) | for every (legal parent 1-star, child index) pair, inflate and record the child's 1-star type and role (child index, parent frame, parent translation) | every legal type has **exactly one** role; V₁ = Φ(V₁). Only one type plays the centre child. |
| **S** | in the level-1 supertile the centre child is within Chebyshev distance 1 of all 7 siblings; the other pairs are within 1 except (2,7), (3,6), (4,5) at distance 2 | for every legal 1-star, every distance-1 sibling predicted by its role is a tile of the star with the predicted pose |
| **A** (sibling consistency) | for every legal τ_a, every distance-1 sibling b, and every legal τ_b compatible with τ_a (equal cube ownership wherever both define it), role(τ_b) predicts the same parent | 1246 compatible pairs, all consistent |
| **B** (desubstitution) | with P fixed (rotation and translation covariance), enumerate all mutually compatible legal stars of P's 8 children with the right roles. Then resolve the parent of every tile owning a child cube of a parent-level cube in P's 1-star region: if a tile's compatible legal stars predict one parent it is forced; otherwise branch over the distinct predicted parents, adding only the cube assignments common to the group. This over-approximates, since the true star lies in exactly one group. | 72 configurations, 60 branches pruned as inconsistent, **every derived parent 1-star legal**, and together they are exactly V₁ |

*Proof of Theorem 6.2 from the checks.*
- **Each tile has a parent.** Every tile a of Y has a unique role (R0). The centre sibling c₀ is in a's 1-star (S) and has the same parent (A).
- **The parent's 8 children are present.** c₀'s 1-star contains all 8 children with the predicted poses (S with c = 0). Each of them is at distance 1 from c₀ and so shares the parent (A).
- **Y = σ(Y′).** Parents partition Y into complete supertiles, so Y = σ(Y′) for a tiling Y′ by chairs with proper frames.
- **One parent grid.** Neighbouring parents are on the same grid (aligned translations, asserted in B), so Y′ lies on one grid.
- **Y′ ∈ 𝒯₁.** Covariance lets every parent be moved to P = (I, 0); then check B shows that Y′ ∈ 𝒯₁.
- **Every patch is legal.** Iterating, Y = σⁿ(Y⁽ⁿ⁾) with Y⁽ⁿ⁾ ∈ 𝒯₁ for every n. A finite patch K of Y lies in σⁿ(1-star of the level-n ancestor of one of its tiles) once 2ⁿ > diam K + 2. That 1-star is legal, and σⁿ maps legal patches to legal patches, so K is legal and Y ∈ Ω_FR30.
- **Non-periodicity.** Roles are translation-equivariant. If Y + t = Y, then the parents shift by t, so t ∈ 2ℤ³ (one grid), and Y′ has period t/2. By induction t ∈ 2ⁿℤ³ for every n, so t = 0.
- **E(Y) = E_FR30.** Ω_FR30 is minimal (primitivity), so every finitely supported trial vector on one hull element has a copy with the same Rayleigh quotient on every other. ∎

### 6.3 Answers to the brief's questions (C1–C5)

| # | question | answer |
|---|---|---|
| 1 | what in a 1-star determines the role | the *type* (relative frames and translations of the 9–27 tiles of the 1-star) determines the child index and the parent's relative frame and translation (R0) |
| 2 | is the decomposition unique at every level | yes: Y⁽ⁿ⁾ ∈ 𝒯₁ at every level (B), and R0 applies again |
| 3 | how recognizability propagates under inflation | through check B: the parent tiling is again 1-legal, so recognizability holds at every level with the same radius |
| 4 | scope | every tiling of ℤ³ by chairs with proper frames whose 1-stars are legal, not only the computed FR30 tiling. Equivalently the whole hull, which equals 𝒯₁. |
| 5 | essential assumptions | (i) proper frames (the legal types contain only the 24 rotations; mirror images are excluded, which fixes the chirality); (ii) tilings of all of ℤ³, with no boundary; (iii) the legality predicate is the FR30 one. No extra matching decorations are needed: the frames are the decoration. |

### 6.4 Periodic obstruction

**Proof.** The proof of non-periodicity is Theorem 6.2.

**Bounded search (corroborating only).** Exact cover on ℤ³/(mΛ), for both index-7 chair lattices Λ.
- Controls:
  - with legality off, the crystal is found;
  - with the legal set replaced by P₁'s own 1-star types, P₁ is found;
  - P₁'s 7/8 illegal stars are reproduced.
- Results: m = 1 (42 nodes) and m = 2 (10 338 nodes) exhausted with no solution, for the first lattice; the second lattice, ker(x + 4y + 2z mod 7), is likewise exhausted at m = 1 (42 nodes) and m = 2 (10 338 nodes). At m = 3 (27 tiles per period) both lattices stopped at the 3 000 000-node cap without a solution — **not exhausted**, so no conclusion at m = 3. m = 4 was not run.
- Scope: the search covers only tilings whose period lattice contains mΛ for the listed m. Every periodic tiling has a period lattice containing 7·index(L)·Λ, so only an unbounded search would be exhaustive.

---

## 7. Spectral localization (Proposition 5) — **theorem with certified constants** [P + C]

### 7.1 Discrete IMS identity: every term

**Setting.**
- x_a is the centroid of tile a; φ is the Dirichlet ground state of B_ρ ⊂ ℝ³; χ_y(a) = φ(x_a − y)/‖φ‖₂.
- **Normalisation.** ∫χ_y(a)² dy = 1.
- **Overlap.** ∫χ_y(a)χ_y(b) dy = c(|x_a − x_b|/ρ), with c(η) = [π(1 − η/2) sin πη + 1 − cos πη]/(π²η) for 0 < η ≤ 1.
  - Derivation: the 3D radial convolution formula.
  - Checks: sympy symbolically; adaptive radial quadrature; an independent *Cartesian* 3D grid quadrature. The maximum deviation is 6.2·10⁻⁷ (`phase7b_ims_check.json`).

**The commutator form.**
- For H = 24 − A_U: ∫χ_y H χ_y dy = H − ½∫[χ_y, [χ_y, H]] dy.
- The double commutator has entries (χ_y(a) − χ_y(b))² H_ab.
- After integration this gives H + W, with W_ab = w_ab A_ab, w_ab = 1 − c(|x_a − x_b|/ρ), and W_aa = 0.

**Equivalent exact form.** Panel-adjacent tiles satisfy |x_a − x_b| ≤ 15/7 < ρ, so c > 0 on every link, and

  ⟨ψ, (24 − A_U)ψ⟩ = ∫⟨χ_yψ, (24 − Ã)χ_yψ⟩ dy,  Ã_ab = A_ab / c(|x_a − x_b|/ρ),

for every finitely supported ψ. This is exact: there is no remainder term.

### 7.2 Theorem

> **Theorem 7.1.** Let R ≥ 6, ρ = R − 311/175 (311/175 > r_c = √619/14) and B_t = {a : |x_a − x_t| < R}. Define
> - Λ_R := min over legal t of λ_min((24 − Ã_ρ)|_{B_t});
> - D_R := min over legal t of λ_min((24 − A)|_{B_t}).
>
> Then:
> - **(a)** E(Y) ≥ Λ_R for every Y ∈ 𝒯_R; in particular E_FR30 ≥ Λ_R.
> - **(b)** D_R ≥ E_FR30.
> - **(c)** Λ_R ≥ D_R − ε(ρ).
> - **(d)** D_R ≤ E_FR30 + ε(ρ).
> - **(e)** ε(ρ) := max over legal 1-stars of Σ over 24 panels of (1/c(|h_f|/ρ) − 1) ≤ K(ρ)·S₁/ρ², with S₁ = 4734/49 and K(ρ) = (π²/6)/(1 − π²(15/7)²/(6ρ²)).
>
> Hence |Λ_R − E_FR30| ≤ ε and |D_R − E_FR30| ≤ ε, and both converge to E_FR30 at the explicit rate O(R⁻²).

**Proof.**
- **Covering for (a).** For y in the closure of tile t, supp χ_y ⊂ {a : |x_a − y| < ρ} ⊂ B_t, because |y − x_t| ≤ r_c.
- **Locality.** B_t ⊂ R-star(t): the cubes containing x_a and x_t are at Chebyshev distance ≤ ⌈ρ + r_c⌉ ≤ R.
- **(a).** Each tile's R-star is legal, so the restricted operator is one of the enumerated legal balls. Cauchy interlacing, then integration in y, gives E(Y) ≥ Λ_R.
- **(b).** (24 − A)|_{B_t} is a compression of FR30's operator, since the ball is legal.
- **(c).** Weyl's inequality with δA_ab = A_ab(1/c − 1). Its norm is at most the maximum row sum ≤ ε: at most 24 panels, each link of norm 1.
- **(d).** Take ψ with ⟨ψ, Hψ⟩ ≤ (E_FR30 + η)‖ψ‖². The identity gives some y with ⟨χ_yψ, (24 − Ã)χ_yψ⟩ ≤ (E_FR30 + η)‖χ_yψ‖². Since 24 − A = (24 − Ã) + δA and supp χ_yψ ⊂ B_t, this gives λ_min((24 − A)|_{B_t}) ≤ E_FR30 + η + ε.
- **(e).** By Fourier, 1 − c(η) = ½∫(χ_y(a) − χ_y(b))² dy ≤ π²η²/6, using 4 sin²(x/2) ≤ x² and the isotropy of φ. So 1/c − 1 ≤ (π²η²/6)/(1 − π²η²/6), and the bound follows with η ≤ (15/7)/ρ.
- **Covering of the hull.** Every FR30 tile is a descendant, ⌈log₂R⌉ levels down, of a tile with a legal 1-star (V₁ complete, §6.1). Each enumerated R-star is asserted complete inside σ^m(τ), and B_t ⊂ R-star is asserted. ∎

**Convergence.** Λ_R, D_R → E_FR30 unconditionally: the only inputs are legality (§6.1) and the bound on ε.

**Relation to E_inf(R).** By Theorem 6.2 the true infimum over 𝒯_R equals E_FR30, so the bounds are bounds on the floor itself, not on a smaller local quantity.

### 7.3 Certified numbers

How the numbers are certified (`phase7_ims.py`):
- Each distinct legal ball is certified at a common dyadic μ by a blocked Cholesky factorisation of the real form, with explicit pivot divisions and conventional GEMM updates. Higham's Thm 10.3 bound applies: ‖ΔM‖₂ ≤ γ_{N+1}‖L̂‖_F².
- The error of the stored amplification factors is bounded by mpmath interval arithmetic.
- The exact Bareiss test on the R = 6 minimiser (complex dimension 288) confirms the bound and rejects λ + 10⁻⁶.

| R | ρ | legal balls | tiles/ball | D_R (certified ≥) | **Λ_R (certified)** | ε(ρ) | K(ρ)S₁/ρ² |
|---|---|---|---|---|---|---|---|
| 6 | 4.2229 | 325 | 118–145 | 9.4166327 | **3.6555586** | 10.04 | 15.46 |
| 8 | 6.2229 | 747 | 290–321 | 9.0515203 | **6.5627832** | 4.23 | 5.10 |
| 10 | 8.2229 | 1440 | 566–624 | 8.9143715 | **7.5112581** | 2.36 | 2.65 |
| 12 | 10.2229 | 2315 | 1009–1072 | 8.8569812 | **7.9542920** | 1.51 | 1.64 |

**Reading the table.**
- The localization cost actually paid, D_R − Λ_R, is 0.57–0.60 of ε, because the local ground states feel the frustrated links.
- Two-sided: E_FR30 ∈ [Λ₁₂, min(D₁₂, 8.7649120247)] = [7.954292, 8.7649120247].
  - D_R's float values (9.42, 9.05, 8.91, 8.86) are ≥ E_FR30 and decrease toward it [E]. Their certificates bound them from below and are not used as upper bounds.
- No sequence was fitted. The R-dependence is the proven bound (e).

**Verification.**
- **Finite patches, three connections.** The theorem's finite-patch analogue, λ_min(H|_K) ≥ min over t of λ_min((24 − Ã)|_{B_t ∩ K}), is tested against exact eigenvalues for a level-3 supertile K inside the level-5 supertile:

  | connection | exact λ_min(H\|_K) | IMS bound (R = 6) |
  |---|---|---|
  | FR30 | 9.3785 | 4.0576 |
  | Z₂ | 5.1327 | −0.918 |
  | trivial | 1.6695 | −5.166 |

  All hold, and the direction is never violated.
- **Second implementation** (independent tiles, operator and keys; overlap by quadrature, not the closed form).
  - R = 6: 325 balls; D₆ = 9.416634264668 and Λ₆ = 3.655559949, identical to the main code.
  - R = 8: 747 balls (equal to the main enumeration), D₈ = 9.051521980916, Λ₈ = 6.562784793 (main code: 9.051521980916, 6.562784793).

---

## 8. Abelian versus Q₈ (Proposition 3) — **certified separation, interpreted narrowly**

**Standardisation.** Everything below shares one setting:

| item | standard |
|---|---|
| graph | the chair geometry (identical for all decorations; tile labels differ) |
| operator | 24 − A_U |
| finite-volume quantity | Y_L = λ_min of the compression to the level-L supertile, an upper bound on the hull floor |
| infinite-volume quantity | E = inf σ on any hull element |
| flux statistics | plaquette classes, f_m1 and f_trl, with Wilson density w = f_trl + 2·f_m1 (identical to `phase5b_sweep.predictors`: FR30 L4 f_m1 = 0.0797, f_trl = 0.4008) |

| system | links | Abelian | hull-covariant | w (L4) | Y₃ | Y₄ | Y₅ | Y₆ | certified lower on E | certified upper on E |
|---|---|---|---|---|---|---|---|---|---|---|
| trivial | 1 | yes | yes | 0 | 1.6695 | 0.5027 | 0.1386 | 0.03646 | 0 | 0.0364608284 (E = 0) |
| Z₂ reflection (π ≡ id) | ±1 | yes | yes | 0.5445 | 5.1327 | 3.8223 | 3.4546 | 3.3574 | 1.67156 (Thm 5.1) | **3.3573965495** |
| χ₂∘U_FR30 | ±1 | yes | yes | 0.4839 | 6.7713 | 5.5894 | 5.3870 | 5.3286 | — | 5.3869801094 (L5); **5.3285882042** (L6) |
| χ₁∘U_FR30 (= χ₃) | ±1 | yes | yes | 0.5596 | 9.2540 | 7.9266 | 7.7001 | 7.6345 | — | 7.7001335057 (L5); **7.6345317659** (L6) |
| **FR30** | Q₈ | no | yes | 0.5602 | 9.3785 | 8.9196 | 8.7970 | 8.7701 (recomputed = V-E) | **7.954292** | 8.7649120247 (V-E L7) |
| i.i.d. Q₈ (2 seeds) | Q₈ | no | no | 1.00 | 15.06 | 14.50 | 14.36 | — | — | **E = 0 a.s.** |
| i.i.d. Z₂ (2 seeds) | ±1 | yes | no | 1.00 | 14.30 | 13.39 | 12.55 | — | — | **E = 0 a.s.** |

**What the Z₂ certificate bounds.**
- The exact Rayleigh quotient (a rational number, computed from a Gaussian-integer vector) bounds λ_min of the *finite* level-6 pinned matrix.
- That matrix is the compression of the infinite-volume Z₂ operator to the level-6 supertile. This is the embedding: the supertile occurs in every element of the reflection-only hull, which is primitive and therefore minimal.
- So it also bounds E_Z₂ for every hull element. It bounds nothing else.

**Random links.**
- The patch T_L carries all-trivial links with probability 8^{−#panels} > 0, and such patches recur independently.
- So almost surely there are arbitrarily large pure-gauge regions, and the infinite-volume floor is 0. The large finite-volume values are typical-region values.
- i.i.d. links therefore fail the hypothesis of Theorem 5.1 (uniformity), and they are excluded from the infinite-volume comparison.

**Certified separations.**
- E_FR30 ≥ 7.954292 exceeds the upper bounds of Z₂ (3.357) and of all three Abelian shadows (7.6345, 5.3286, 7.6345 at L6).

**Interpretation.**
1. **Non-commutativity contributes.** χ₁∘U_FR30 has the same geometry, the same hierarchy, the same Abelianised flux pattern, and the same Wilson action density (0.5596 vs 0.5602). FR30 nevertheless exceeds it in infinite volume, with a certified margin ≥ 0.320 (7.954292 − 7.6345318), and by 1.10 at level 5 [E].
2. **The group is not the main factor.** Z₂ reflection and χ₁ are both Abelian with similar w (0.54 vs 0.56), yet their level-6 floors are 3.36 vs 7.63: the *spatial arrangement* of the flux dominates. i.i.d. Z₂ beats FR30 in finite volume.
3. **So the statement is not "Q₈ is essential".** It is: *for the FR30 flux arrangement, the non-Abelian connection has a higher floor than every Abelian projection of itself.*

**The 264 rule classes (D)** (`deliverables/PHASE7_RULE_TABLE.md`, every class listed).
- Results (all 264 classes, none missing):
  - All rule substitutions are primitive (M² > 0 on the 24 frames) and census-consistent.
  - B₂ ∈ [2.382, 4.580], median 3.362.
  - **134 classes are certified above Z₂** (B₂ > 3.3573965495).
  - **130 are inconclusive** (B₂ ≤ 3.3574).
  - FR30's B₂ = 4.008 is not the largest (class 3718: 4.580; class 1387: 4.493).
  - The upper-side values are Y₄ ∈ [6.096, 9.517].
- Separation from Z₂ is certified only where B₂ > 3.3573965495. The other classes are inconclusive, not failures: B₂ is a radius-2 bound and is loose by 4–5 units for FR30.
- Phase V-D: across the 264 classes, a two-parameter flux model (f_trl, f_m1) explains CV-R² = 0.80 of the level-4 floor. FR30 sits +0.77 above it.

---

## 9. Hierarchy dependence (Proposition 6) — **not established; negative result with a structural reason**

**Structural reason** [P].
- By Theorem 7.1, E_FR30 = lim_R D_R = lim_R Λ_R, both minima over the *set* of legal balls. Patch frequencies do not enter.
- By Theorem 6.2, that set is determined by V₁, and V₁ forces the hierarchy.
- For the band bottom, "local frustration" and "hierarchy" are therefore the same information, and no control can vary one while holding the other fixed.
  - A tiling with FR30's 1-stars *is* an FR30 hull element.
  - Every non-hierarchical control (Phase V-B: iid, coarse, fine, shuffle, flip) necessarily changes the local patches. Its floor differences are confounded with local differences.

**Pre-registered scale observable** [E] (`phase7b_scaling.py`).
- Defined in the script before any level-6 control value existed: r_L = (Y_{L−1} − Y_L)/(Y_{L−2} − Y_{L−1}).
- Dirichlet confinement of a dispersive bulk ground state gives r_L → 1/4.

| system | r₄ | r₅ | r₆ | r₇ |
|---|---|---|---|---|
| trivial | 0.379 | 0.312 | 0.281 | — |
| Z₂ | 0.336 | 0.281 | 0.264 | — |
| χ₁ | — | 0.171 | 0.290 | — |
| χ₂ | — | 0.171 | 0.289 | — |
| FR30 | 0.328 | 0.267 | 0.219 | 0.194 (V-E) |

- **FR30 is the only matched system whose approach ratio stays below 1/4.** Its r_L decreases monotonically: 0.328, 0.267, 0.219, 0.194. Its ground state concentrates as the level grows (IPR·n = 6.4, 9.1, 19.9, … 121 at L7, Phases V-A/V-E).
- FR30's own Abelian shadows, with the same geometry, the same hierarchy and the same Wilson density, dipped to 0.17 at L5 but returned to 0.29 at L6. The level-5 dip was not stable.
- Z₂ (0.264) and trivial links (0.281) approach 1/4 from above, which is dispersive confinement.
- **Conclusion.** The persistent sub-1/4 approach is a finite-size signature of the *non-Abelian* FR30 connection, isolated against its hierarchy-preserving Abelian shadows. It is not attributable to the hierarchy as such: the shadows carry the same hierarchy and do not show it.
- With levels ≤ 7 this is a finite-size observation [E]. No asymptotic claim is made.

**Phase V-D result, re-read.**
- FR30's level-4 floor lies +0.77 above the two-parameter flux model, while every non-self-similar V-B control lies below it.
- This is a correlation between finite-volume pinned bottoms and a fitted model, not a matched intervention: flux pattern and local patches differ between FR30 and the controls.
- It does not survive as a causal hierarchy signature.

**The invariant that remains** [P, standard theory].
- The integrated density of states depends on patch *frequencies* (Shubin trace formula), not only on the patch set.
- By the gap-labelling theorem, its values in spectral gaps lie in the frequency module of the hull, which for a substitution tiling is generated by the Perron–Frobenius data of the collared substitution matrix.
- That is the hierarchy-specific spectral quantity. It is not tested here (§12).

---

## 10. Novelty assessment

| result | status |
|---|---|
| Forced curvature (Thm 4.2) | elementary, model-specific counting. New as a statement about this construction; not new mathematics |
| Uniform gap (Thm 5.1) | standard block positivity and exhaustive certification. Model-specific |
| Local rules (Thm 6.2) | the *method* is standard (recognizability plus desubstitution closure; Mozes 1989, Goodman-Strauss 1998, Anderson–Putnam 1998). Novel element: for FR30 the *frame decoration itself* is a radius-1 matching rule, established by a finite computer-assisted check. Model-specific and modest, but a genuine theorem |
| Localization (Thm 7.1) | an application of IMS localization (Cycon–Froese–Kirsch–Simon, *Schrödinger Operators*, 1987, Ch. 3) to a tiling Hamiltonian, in its exact amplified-link form with a closed-form ball autocorrelation. The machinery is established; the certified enclosure E_FR30 ∈ [7.954, 8.765] is new for this operator |
| Non-Abelian vs Abelian shadows (§8) | new and model-specific; the "shadow" control (characters Q₈ → Z₂ applied to the same connection) is a natural matched control. Not a general theorem about Q₈ |
| Hierarchy signature | none established |

---

## 11. Remaining blockers (exact missing items)

1. **Sharper enclosure of E_FR30.**
   - Getting Λ_R ≥ 8.70 needs ε ≲ 0.065, i.e. ρ ≳ 50 (R ≈ 52) with the present constant, or a better partition.
   - The present certification cost grows like R¹²: ball dimension R³, Cholesky cost (R³)³, and R³ balls.
   - **Missing lemma:** a localization whose cost constant is not S₁ = 96.6 — for example anisotropic or tile-adapted cutoffs, or a Temple/Lehmann-type two-sided bound around the D_R minimiser.
2. **Per-rule separation from Z₂.** The remaining inconclusive classes need Λ₈(rule) (§7 machinery per rule), not B₂.
3. **Exact per-star check B.** The canonical check is the grouped over-approximation, which is sufficient. The exact per-star enumeration is a cross-check of the implementation, not a gap in the proof. It was stopped by hand at 2 112 542 configurations (2987 s) and wrote no result file. A complete run needs a memoised enumeration.
4. **Gap labels.** No spectral gap of the FR30 operator above E_FR30 is known rigorously, so the hierarchy-dependent invariant (§9) has not been evaluated.
5. *(Resolved in VII-B.)* The closure lemma now has a paper proof (§6.1), in addition to the per-instance assertions.

## 12. Next decisive result

**Certify one spectral gap of H_FR30 and compute its IDS label.**
- Find an interval (a, b) above E_FR30 with no spectrum:
  - certified absence, by Λ-type local lower bounds applied to (H − a)²-shifted problems;
  - certified presence on both sides, by Rayleigh quotients on legal patches.
- Then compute N(a) from the PF-normalised 1-star frequencies via the local trace formula.

**Why this is decisive.** Theorem 6.2 and Theorem 7.1 together make the floor a support-only quantity. The gap label is the unique spectral number that must carry the substitution's frequency module, the 2-adic/8ᵏ structure.
- If N(a) lies in ℤ[1/8]-combinations of the 1-star frequencies but outside every periodic module (1/n)ℤ, that is the first hierarchy-specific spectral invariant of this model.
- If no gap exists below some energy, that is equally informative.

---

**Machine-readable ledger:** `audit/results/phase7b_ledger.json` (claims, sources, certificates, test commands, statuses, caveats; regenerate with `python -u -I audit/phase7b_ledger.py`).

**Independence of the checks** (brief, item G).
- **Logically independent** of the main implementations:
  - `phase7_adversarial.py`: own Q₈ table, own level-1 geometry rebuilt from its description;
  - `independent_clifford_q8_audit.py`: separate tile generator and matrix links;
  - `phase7b_census.py`: distance-based stars, raw-pose keys;
  - `phase7b_ims_check.py`: separate operator assembly, numeric overlap quadrature, Cartesian overlap check;
  - the Lean files (finite propositions only).
- **Shared** by all of them: the FR30 decoration, the pose convention, and the definitions in `PHASE7_DEFINITIONS.md`.
- **Shared** by `phase7_ims.py`, `phase7b_local_rules.py`, `phase7_periodic_search.py` and `phase7b_census.py`'s generator side: the `phase7_local.py` machinery (`encode`, `Phi_r`, `inflate`).
- **JSON-reading tests** check stored outputs for consistency; they are not independent proofs.

**Rule table:** `deliverables/PHASE7_RULE_TABLE.md`.

**Definitions:** `deliverables/PHASE7_DEFINITIONS.md`.
