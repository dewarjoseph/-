# Phase V-B, Workstream A — reproduction and validation of the Phase V-A baseline

Branch `claude/phase5b-excess-mechanism`; nothing committed; no existing file modified. Date 2026-10-21. Machine: 4 cores shared
with other jobs, `OMP_NUM_THREADS=1`, one heavy process at a time, peak RSS of any process in this workstream 0.44 GB, no
operator above level 5 (dim 65 536). All numbers below were computed in this session unless the method column says
"read from artifact". Code: `audit/phase5b_a_validation.py`; tests: `tests/test_phase5b_a_validation.py`; raw outputs:
`audit/results/phase5b_a_{geometry,bottoms,periodic,controls,lowerbound}.{txt,json}`,
`audit/results/phase5b_a_lean_datafree_{extract.lean,compile.txt}`.

**Method labels.** *independent* = own code written for this workstream with a different design from the Phase V-A
scripts (per-tile/per-cube Pauli-matrix plaquette evaluation; own owner map and panel list; own COO assembly of
`24 I - A`; own solver calls — dense `eigh`, `eigsh` shift-invert, `lobpcg` with a different seed/block; exact `LDL^T` on
the real symmetric embedding with `fractions.Fraction`; own `Lambda_7` crystal, torus and Bloch code). *re-run* = a
Phase V-A script executed again (from a scratch copy when it writes into `audit/results`). *read* = a stored number.
Only the definitions (FR30 table, `U3`, `tiles_at_level`, `panel_edges`, `clifford_link`, `q8label`) are imported; each
of them was re-derived and compared (own pose recursion identical to `tiles_at_level` at levels 1–4, own cube sets
identical, own panel multiset identical to `panel_edges`, own `pauli_link` identical to `clifford_link` on all
24×24×3 (frame, frame, axis) triples).

## 1. Baseline-reproduction table

| item | dossier value | value obtained here | method | discrepancy |
|---|---|---|---|---|
| (a) level-1 inter-tile plaquette classes (N; +1, −1, i, j, k) | 60; 26, 3, 12, 7, 12 | 60; 26, 3, 12, 7, 12 | independent | none |
| (a) level 2 | 792; 385, 42, 124, 117, 124 | 792; 385, 42, 124, 117, 124 | independent | none |
| (a) level 3 | 7728; 3945, 530, 1020, 1213, 1020 | 7728; 3945, 530, 1020, 1213, 1020 | independent | none |
| (a) level 4 | 67680; 35161, 5394, 8188, 10749, 8188 | 67680; 35161, 5394, 8188, 10749, 8188 | independent | none |
| (a) level 5 | 565440; 296121, 48146, 65532, 90109, 65532 | 565440; 296121, 48146, 65532, 90109, 65532 (`phase5a_flux_vs_edge.plaquettes` and `phase5a_independent_enumerator.Level(5)`, both re-run); own enumerator at level 5: see §2(a) | re-run (+ independent, §2a) | none |
| (a) level-5 fractions (nontriv / traceless / −1) | 0.4763 / 0.3912 / 0.0851 | 0.4763 / 0.3912 / 0.0851 (= 269319/565440, 221173/565440, 48146/565440) | re-run + independent | none |
| (a) limit fractions | 17/36 nontrivial; 19/36, 13/144, 1/9, 23/144, 1/9 | not recomputed (consequence of the Lean-checked recursion); level-1..5 fractions 0.5667, 0.5139, 0.4895, 0.4805, 0.4763 → 0.4722 | read | none |
| (b) pinned bottom level 2 (dim 128) | 10.776951 (certified 10.776950512) | 10.776950512, residual 2.0e-14, Kramers split 5.3e-15, next pair gap 0.9005 | independent (dense eigh) | none |
| (b) level 3 (dim 1024) | 9.378470 (certified 9.378470210) | 9.378470210, residual 9.5e-14, Kramers split 3.6e-15, next pair gap 0.2109 | independent (dense eigh) | none |
| (b) level 4 (dim 8192) | 8.919634 (certified 8.919634360) | 8.919634360, residual 1.4e-14, Kramers split 7.3e-14, next pair gap 0.029152 | independent (eigsh shift-invert σ=8, sparse LU, 7 s, 0.25 GB) | none |
| (b) level 5 (dim 65536) | 8.797011 (certified 8.797011333) | 8.797011315, residual 1.9e-08, Kramers split 1.3e-13, next pair gap 0.001969 | independent (lobpcg block 6, seed 1, tol 1e-7, 277 s, 0.44 GB) | none (dossier's floating value 8.7970113; the certified rational 8.797011333 is an upper bound and lies 1.8e-8 above the Ritz value, as it must) |
| (b) monotonicity | non-increasing (theorem) | 10.776951 > 9.378470 > 8.919634 > 8.797011 | independent | none |
| (c) natural FR30 bijection on Λ7/2Λ7 | E_per = 10.644234146 at Γ | own Bloch 10.644234146 at θ=(1,1,1) (diff +1.6e-10); own real-space tori N=2 (dim 128) and N=4 (dim 1024): lowest 10.644234146 (doublet), next 14.984649919 / 12.358560608; plaquette classes per cell {+1:42, −1:26, i:20, j:32, k:24} | independent | none |
| (c) D2 counterexample S=[[1,0,6],[0,1,6],[0,0,8]], frames [2,2,10,10,7,6,16,10] | E_per = 9.633732 (flux 0.5000/0.3750/0.1250) | own Bloch 9.633732107 at θ=(0.84983, 0.85392, 0.79437) (diff +2.9e-10 vs 9.633732107); own tori N=4, N=8: λ_min 9.697684260 = own commensurate Bloch minimum (|diff| ≤ 9e-15), ≥ E_per; classes {+1:72, −1:18, i:14, j:16, k:24} → 0.5000/0.3750/0.1250 | independent | none (torus λ_min 9.6977 > E_per because the band minimum is incommensurate, exactly as the D2 record states) |
| (d) regression constants | −1.904 + 14.303 f_trl + 30.696 f_−1 | string present verbatim in `phase5a_periodic_control_T.txt`; E_fit recomputed from the stored fractions reproduces the JSON E_fit (seed 1: 5.549, seed 108: 6.259) | read | none |
| (d) seed 1, level-4 bottom | 6.92890 (table) | 6.928902 (residual 1.4e-14), diff +2.0e-14; IPR·n 72.011 = stored; interface-1 weight 0.861 = stored | independent | none |
| (d) seed 108, level-4 bottom | 8.60774 | 8.607741 (residual 2.4e-14), diff −7.5e-14; IPR·n 7.990 = stored; interface-1 weight 0.564 = stored | independent | none |
| (d) seeds 1, 108 level-5 fractions | 0.4768/0.4381/0.0386; 0.4705/0.3830/0.0875 | identical (re-run of `plaquettes`); residuals r = +1.141, +2.234 reproduced | re-run | none |
| (d) decorations | seeds 1, 108 | own re-implementation of the RNG draw equals `random_decoration` and the decoration stored in the JSONs | independent | none |
| (d) `phase5a_flux_vs_edge.table()` | stored `phase5a_flux_vs_edge.txt` | re-run on scratch copies of the 19 JSONs: generated part byte-identical to the stored file (the stored file additionally has a hand-appended SUPPLEMENT section) | re-run | none |
| (e) IPR·n, levels 2–5 | 2.39, 6.42, 9.15, 19.93 | 2.3873, 6.4243, 9.1464, 19.9304 | independent | none |
| (e) IPR·n from stored weight files, levels 3–6 | 6.42, 9.15, 19.93, 42.79 | 6.4243, 9.1464, 19.9304, 42.789; own densities vs stored: max diff 6.9e-18 (L3), 6.9e-09 (L4), 2.0e-08 (L5) | read + independent | none |
| (e) depth-1 interface weight / tile fraction | 0.78/0.53, 0.66/0.31, 0.58/0.17 (levels 3–5) | 0.7821/0.5254, 0.6557/0.3118, 0.5816/0.1708 (enrichment 1.49, 2.10, 3.41) | independent | none |
| (e) box counting 1/S2(d), level 4 | 3.161 13.576 78.288 447.829 | 3.161 13.576 78.288 447.829 | independent | none |
| (e) 1/S2(d), level 5 | 3.252 17.356 72.185 301.776 1644.121 | 3.252 17.356 72.186 301.777 1644.124 (stored weights: 72.185 301.776 1644.121) | independent | ≤ 3e-3 relative, solver-tolerance level |
| (e) D2 from consecutive levels | 2.49, 1.88, 1.90 (3→4, 4→5, 5→6) | 2.49, 1.88, 1.90 (5→6 from the stored level-6 weights) | independent / read | none |
| (f) exact lower bound | 3137451/2000000 = 1.5687255 | min over complete-star tiles of T_4 (2744 tiles) and of T_5 (27000 tiles) of Σ_e μ_e = 3137451/500000 exactly, /4 = 3137451/2000000; 544 (T_4) + 16 (T_5) non-flat signatures certified by own exact LDL^T, 0 failures; every certificate rejects μ_e + 2.2e-5; 128 flat signatures exactly singular | independent | none |
| (f) same, Phase V-A script | 3137451/2000000 | `phase5a_star_closure_lower_bound.py` re-run from a scratch copy: output identical to the stored file (timing lines excluded): 72 star types, 207 signatures, 163 certified non-flat | re-run | none |
| (f) improved bound | 12805833/4000000 = 3.2014583 | PENDING_C2 | re-run | PENDING_C2D |
| (f) certified upper bounds | 10.776950512, 9.378470210, 8.919634360, 8.797011333 | PENDING_CUB | re-run | PENDING_CUBD |
| (f) Lean theorem dependency list | 23 declarations, axioms ⊆ {propext, Quot.sound, Classical.choice}, 14 `decide +kernel` | read from `phase5a_lean_full_kernel_compile.txt` (EXIT=0, 454 s, 11.3 GB, sha256 f8f89bb…0de68 = current file); data-free extract (lines 40–79, 181–195, 205–222, 576–705; 212 lines, no data, no sorry/native_decide/axiom) compiled with the kernel in 4.4 s: `closed_form_general`, `step_case_general` depend on [propext, Quot.sound]; `q8_closed` on [propext]; `q8_conj_is_inverse`, `q8_class_conj_invariant`, `q8_class_inverse_invariant` on no axioms — identical to the full-compile record | read + extract compiled | none |

## 2. Details and definitions

**(a) Own enumerator.** For every tile `a`, every cube `c` of `a` and every transverse pair `(i,j)`, the lattice edge
with lower-corner cube `c` is surrounded by `c, c+e_i, c+e_i+e_j, c+e_j`; it is an inter-tile plaquette iff all four
cubes are in the patch and belong to ≥ 2 tiles. The holonomy is the ordered product of explicit 2×2 Pauli-matrix links
`(σ·M_a^T n)(σ·M_b^T n)` (identity inside a tile), classified by trace (±2) and, for traceless holonomies, by the Pauli
axis. No Q8 code table, no grid slicing, no cube→edge attribution shared with the Phase V-A enumerators. Run times:
3.4 s at level 4; level 5 own run: PENDING_OWN5.

**(b) Operator.** `H_pin = 24 I − A`, `A_ab = Σ_panels (a,b) C_ab`, `C_ba = C_ab^†`, panels between the same pair summed
with multiplicity. Own assembly checks: Hermiticity defect exactly 0 (no nonzero entry in `H − H^†`), all entries
Gaussian integers (defect 0.0). Entries of modulus > 1 do occur: pairs of tiles sharing several panels give
off-diagonal blocks such as `−2·C` (see discrepancy D2 below).

**(c) Periodic conventions decoded from `phase5a_d2_census_verify.py`:** `L = ker φ`, basis rows `BL=[[1,1,1],[2,1,−1],[−1,2,1]]`;
`L'` has basis rows `S·BL` (HNF `S` in L-coordinates); cosets indexed by the canonical representative in
`[0,d1)×[0,d2)×[0,d3)` and ordered by the key `(k S^{-1})^T m mod k`; frame indices refer to the list
`diag(s)·P(p)` (p in `itertools.permutations` order, s in `{+1,−1}^3`, det = +1). The chair at lattice point `x`
occupies cubes `x + U3`; the link across a panel with ambient normal `n` is the same Pauli formula as for the
aperiodic tiling. The natural bijection puts the FR30 frame of child `v = m mod 2` on coset `m` (centre frame on
`(1,1,1)`): coset order `[0,0,0],[0,0,1],…,[1,1,1]` → frame slots `[1,2,3,4,5,6,7,0]` → SO(3,Z) indices
`[0,4,21,13,10,2,19,0]`. For `S=[[1,0,6],[0,1,6],[0,0,8]]` the coset representatives are `[0,0,t]`, t=0..7.

**(e) Definitions used (checked against `phase5a_edge_states.py`, `phase5a_scaling_controls.py`,
`phase5a_level6_structure.py`, and used identically here).** Tile density `p_a = |ψ_{2a}|² + |ψ_{2a+1}|²`
(spinor components of tile `a`), normalised to Σ_a p_a = 1, averaged over the two vectors of the Kramers pair (the
pair densities agree to 1.5e-16 at level 4 and 4.1e-09 at level 5, LOBPCG tolerance). `IPR = Σ_a p_a²`, reported as
`IPR·n` with `n = 8^L`. Depth-d ancestor of tile `a` = `a // 8^(L−d)` in the depth-first order of the pose recursion
(child order `[centre, (0,0,0), (0,0,1), (0,1,0), (0,1,1), (1,0,0), (1,0,1), (1,1,0)]`). Depth-d interface tile = tile
incident to at least one panel whose two tiles have different depth-d ancestors; interface weight = Σ p_a over those
tiles; interface fraction = their number / n; enrichment = weight / fraction. Box counting
`S2(d) = Σ_{depth-d children} (Σ_{a in child} p_a)²`, `1/S2(d)` = effective number of occupied children,
`D2(d) = log2(S2(d−1)/S2(d))` (3 for a uniform state); the dossier's "D2 from consecutive level pairs" is
`log2(IPR_L / IPR_{L+1})` (linear size doubles per level). Boundary tile = degree < 24.

**(f) Lower bound.** `h_e` = quadratic form of the 4-cycle of tiles around lattice edge `e` (terms `‖ψ_a − C ψ_b‖²`
for the panels containing `e`); `⟨ψ,Hψ⟩ = ¼ Σ_e h_e` (each panel has 4 edges; verified exactly on T_2 in the tests:
Σ over all edges of `h_e` = 4 H_free, over interior edges = 4 H_pin on tiles all of whose edges are interior). Own
certificate: for each signature, `μ_e = (⌊10⁶ λ_min⌉ − 2)/10⁶` and `h_e − μ_e I` positive definite by exact
rational `LDL^T` of the real symmetric embedding `[[Re,−Im],[Im,Re]]` (positive definite ⇔ the complex form is).
Distinct `λ_min(h_e)`: {0, 2−2cos(π/8), 2−√3, 2−√2, 1, 2}. Every tile with a complete vertex star touches exactly 48
inter-tile edges; the minimum of Σ_e μ_e over the 2744 (T_4) and 27 000 (T_5) complete-star tiles is 3137451/500000
in both cases, so the bound does not need the star-type closure to be reproduced on T_5 (the dossier states T_5
realises all 72 types; here only the minimum over realised stars is recomputed, which is the quantity entering the
theorem together with the closure lemma). My signature key (cyclic tile pattern from the lower-corner cube plus
signed link labels, no canonicalisation) is finer than the Phase V-A key: 672 signatures (544 non-flat, 128 flat) on
T_4, 16 more on T_5, versus 207 (163 non-flat) in `phase5a_star_closure_lower_bound.py` and 205 (161) in the C2 check;
the set of `λ_min` values and the star sums agree.

## 3. Discrepancies found

* **D1 (documentation, framework §3.2 / dossier §3 item 9).** "All matrix entries lie in {0, ±1, ±i, 24}" is not
  literally true for `H_pin`: when two tiles share several panels the off-diagonal 2×2 block is the sum of the links,
  e.g. `−2C` (entries of modulus 2 occur already at level 2; the tests check that the modulus never exceeds the panel
  multiplicity of the pair). The certified Rayleigh quotients are unaffected because `phase5a_certified_upper_bound.py`
  sums per panel in exact integer arithmetic.
* **D2 (ordering convention, not an error).** In the depth-first tile order the first 8^L tiles of T_{L+1} are the
  *centre* child's subtree, not the (0,0,0)-child; the exact compression `H_pin(T_L) = H_pin(T_{L+1})` restricted to
  the (0,0,0)-subtree holds on indices `8^L .. 2·8^L − 1` (verified entry by entry for L = 1, 2 in the tests). The
  dossier's ancestor rule `index // 8^(L−d)` is unaffected.
* **D3 (counting convention).** The number of distinct plaquette signatures differs between the two Phase V-A scripts
  (207 / 163 non-flat in `phase5a_star_closure_lower_bound.py`, 205 / 161 in `phase5a_c2_lower_bound_check.py`) and
  from this workstream (672 / 544 + 16); the three keys canonicalise the 4-cycle differently. The certified quantities
  (λ_min values, μ_e, star sums, the final rational) agree.
* **D4 (precision wording).** The dossier quotes the level-5 bottom as 8.797011 and the certified rational
  8.797011333; the Ritz value obtained here is 8.797011315 (residual 1.9e-8) and C2's value 8.797011315 (residual
  5.9e-7). The certified rational is an upper bound 1.8e-8 above the Ritz value, consistent; the rounded 8.797011 is
  fine, but "8.7970113" (certified-upper-bound file) rounds the Ritz value up. No action needed.
* No numerical discrepancy with any dossier value was found in items (a)–(f).

## 4. Tests

`python3 -m unittest tests/test_phase5b_a_validation.py`: 14 tests, OK, 51.6 s (wall 53.8 s). Coverage: boundary
conditions (interior tiles have degree 24 and boundary tiles < 24; `H_pin − H_free` is diagonal, equal to `24 − deg`,
supported exactly on boundary tiles; exact compression T_L ⊂ T_{L+1} for L = 1, 2; interior rows equal the bulk formula
`24 I − Σ_f C_f`), graph construction (8^L tiles, 7·8^L cubes, exact box filling, `12(8^L − 4^L)` panels, panel
multiset symmetric under reversing the scan direction and equal to `panel_edges`; every panel lies in exactly 4
lattice-edge cycles and the plaquette decomposition identity holds exactly), gauge invariance (random Q8 gauge:
spectrum at levels 2–3 invariant to 1e-10, all five classes invariant, links changed; random SU(2) gauge: spectrum
invariant to 1e-10, the three trace classes invariant), eigenvalue convergence (dense vs LOBPCG at level 3 to 1e-8;
shift-invert vs LOBPCG at level 4 to 1e-8, agreement with the certified 8.919634360 to 2e-9; pinned bottoms
non-increasing over levels 1–4), numerical precision (all entries of `H` and `4H` exact Gaussian integers, Hermiticity
defect exactly 0, all links in Q8 and equal to `clifford_link`, `C_ba = C_ab^†`, own signed labels equal `q8label`).

## 5. Caveats

* Level 5 is the largest operator solved (dim 65 536); level 6 was only re-analysed from the stored weight vector
  (IPR·n 42.789, 1/S2(d) = 4.982, 26.009, 88.838, 294.454, 1140.125, 6126.428); its interface weights were not
  recomputed (they need the level-6 panel list, not built here).
* The level-5 bottom obtained here is a LOBPCG Ritz value (residual 1.9e-8), not an exact certificate; the exact
  certificates were re-run with the Phase V-A script (see table). The lower bound 3137451/2000000 is reproduced
  exactly, but the star-type closure argument (72 types, Lemma 3.5) was not re-derived here; what was recomputed is the
  minimum of the certified star sums over all complete stars of T_4 and T_5.
* The full Lean certificate was not recompiled (11.3 GB); the dependency list is read from the Phase V-A record whose
  sha256 matches the current file, and the data-free extract was compiled with the kernel.
* The limit fractions 19/36 etc. were not recomputed (they follow from the recursion; the level-5 fractions were).
* `phase5a_flux_vs_edge.table()` and the certificate scripts were executed on scratch copies because they write into
  `audit/results`; their outputs were compared with the stored files instead of overwriting them.
