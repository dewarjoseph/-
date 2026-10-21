# Phase 5A, Task A3 — The type recursion as a theorem, and the clean-spectrum criterion (H6)

Status labels used below: **[P]** proved in this document (ordinary mathematics, complete argument given);
**[E]** exact computation performed in this session (command and output file named); **[K]** kernel-checked in
`certificates/TypeSubstitutionCertificate.lean` (earlier phase; re-parsed and re-verified here, not re-compiled);
**[prior]** a saved result of an earlier phase quoted for context, not recomputed here.

Reproduction (from the repository root; total about 6 minutes, < 1.5 GB):

```
python3 -u -I audit/phase5a_recursion_theorem_audit.py     # -> audit/results/phase5a_recursion_theorem_audit.txt
python3 -u -I audit/phase5a_counterexamples.py             # -> audit/results/phase5a_counterexamples.txt
python3 -m unittest tests/test_phase5a_recursion_theorem.py   # 15 tests, ~30 s, no geometry enumeration
```

The main script exec-loads `audit/phase4_type_substitution_proof.py` (the derivation of the 49 panel types and
108 plaquette types and their inflation images, exactly as `audit/export_type_certificate.py` does), rebuilds the
operator, re-enumerates the supertiles of levels 1 to 4 from the geometry, parses the certificate vectors from the
Lean file and recomputes them, and computes the condensation of the type graphs for FR30, the achiral decoration and
two random admissible decorations (the same random stream, seed 2026, as `audit/phase5_universality_types.py`, so
they are that file's decorations #0 and #1; their characteristic polynomials agree with
`audit/results/phase5_universality_types.txt`).

---

## 0. Convention

Count vectors are **columns**: `v_m = (P_m ; Pi_m)` in `Z^157`, `P_m(t)` = number of inter-tile panels of type `t`
in the level-`m` supertile `T_m`, `Pi_m(theta)` = number of inter-tile plaquettes of type `theta`.
The type-substitution operator is

    S = [[M, 0], [A, B]],      S[r, c] = number of fine objects of type r produced by one coarse object of type c,

so columns are indexed by the parent (coarse) type and rows by the child (fine) type, and the recursion is
`v_{m+1} = S v_m + 8^m f`, `f = v_1 = (p_1 ; pi_1)`.

**[E]** Verified in Section 1 of the output: every column of `M` (49 columns) sums to 4, every column of `A` sums to
4, every column of `B` (108 columns) sums to 2; `S` is 157 x 157, block lower triangular, nonnegative integer, with
575 nonzero entries; `sum(p_1) = 48`, `sum(pi_1) = 60`. The row sums are **not** constant:
row sums of `M`: `{0: 30 rows, 7: 12, 11: 2, 17: 4, 22: 1}`; of `A`: `{0: 90, 7: 12, 17: 4, 22: 2}`;
of `B`: `{0: 64, 1: 26, 2: 2, 6: 4, 7: 6, 9: 2, 16: 2, 35: 2}`.

---

## 1. Statement 1 — exact finite-state recursion   **[P + E (levels 1-4) + K (levels 1-2)]**

**Hypotheses.**
(H1) *Exact block substitution.* A prototile `P ⊂ Z^d` (finite union of unit cubes), an integer inflation factor
`L ≥ 2`, a finite group `G ⊂ O(d, Z)` of signed permutation matrices, `Γ = G ⋉ Z^d`, and child poses
`(g_1, t_1), ..., (g_K, t_K)` such that the cubes of the children of the identity pose are **exactly** the cubes of
`L·P`. (Chair/FR30: `d = 3`, `L = 2`, `K = 8`, `G = SO(3, Z)`.)
(H2) *Locality and invariance of the observable.* Panel types are `Γ`-orbits of (two posed tiles, shared face),
plaquette types are `Γ`-orbits of (the ≤ 4 posed tiles around a lattice edge, the edge); the link rule and the
holonomy class are functions of the type.

**Conclusion.** The set of panel and plaquette types occurring in `∪_m T_m` is finite (bounded relative poses
in a finite group times a bounded translation), and for every `m ≥ 1`, **exactly**,

    P_{m+1}  = L^{dm} p_1 + M P_m,
    Pi_{m+1} = L^{dm} pi_1 + A P_m + B Pi_m,

where `M` has constant column sums `L^{d-1}`, `A` has constant column sums `2L(L-1)` (interior edges of the
`L x L` grid covering an inflated face; 4 for `L = 2`), and `B` has constant column sums `L`.

**Proof (parity trichotomy).** `T_{m+1}` is the dilate of `T_m` by `L`: the coarse cube with lower corner `x` is
replaced by the `L^d` fine cubes with lower corners `Lx + {0, ..., L-1}^d`, all owned by children of the coarse tile
owning `x` (H1). Hence the coarse parent of a fine cube `c` is `floor(c/L)`.
*Panels.* The two fine cubes of a fine inter-tile panel have coarse parents that are either equal or adjacent. If
the parents lie in one coarse tile `t`, the panel is interior to `σ(t)`, a rigid copy of `T_1` (equivariance
`σ(γ p) = γ_L σ(p)`, which is immediate from the definition of inflation), and the `L^{dm}` coarse tiles contribute
exactly `L^{dm} p_1`. Otherwise the parents are adjacent cubes of two different coarse tiles, i.e. they share a
coarse inter-tile panel, and the fine panel is one of its `L^{d-1}` covering fine panels: the term `M P_m`. The
cases are disjoint and exhaustive.
*Plaquettes.* Let `e` be a fine edge in direction `k` with midpoint `μ` (`μ_k` half-integer, `μ_i, μ_j` integers).
The four fine cubes around `e` have, in direction `i`, the coordinates `μ_i - 1` and `μ_i`, whose coarse parents
coincide iff `μ_i` is not divisible by `L` (for `L = 2`: iff `μ_i` is odd); same for `j`; in direction `k` all four
share one coarse coordinate. So the set of coarse parents has size 1, 2 or 4 according to whether zero, one or two
of `μ_i, μ_j` are divisible by `L`; these cases are exhaustive and mutually exclusive. (1) If all parents lie in one
coarse tile `t`, `e` is interior to `σ(t)` and contributes to `L^{dm} pi_1`. (2) Otherwise, with 2 parents, they are
adjacent cubes of two different tiles sharing a coarse inter-tile panel and `e` is one of the `2L(L-1)` interior
edges of its covering grid: the term `A P_m`. (3) Otherwise there are 4 parents around a coarse edge, all present
(their children are) and in ≥ 2 tiles: a coarse inter-tile plaquette, of which `e` is one of the `L` fine
sub-edges: the term `B Pi_m`. In cases (2) and (3) the fine edge is indeed a fine inter-tile plaquette (its cubes
belong to children of ≥ 2 coarse tiles), so the column sums are exactly as stated. ∎

**Verification [E]** (`audit/results/phase5a_recursion_theorem_audit.txt`, Section 2). Every fine panel/plaquette
of `T_1, ..., T_4` was classified into its category by looking up the coarse owners of `floor(c/2)`, and every
category identity was checked coordinate-wise on all 157 types, not only in total:

| level m | tiles | inter-tile panels (tile-interior / covering coarse panels) | inter-tile plaquettes (tile-interior / interior edges of coarse panels / halves of coarse edges) | identities |
|---|---|---|---|---|
| 1 | 8 | 48 (48 / 0) | 60 (60 / 0 / 0) | seed |
| 2 | 64 | 576 (384 / 192) | 792 (480 / 192 / 120) | `384 = 8·48`, `192 = M P_1`, `192 = A P_1`, `120 = B Pi_1`: all True |
| 3 | 512 | 5376 (3072 / 2304) | 7728 (3840 / 2304 / 1584) | all True |
| 4 | 4096 | 46080 (24576 / 21504) | 67680 (30720 / 21504 / 15456) | all True |

In addition, **each** of the 8, 64, 512 inflated coarse tiles contributes exactly `(p_1, pi_1)` (equivariance
checked tile by tile), and `v_{m+1} = 8^m f + S v_m` holds in all 157 coordinates for `m = 1, 2, 3`. The class
counts at level 4 (`{+1: 35161, -1: 5394, i: 8188, j: 10749, k: 8188}`) coincide with the recursion's prediction
and with the saved direct enumeration of Phase 4 **[prior]**. The Lean certificate checks the class counts of the
recursion against the geometry at levels 1 and 2 **[K]**.

**What is not formalized.** The trichotomy argument for all `m` is a paper proof (above); it is verified exactly for
`m ≤ 4` and kernel-checked only at the level of class counts for `m ≤ 2`.

---

## 2. Statement 2 — existence of normalized limits   **[P]**

**Hypotheses.** `S` a nonnegative square matrix, `λ > ρ(S)`, `f` any vector, `v_{m+1} = S v_m + λ^m f`, arbitrary
initial vector `v_1`.

**Conclusion.** `λ^{-m} v_m → u := (λ - S)^{-1} f`, and the limit does **not** depend on `v_1`. The error is
`O(m^{k} (ρ(S)/λ)^m)` with `k` < the largest Jordan block of `S`.

**Proof.** `v_m = S^{m-1} v_1 + Σ_{j=1}^{m-1} λ^j S^{m-1-j} f`, so
`λ^{-m} v_m = λ^{-m} S^{m-1} v_1 + Σ_{i=0}^{m-2} λ^{-(i+1)} S^i f`. Since `‖S^i‖ ≤ C i^k ρ(S)^i` and `ρ(S) < λ`,
the first term tends to 0 and the series converges to `Σ_{i≥0} λ^{-(i+1)} S^i f = (λ - S)^{-1} f`. ∎

**Remarks.** (a) For an exact block substitution the hypothesis is automatic: the column sums of `M`, `A`, `B`
force `ρ(S) = max(L^{d-1}, L) ≤ L^{d-1} < L^d = λ` (`d ≥ 2`). No primitivity, irreducibility or aperiodicity of `S`
is used. (b) **Counterexample (b)** (`audit/phase5a_counterexamples.py`, exact): for the *homogeneous* recursion of
the non-primitive substitution `a → aa, b → bb` (`Mat = 2I`, two sink components), the normalized limit exists but
equals the seed frequencies (`a`: (1, 0); `b`: (0, 1); `ab`: (1/2, 1/2); `aab`: (2/3, 1/3)), so for homogeneous
recursions seed-independence requires a unique sink (primitivity). With the same matrix and a forcing term `8^m f`,
`f = (1, 2)`, all seeds give `(8 - Mat)^{-1} f = (1/6, 1/3)`, with deviation exactly `4^{-m}(v_1/2 - 2f/3)`
(checked at `m = 5, 10, 20` for three seeds). The FR30 limit is seed-independent for the second reason, not the first.

---

## 3. Statement 3 — rationality   **[P]**

**Hypotheses.** Statement 2 with `S` an **integer** matrix and `λ` an **integer** (`λ > ρ(S)`), `f` integer.

**Conclusion.** `u = (λ - S)^{-1} f ∈ Q^N` (Cramer's rule); all limiting type and class frequencies are rational,
with denominators dividing `det(λ - S)`.

**Counterexample (a)** [E, exact]: Fibonacci `a → ab, b → a` has finite type (2 letters), exact linear recursion
(verified for `σ^n(a)`, `n = 1..12`) and is primitive, but its Perron root is `φ = (1+√5)/2` and its limiting
frequencies are `(1/φ, 1/φ²) = (−1/2 + √5/2, 3/2 − √5/2)`, irrational. So "finite type ⇒ rational frequencies" is
**false** without an integer dominant eigenvalue; for substitutions this is the constant-length (integer-expansion)
hypothesis, which for block substitutions holds because of (H1).

**Independence from cleanliness** [E]: the random decorations (non-clean spectra), Thue–Morse 2-blocks
(spectrum `{2, 1, −1, 0}`, frequencies `1/6, 1/3, 1/3, 1/6`) and period-doubling (spectrum `{2, −1}`, frequencies
`2/3, 1/3`) all have rational frequencies. Rationality is a consequence of the integer Perron root alone.

---

## 4. Statement 4 — exact finite-size formulas   **[P general; E + K for FR30]**

**General form [P].** Under Statement 2 with `S` integer, let `ν` be the nilpotency index of `S` on its generalized
0-eigenspace and let the nonzero part of `S` be semisimple with distinct nonzero eigenvalues `μ_1, ..., μ_r`. Then
for every `m ≥ ν`

    v_m = λ^m u + Σ_i μ_i^m w_i          (exact, finitely many terms),

with `u = (λ - S)^{-1} f` and `w_i = −(λ - μ_i)^{-1} f_i` where `f_i` is the component of `f` in the
`μ_i`-eigenspace. Proof: decompose `f = Σ_i f_i + f_0`; the `μ_i` parts give `(λ^m − μ_i^m)/(λ − μ_i) f_i`; the
0-part gives `Σ_{k<ν} λ^{m-1-k} S^k f_0 = λ^m (λ - S)^{-1} f_0` as soon as `m ≥ ν` (the sum is then complete), which
is absorbed in `λ^m u`. For `m < ν` the 0-part is incomplete and the formula fails in general. If the nonzero part
is not semisimple, `w_i` is replaced by a polynomial in `m`. ∎

**FR30 instance [E].**
* `charpoly(M) = λ^44 (λ−4)(λ−1)^4`, `charpoly(B) = λ^103 (λ−2)(λ−1)^4`,
  `charpoly(S) = λ^147 (λ−4)(λ−2)(λ−1)^8 = charpoly(M)·charpoly(B)` (exact, fraction-free).
* Semisimplicity: `rank(S − 4) = rank((S − 4)²) = 156`, `rank(S − 2) = rank((S − 2)²) = 156`,
  `rank(S − 1) = rank((S − 1)²) = 149` (geometric multiplicities 1, 1, 8 = algebraic).
* Nilpotency: `rank S = 27`, `rank S² = 10`, `rank S³ = 10`, so `ν = 2` and the generalized 0-eigenspace has
  dimension 147.
* Certificate: `D = 64`; the parsed `W8L, W4L, W2L, W1L` (157 entries each) equal the recomputed
  `D (8 − S)^{-1} f` and the Vandermonde solution from `v_3, v_4, v_5`; the identities `S W8 + D f = 8 W8`,
  `S W4 = 4 W4`, `S W2 = 2 W2`, `S W1 = W1` hold; `S` rebuilt from the certificate's index lists
  (`panelImgP, panelImgQ, plaqImg`) equals `S` rebuilt from the phase-4 images.
* `D v_m = 8^m W8 + 4^m W4 + 2^m W2 + W1` holds exactly for `m = 2, 3, ..., 9` and **fails at m = 1**, in agreement
  with the general form (`ν = 2`). The Lean theorem `closed_form_all` proves it for `m ≥ 3` **[K]**; the
  computation shows the base case could be lowered to `m = 2`.
* Nonzero coordinates: `W8` 157, `W4` 25, `W2` 2 (types 50 and 98, both plaquette types), `W1` 65.
* Totals: `N_m = 18·8^m − 24·4^m + 6·2^m` (`D·N_m = 1152·8^m − 1536·4^m + 384·2^m + 0`);
  `lim N_m/8^m = 18`; limiting class frequencies `19/36, 13/144, 1/9, 23/144, 1/9` for `{+1}, {−1}, {±i}, {±j}, {±k}`;
  `v_7` class counts from the recursion `[19677945, 3325970, 4194300, 5963773, 4194300]`.

---

## 5. FR30-specific structure: the condensation of the type graphs   **[E]**

Directed type graph: `c → r` iff `M[r, c] > 0`. Strongly connected components (Tarjan), block spectra exact.

**Panel block `M` (49 types, 43 SCCs, 1 sink).**
* **No panel type is self-reproducing as a single type: no `c` has `M[c, c] = 4`** (self-loop histogram
  `{0: 41, 1: 8}`). The premise "report which panel types have `M[c,c] = 4`" is therefore answered: none.
* The unique **sink SCC** is the 7-type set `{0, 2, 5, 9, 14, 25, 42}`: an irreducible block with all column sums 4,
  rank 2, trace 5, characteristic polynomial `λ^5 (λ−4)(λ−1)`. Its structure: the types `{0, 5, 9, 14}` each
  produce one panel of each of `{0, 5, 14, 25}`, and the types `{2, 25, 42}` each produce `{2, 9, 9, 42}`; the
  quotient dynamics of the two sub-populations is `[[3, 2], [1, 2]]` with eigenvalues 4 and 1. So the fourth
  eigenvalue 1 of `M` is a non-Perron mode of the stable interface set (the mixing ratio of its two sub-populations
  relaxes with eigenvalue 1, i.e. a constant correction).
* Three **fixed-point singletons** with `M[c, c] = 1`: types `1, 3, 4` (each produces exactly one copy of itself and
  three panels of other types).
* 39 **transient singletons** (`M[c, c] = 0`, no cycle through them).
* Multiplicity bookkeeping: eigenvalue 4 ↔ 1 sink; eigenvalue 1 ↔ 3 fixed points + 1 from the sink block;
  `λ^44 = λ^39 (transients) · λ^5 (sink block)`.

**Plaquette block `B` (108 types, 107 SCCs, 1 sink).**
* Unique sink SCC `{1, 49}` with block `[[1, 1], [1, 1]]` (rank 1, charpoly `λ(λ−2)`): two plaquette types that each
  produce one copy of each. No `B[c, c] = 2` exists.
* Four fixed-point singletons (`B[c, c] = 1`): types `0, 4, 5, 11`; 102 transient singletons.

**Geometric meaning.** A sink SCC is an inflation-closed set of interface types: once an interface of one of these
types exists, all its descendants stay in the set forever; these are the *stable interfaces*, and the multiplicity
of `L^{d-1}` (resp. `L^{d-2}`) counts the stable panel (resp. plaquette) families. A loop-1 singleton is an interface
type that persists as exactly one copy under inflation (its population is conserved, not multiplied); a transient
type never reproduces itself and is present only because the forcing term re-creates it inside every freshly
inflated tile and because other types produce it. In FR30 the stable interface is not a fixed type but a 7-type set
whose internal composition converges with a constant (eigenvalue-1) correction. The Phase 5 phrase "interface types
reaching fixed points after a bounded transient" is accurate for the *set*, not for individual types.

---

## 6. Statement 5 — the clean-spectrum criterion (H6)   **[P, with the census E]**

**Definitions.** Let `M ≥ 0` be an integer matrix with constant column sums `K ≥ 2`. The spectrum is *clean* if
`spec(M) ⊆ {0, 1, K}`. For an SCC `C`, `M_C` is the principal submatrix; `C` is a *sink* if no edge leaves it, i.e.
iff all column sums of `M_C` equal `K`.

**Theorem (clean-spectrum criterion).** `spec(M) ⊆ {0, 1, K}` **if and only if**
(i) every non-sink SCC is a single node with self-loop weight 0 or 1, and
(ii) every sink SCC has non-Perron spectrum contained in `{0, 1}`, i.e. `charpoly(M_C) = λ^a (λ−1)^b (λ−K)`.
Moreover, unconditionally, `mult_M(K) = number of sink SCCs ≥ 1`, and `K` is a simple root of every sink block.

**Corollaries for sink blocks.** A sink block of rank 1 is always clean (spectrum `{K, 0}`); a sink block of rank 2
is clean iff its trace is `K` or `K + 1` (its second nonzero eigenvalue is `trace − K`). A sink that is a single
node (`M[c, c] = K`) is clean. The theorem holds verbatim for `B` with `K = L^{d-2}` and for
`S = [[M, 0], [A, B]]` since `spec S = spec M ∪ spec B`.

**Proof.** Order the SCCs topologically; `M` becomes block lower triangular with the `M_C` on the diagonal, so
`charpoly(M) = Π_C charpoly(M_C)` and `spec(M) = ∪_C spec(M_C)`. Perron–Frobenius facts for an irreducible
nonnegative matrix `T` (size ≥ 2): (PF1) `min colsum ≤ ρ(T) ≤ max colsum`, with equality on either side iff all
column sums are equal; (PF2) `ρ(T)` is a simple eigenvalue; (PF3) the eigenvalues of modulus `ρ(T)` are
`ρ(T)·(h-th roots of unity)`, `h` the period.
*Sinks.* If `C` is a sink, `M_C` has all column sums `K`, so `ρ(M_C) = K` (`1^T M_C = K 1^T`) and `K` is simple
(PF2; trivial if `|C| = 1`). Hence each sink contributes exactly one eigenvalue `K`, and (ii) is by definition the
condition that the rest of its spectrum lies in `{0, 1}`.
*Non-sinks.* If `|C| = 1`, `M_C = [s]` with `0 ≤ s ≤ K − 1` (some child leaves `C`), clean iff `s ∈ {0, 1}`. If
`|C| ≥ 2`, `M_C` is irreducible with every column sum ≥ 1 (irreducibility) and ≤ K, not all equal to `K`. If the
column sums are not all equal, (PF1) gives `1 ≤ min < ρ(M_C) < max ≤ K`, so `ρ(M_C) ∉ {0, 1, K}`: not clean. If they
are all equal to `s`, then `ρ(M_C) = s ∈ {1, ..., K−1}`; `s ≥ 2` is not clean; `s = 1` forces every column to have a
single entry 1, and since `ρ(M_C^T) = 1` as well with every row sum ≥ 1, every row has a single entry 1 (PF1 applied
to `M_C^T`), so `M_C` is a permutation matrix, irreducible, hence a single cycle of length `|C| ≥ 2` with
`charpoly = λ^{|C|} − 1`, whose roots include a non-trivial root of unity: not clean. So a non-sink SCC is clean iff
(i). In particular no non-sink SCC has `K` as an eigenvalue (`ρ(M_C) < K`), which gives `mult_M(K) = #sinks`.
Combining: `M` is clean iff every block is clean iff (i) and (ii). The rank corollaries follow because a rank-`r`
block has at most `r` nonzero eigenvalues, one of which is `K`, and the trace is their sum. ∎

**Sharpness.** Clause (ii) cannot be replaced by a structural condition on the graph alone: the sink block of
random decoration #0 (21 types, all column sums 4) has non-Perron eigenvalues `2, 2, 1, 1, 1`, while the FR30 sink
block (7 types) has `1`; both are irreducible aperiodic blocks with constant column sums. Which non-Perron spectrum a
sink block has is a property of the integer matrix, decided by the finite computation `charpoly(M_C)`; the theorem
reduces cleanliness to this finite check plus the purely graph-theoretic clause (i).

**Census [E]** (`audit/results/phase5a_recursion_theorem_audit.txt`, Section 4; all iff-statements of the theorem
were checked block by block on every SCC, and `charpoly = Π charpoly(M_C)` was verified exactly in every case):

| decoration | block | types | SCCs | sinks (= mult of K) | non-clean factors and their origin | clean |
|---|---|---|---|---|---|---|
| FR30 | M | 49 | 43 | 1 (7-type block, rank 2, `λ^5(λ−4)(λ−1)`) | none | yes |
| FR30 | B | 108 | 107 | 1 (`[[1,1],[1,1]]`) | none | yes |
| achiral (`D_s` only) | M | 51 | 42 | 3 (three 4-type blocks, each rank 1, `λ^3(λ−4)`) + 3 loop-1 singletons | none | yes |
| achiral | B | 117 | 114 | 3 (three 2-blocks `λ(λ−2)`) + 3 loop-1 | none | yes |
| random #0 | M | 81 | 55 | 1 (21-type block `λ^15(λ−4)(λ−2)²(λ−1)³`) | `(λ−2)²` from the sink block (clause ii fails); `(λ²+λ+1)³` from three 3-cycles `{3,4,5}, {7,8,10}, {11,12,14}` (clause i fails) | no |
| random #0 | B | 234 | 220 | 4 (two 4-blocks `λ^3(λ−2)`, two 2-blocks `λ(λ−2)`) + 9 loop-1 | `(λ²+λ+1)³` from three 3-cycles | no |
| random #1 | M | 81 | 57 | 1 (9-type block `λ^6(λ−4)(λ²+λ−4)`) | `λ²+λ−4` (roots `(−1±√17)/2`) from the sink block; `(λ²+λ+1)³` from three 3-cycles; `λ³−2λ²−7λ+6` from an **irreducible non-sink block of 11 types** with column sums `[4,4,3,4,3,4,4,3,3,4,3]` | no |
| random #1 | B | 266 | 219 | 7 (six 6-blocks `λ^4(λ−2)(λ+1)`, one 12-block `λ^9(λ−2)(λ+1)²`) | `(λ+1)^8` from the seven sink blocks (period-2 non-Perron modes); `(λ²+λ+1)³` from three 3-cycles | no |

Random decoration permutations (seed 2026 stream): #0 `{'0': (2,0,1), (0,0,0): (0,1,2), (0,0,1): (0,2,1), (0,1,0): (1,0,2), (0,1,1): (1,2,0), (1,0,0): (1,0,2), (1,0,1): (0,1,2), (1,1,0): (1,2,0)}`;
#1 `{'0': (1,2,0), (0,0,0): (1,2,0), (0,0,1): (2,1,0), (0,1,0): (2,1,0), (0,1,1): (2,0,1), (1,0,0): (2,1,0), (1,0,1): (2,0,1), (1,1,0): (0,1,2)}`.
Their characteristic polynomials and limiting frequencies coincide with decorations #0 and #1 of
`audit/results/phase5_universality_types.txt` **[prior]**; the universality engine's `M, B` for FR30 were checked to be
identical to the phase-4 rebuilt `M, B`.

**Answer to the question "do non-clean spectra always come from cycles of length ≥ 2 or from irreducible blocks of
size ≥ 2?"** In the four decorations analysed, yes: every non-clean factor originates in an SCC of size ≥ 2 — a
3-cycle (`λ²+λ+1`, period-3 oscillation of finite-size counts), an irreducible non-sink block (random #1, size 11,
Perron root ≈ 3.41 strictly between 1 and 4), or a sink block with a non-Perron eigenvalue outside `{0, 1}` (`2`,
`−1`, `(−1±√17)/2`). No singleton with self-loop weight 2 or 3 occurred (self-loop weights in all four decorations
are in `{0, 1}`). By the theorem, however, such a singleton would also be non-clean, so "always" is an empirical
observation on this sample, not a theorem. In the achiral decoration the three stable interface families are
rank-1 blocks (spectrum `{4, 0}`), the cleanest possible case; FR30's single stable family is rank 2 with trace
`K + 1 = 5`, the only other clean possibility for rank 2.

**Geometry versus decoration.** Forced by the geometry (any exact block substitution, all admissible chair
decorations): finiteness of types; the column sums `4, 4, 2`; the eigenvalue `8` of the forcing and the presence of
`4` and `2` with multiplicity = number of stable families ≥ 1; rationality; the exact finite-size expansion in
powers of the eigenvalues; `O(2^{-m})` relative surface corrections. For the chair specifically the cube partition
of `T_m` is the same for every admissible decoration (the chair's cube set `{0,1}^3 \ {(1,1,1)}` is invariant under
coordinate permutations, and admissible frames differ from `D_s(v)` only by permutations), which is why
`48, 60`, `N_m = 18·8^m − 24·4^m + 6·2^m` and the surface-to-volume law are decoration-independent, as the Phase 5
census observed **[prior]**. Caused by the decoration: the condensation structure (number and rank of stable
families, loop-1 types, cycles, non-sink blocks), hence cleanliness, the specific limiting frequencies, and the
denominator `D`. The `Q_8` link rule plays no role in the spectrum: types are defined by relative poses alone and the
holonomy class is a function on types, so **every** `Γ`-invariant local observable (not only the gauge-invariant
holonomy class) inherits the same recursion and the same spectrum; the decoration determines the spectrum through
the type graph and the flux through the class function, separately.

---

## 7. Statement 6 — general-class statements and the counterexamples that bound them   **[P + E]**

| statement | hypotheses | status | refuted without the hypothesis by |
|---|---|---|---|
| G1 exact finite-state linear recursion for type counts | finite local complexity modulo a group under which the observable is invariant (H1–H2; more generally any substitution with finitely many collared types) | [P] (Statement 1) | pinwheel-type irrational rotations (infinitely many types; not computed here) |
| G2 normalized limits exist, seed-independent | forcing eigenvalue `λ > ρ(S)` | [P] (Statement 2) | (b) `a→aa, b→bb`: homogeneous, non-primitive — limit exists but depends on the seed |
| G3 rational limits | G2 + integer `S`, integer `λ` (constant length / integer expansion) | [P] (Statement 3) | (a) Fibonacci: finite type, exact recursion, primitive, frequencies `1/φ, 1/φ²` irrational |
| G4 exact finite-size formula `Σ μ^m w_μ` for `m ≥ ν` | G3; semisimple nonzero part (else polynomial factors) | [P] (Statement 4) | (d) period-doubling: still exact, but with an oscillating `(−1)^n` term — exactness does not need cleanliness |
| G5 clean spectrum `⊆ {0,1,K}` | criterion (i)+(ii) of the Theorem, a property of the decoration | [P] (Statement 5) | (c) Thue–Morse: letter spectrum `{2, 0}` clean, 2-block spectrum `{2, 1, −1, 0}` not clean — cleanliness is not inherited from tiles to collared (interface) types; (d) `0→01, 1→00`: constant length + primitive, spectrum `{2, −1}` |
| G6 monotone (non-oscillating) finite-size corrections with pure powers of `L` | G5 | [P] (consequence of Statement 4 + 5) | random decorations #0, #1: `λ²+λ+1` (period 3), `λ+1` (period 2) |

Counterexample details [E] (`audit/results/phase5a_counterexamples.txt`):
(a) `Mat = [[1,1],[1,0]]`, `charpoly λ² − λ − 1`; (b) `Mat = 2I`, `charpoly (λ−2)²`, not primitive;
(c) 2-block alphabet `00, 01, 10, 11`, induced rule `00→(01,10), 01→(01,11), 10→(10,00), 11→(10,01)`, matrix
`[[0,0,1,0],[1,1,0,1],[1,0,1,1],[0,1,0,0]]`, `charpoly λ(λ−2)(λ−1)(λ+1)`, semisimple, frequencies `1/6, 1/3, 1/3, 1/6`
(empirical on `σ^14(0)`: `910/5461, 1/3, 1/3, 2731/16383`); (d) `Mat = [[1,2],[1,0]]`, `charpoly (λ−2)(λ+1)`,
`v_n = P diag(2^n, (−1)^n) P^{-1} v_0` equals the direct counts for `n = 0..6`, coefficients `(−1/3, 1/3)`.

The Thue–Morse example is the exact analogue of the FR30 situation: the tile-level substitution matrix of the chair
(one prototile up to `Γ`, 8 children) is trivially clean, and whether the induced operator on *interfaces* (panels,
plaquettes) is clean is a separate question with a decoration-dependent answer.

---

## 8. Outcome per target and remaining proof obligations

| item | outcome |
|---|---|
| Exact finite-state recursion (Statement 1) | **proved theorem** (paper proof) + exact verification `m ≤ 4` + kernel check of class counts `m ≤ 2` |
| Existence of limits (Statement 2), rationality (Statement 3), finite-size formula (Statement 4) | **proved theorems** under the stated hypotheses; FR30 instance exact [E] and kernel-checked for `m ≥ 3` [K] |
| FR30 spectrum, semisimplicity, nilpotency 2, `D = 64`, `W` vectors, `N_m`, frequencies | **verified exactly** [E], consistent with [K] |
| Clean-spectrum criterion (H6) | **proved theorem** (condensation criterion, Statement 5); the census confirms every clause on 4 decorations |
| A closed-form criterion in terms of the 8 permutations of a decoration | **unresolved**: the theorem reduces cleanliness to a finite condensation check, but no formula predicting the condensation from the permutation data is known; the Phase 5 census [prior] shows it is not controlled by the contact-language size |
| Counterexamples (a)–(d) | **exact** [E] |

Remaining proof obligations (precise):
1. Formalize the parity trichotomy (Statement 1) for all `m` in Lean; currently paper + exact check for `m ≤ 4`.
2. Lower the Lean base case of `closed_form_all` from `m = 3` to `m = 2` (the computation shows it holds; `ν = 2`).
3. Prove or refute: for admissible chair decorations, every non-sink SCC of `M` has size 1 or is a 3-cycle (observed
   in 3 of 4 decorations; refuted as a general statement by the 11-type non-sink block of random #1 — so the open
   question is the classification of the non-sink blocks that can occur).
4. Characterize which sink blocks occur (observed: ranks 1 and 2 for clean decorations; non-Perron eigenvalues
   `2`, `−1`, `(−1±√17)/2` for non-clean ones) in terms of the decoration — unresolved.
5. The unit-cube periodic control and the full `|P_0|` census are quoted from Phase 5 [prior] and were not recomputed
   in this session.
