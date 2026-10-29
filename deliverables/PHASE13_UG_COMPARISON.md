# Phase XIII, part 2 — The Unique Games proof (openai/math) set against this programme's own work

**What was compared.**
- *The proof:* `preprints/The-Unique-Games-Theorem-September-23-2026/build/sections/*.tex` (openai/math 7ef5c0c), read as data and not refereed. Its result is cited as **claimed**.
- *The programme's own work* reachable from this session, leaving out the openai/math mathematics:
  - this repository: Chair44 Phases I–XII; Pillar 10, `deliverables/pillar10_p_vs_np_clifford_complexity.tex`; and `certificates/PvsNPCliffordCertificates.lean`, 14 533 lines, 440 `#print axioms` checks, 508 theorems, no `sorry`, not compiled here;
  - the GitHub copy of `QIS`, last pushed 21 August 2026.
- *Not reachable:* the local folders `C:\Users\super\git\p_vs_np_repo` and `QIS`. They are not on GitHub and not shared with this session (Remote Control serves only Mac or Linux folders). Files cited from them, such as `p_vs_np_repo/proofs/Max3SAT_Cycle_Space_Gauge.lean` (named in the Pillar 10 Lean file), were not seen.
- *Searches.* `QIS` contains nothing on unique games, label cover, SDP or frustration. The searches in this repository found Pillar 10 and the Phase XII §15 material.

**Labels.**
- [P] proved;
- [C] computed exactly or to rounding level;
- [A] analogy only: a shared shape, no shared mathematics.

---

## 1. The proof in one paragraph

- **The claim.** For fixed ε, δ there is a polynomial reduction from 3SAT to *translation* unique games over K = 𝔽₂ˢ, i.e. constraints a(v) = a(u) + c_e, with value ≥ 1 − ε or ≤ δ.
- **The starting point** is Håstad's gap for nearly satisfiable parity (3LIN) equations.
- **The tables** are affine maps into a binary space 𝒱 ⊃ K.
- **The "latent alphabet" gadget** is a nonlinear map C : 𝒱 → K that is translation-equivariant, C(x+h) = C(x) + h for h ∈ K. It is stable under a special noise law μ, while every high-rank family of linear observations detects that noise.
- **Folding.** The answers are folded: the constant K-translates of a table form one vertex.
- **The test** checks equality under rank-one matrix updates (the degree-two matrix shortcode of Barak–Kothari–Steurer).
- **Soundness.**
  - Fourier analysis over 𝔽₂ characters forces low-rank Fourier mass.
  - The inverse shortcode theorem, from Khot–Minzer–Safra Grassmann expansion, gives structured agreement.
  - "Clean coordinates" and the Dinur–Steurer parallel-repetition bound give the contradiction.

---

## 2. Where the two genuinely meet

### 2.1 They study the same object: a group-valued connection on a graph, and how close it is to a coboundary [P]

- **The dictionary.** A unique game whose permutations are a group action is a connection with values in that group.
  - A labelling is a section.
  - The game is satisfiable exactly when the connection is a coboundary, c_e = s(v)s(u)⁻¹ (translations: c_e = a(v) − a(u)).
  - This is Phase XII Proposition 15.1's dictionary, and it is Pillar 10 Theorem 1.1(1).
- **Exact satisfiability is easy for every group.** Your own Lean theorem `universal_spanning_tree_coboundary_iff` proves that whether a *fixed* connection is a coboundary is decided by one spanning-tree propagation, over any group, abelian or not.
- **Approximate satisfiability is hard, already for abelian groups.** The Unique Games Theorem concerns whether a connection is *close* to a coboundary (a section violating ≤ ε of the edges, against none violating fewer than 1 − δ). Its instances are translation games over 𝔽₂ˢ, which are abelian.
- **Consequence for Pillar 10's framing** ("Tractable P vs non-abelian Q₈ frustration").
  - The line between tractable and hard does not run between trivial and non-abelian holonomy. It runs between *exact* and *approximate*.
  - A frustrated Q₈ connection, however non-abelian, is simply unsatisfiable, and that is detected in linear time.
  - Non-abelian frustration is not needed for hardness: abelian translation constraints suffice (Håstad's 3LIN gap already showed this for parity; the Unique Games Theorem extends it to near-perfect completeness).
- **What stays correct.** The no-go "no vertex gauge transformation removes the holonomy of a cycle" is true: holonomy changes by conjugation. That fact is what makes the exact problem easy, not hard.

### 2.2 The Chair44 operator is one representation block of the game's label-extended graph [C]

`audit/phase13_ug_label_extended.py` → `phase13_ug_label_extended.json`

- **Setup.** The label-extended graph of the Chair44 Q₈ game has vertices (tile, g ∈ Q₈) and edges (b, g) — (a, U g). It is the graph that spectral unique-games algorithms work with (Kolla; Arora–Barak–Steurer).
- **The decomposition.** Its adjacency is the connection in the left-regular representation of Q₈, which splits as trivial + three one-dimensional characters + twice the spinor. Exactly:

  spec(24 − A_ext) = spec(plain graph) ∪ spec(three ℤ₂ shadows) ∪ spec(quaternion form of H).

- **Checked** on T₂ and T₃ of 1387, 539311 and 4752 (dimensions 512 and 4 096): the largest difference is 3.8·10⁻¹³.

| rule | L | trivial | χ_i | χ_j | χ_k | spinor (Chair44 bottom Y_L) |
|---|---|---|---|---|---|---|
| 1387 | 3 | 1.6695 | 8.8720 | 9.1512 | 6.7677 | 9.9559 |
| 539311 | 3 | 1.6695 | 6.7570 | 8.8762 | 9.0461 | 9.9573 |
| FR30 (4752) | 3 | 1.6695 | 6.7713 | 9.2540 | 9.2540 | 9.3785 |

- **Meaning.**
  - The floor maximised in Phases X–XII is the floor of the **faithful (spinor) block** of the game.
  - The three shadows (Phase XII §15) are the other non-trivial blocks.
  - On these supertiles, the bottom of the label-extended graph, which is what spectral unique-games methods inspect first, comes from the trivial and shadow blocks, not from the spinor block.

### 2.3 The abelian quotient of a Chair44 game is a Unique-Games-Theorem instance [P] + [C]

- **The quotient.** Q₈/{±1} ≅ 𝔽₂². Reducing each link modulo the centre turns a Chair44 game into a translation game over K = 𝔽₂², exactly the theorem's instance format with s = 2. Its characters are the three shadows.
- **The centre.** The central sign ±1 is what the quotient forgets. Pillar 10's "central ℤ₂ frustration, W = −I" is holonomy lying in the kernel of this quotient.
- **The computation.** For every computed supertile, the quotient game is **not** a coboundary: Chair44 is frustrated even after the central sign is forgotten. A spanning-tree section violates 285–297 of 576 panels (T₂) and 2 842–2 898 of 5 376 (T₃).
  - These counts are upper bounds on the minimum.
  - Computing that minimum is the approximate problem the theorem says is hard in general. For these particular structured instances, nothing is claimed.

### 2.4 Parity is the common starting point [P]

- **In the proof:** the reduction starts from Håstad's nearly satisfiable 3LIN gap.
- **In Pillar 10:** `xor3_parity_extraction_and_hastad_floor_certified` splits the 8-clause 3-cube into two 3-XOR blocks, and checks that each 3-clause is satisfied by 7 of 8 assignments.
  - That certifies the random-assignment ratio 7/8, which is the *threshold* in Håstad's Max-3SAT theorem. It does not certify the hardness theorem itself.
  - The name is apt, provided it is read that way.
- **The Tseitin results** (`universal_resolution_vs_f2_polynomial_calculus_exponential_separation`) show exact parity systems are easy for 𝔽₂ linear algebra but hard for resolution. That is consistent with §2.1: exact parity is easy algebraically, approximate parity is hard.

---

## 3. Analogies only [A]

- **Folding and gauge quotients.**
  - The proof folds K-translates into one vertex, which makes answers equivariant, C(x+h) = C(x)+h.
  - Phase XII's Orbit Lemma studies global gauge transformations, σ_{dQ} = ρ_Q∘σ_d.
  - Both quotient by a global symmetry so that it acts on answers; the mathematics is not shared.
- **Rank certificates.**
  - Pillar 10's Spin(4) Gram rank certificate (det = 21 414 742) and the proof's rank-threshold detection both use the rank of a family of linear observations over a field.
  - They play different roles: one certifies an obstruction, the other separates a noise law from uniform.
- **Local-to-global.**
  - The proof turns local test statistics into global structure, via expansion and parallel repetition.
  - The Phase XII support principle and IMS certificates turn local eigenvalues into a global floor.
  - The shape is the same; the tools are not.

## 4. No counterpart in the programme's work

- **In the proof but not in the programme:** Grassmann expansion, the matrix shortcode, the latent gadget, parallel repetition and clean coordinates.
- **In the programme but not in the proof:** the substitution hierarchies, IMS localisation, and the HONHSE solver.
  - The HONHSE solver acts on the full 2ⁿ-dimensional hypercube.
  - The Unique Games Theorem, with Raghavendra's reduction (its §7, "Raghavendra's consequence"), implies that no polynomial-time classical algorithm beats the SDP approximation threshold for Max-k-CSPs unless P = NP. A claim of polynomial-time near-optimal solving for near-satisfiable instances would therefore contradict the theorem.
  - The HONHSE results, which use exponential state vectors, are consistent with it.

## 5. What could be taken from it

1. **Restate Pillar 10's dichotomy as exact vs approximate**, keeping its correct and formalised core: coboundary ⇔ the spanning-tree section works, for every group.
2. **Use the representation split (§2.2) as a tool.** Every Chair44 floor question is a question about one block of a structured unique game. The trivial and shadow blocks are where unique-games spectral methods look; the spinor block is where Chair44 lives.
3. **The 𝔽₂² quotient games of Chair44 are explicit, geometric instances of the theorem's format.** Their exact minimum frustration on Tᴸ is a well-posed, finite, and probably feasible computation (for example, an exact ILP at L = 2). It would give Chair44 a combinatorial counterpart to the spectral floor. That computation was not done here.
