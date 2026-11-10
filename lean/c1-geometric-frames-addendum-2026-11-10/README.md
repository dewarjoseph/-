# Geometric frames addendum to the C1 Lean-chain public copy (2026-11-10)

**Public addendum** to the C1 Lean-chain public copy at `lean/c1-lean-chain-2026-11-10/` (MANIFEST sha256 62342986cfd8410689b7fde41fada69752e9fc4aeff095c7286e22a3ebe18a56).

This folder is a public addendum to the C1 Lean-chain public copy (the folder `lean/c1-lean-chain-2026-11-10/`, whose MANIFEST sha256 is 62342986cfd8410689b7fde41fada69752e9fc4aeff095c7286e22a3ebe18a56). It adds one scratch Lean module, `IcosahedralFramesGeometric_v2_2026-11-10.lean`, which imports the table-driven I ≅ A5 module already in that copy and defines the five frames from the icosahedron's vertices. It is not a Lake package. Clean rebuilds of the original version-2 frames source and of earlier public copies of it, against the three dependency modules from the C1 Lean-chain public copy, exited 0 with empty standard error; the emitted output is byte-identical to the recorded build text listed under Build instructions. A clean rebuild of the copy in this folder (67c898ed…) against the same three dependency modules exited 0 with empty standard error; the emitted output is byte-identical to 0175eef9…. The official real-vertex-set frames source cited below (src 2e84adfe…, raw b9c6d8ce…) is not in this folder and has not been rebuilt from this folder. The files themselves are not a Lake target. No licence is granted or implied. The C1 Lean-chain public copy is not edited by this folder.

## Labels

[P] proved, [C] computed or certified, [E] evidence, [X] conjecture, [A] analogy, [F] falsified.

A paper label may be weaker than its source, never stronger.

Each statement below marked [P, Lean, scratch, not peer reviewed] is scoped exactly to its own wording. The I ≅ A5 and C1 labels are unchanged. The isomorphism remains defined by the table.

## Public wording

The C1 Lean-chain public copy's I ≅ A5 paragraph (README and NOTES) currently ends the table-driven sentence with the clause "but the frames are not defined geometrically in Lean." That clause is not edited there. In this addendum only, it is superseded by the following adopted replacement:

; a separate scratch Lean file (src 4970f35c…, raw 0175eef9…) defines the five frames from the icosahedron's vertices, over the doubled-scale ℤ[√5] model, as sets of pairwise orthogonal-or-parallel edge-midpoint vectors that partition all 30 edge-midpoint vectors, proves each table entry is the frame the corresponding scaled rotation carries frame i onto, and transports this to ℝ: the five real image frames are distinct, and every element g of the imported official group maps the real image of frame i onto the real image of frame σ(g)(i), where σ is the isomorphism [P, Lean, scratch, not peer reviewed]. The isomorphism itself is still defined by the table; the frame labels are chosen representatives; orthogonality is not restated over ℝ; '2-fold axis' and 'inscribed cube' are not proved notions there.

The source and recorded-build hashes in that sentence are those of version 2 of the frames file (original src 4970f35c0a3cf2dbc0276d1e73c6dad64ebbde9e96e8c41e0477a53c0e3f842d, recorded build text 0175eef93a3264ec2f293b0668de6bd7921a4bdf152bc36e9a4f9453362c7e9d). This folder contains a comment-redacted copy of that version 2 file. Version 2 keeps the version-1 theorems, softens comments and docstrings, and adds `halveToReal_injective`, `frameRep_mem_frame_eq` and `realFrame_injective` (the five real image frames are distinct). The adopted sentence includes that distinctness and the caveat that orthogonality is not restated over ℝ.

### Official real-vertex-set frames

The following statements concern the official real-vertex-set frames file (src 2e84adfe…, raw b9c6d8ce…). That source is not in this folder and has not been rebuilt from this folder.

In a scratch Lean file (src 2e84adfe…, raw b9c6d8ce…), the edge vectors u+w of the imported official icosahedron vertex set (vertex pairs at squared distance 4, the least nonzero squared distance) and five frames of them, labelled by chosen golden-ratio representatives, are defined directly on the official real vertex set; there are 30 edge vectors, nonzero and closed under negation; each frame has 6 vectors, is closed under negation and is pairwise orthogonal-or-parallel; the five frames are distinct and pairwise disjoint, partition the 30 edge vectors, and every orthogonal pair or triple of edge vectors lies in a single frame [P, Lean, scratch, not peer reviewed]. These real facts are proved by a proved transfer from the ℤ[√5] model.

Every element g of the imported official group maps frame i onto frame σ(g)(i), and σ(g)(i) is the only frame that g maps frame i into, where σ is the isomorphism to A5, which is still defined by the table (src 2e84adfe…, raw b9c6d8ce…) [P, Lean, scratch, not peer reviewed].

### Involutions, sign-pairs and face-sum sets

The sentences cite the scratch Lean file IcosahedralCubesInvolutions_v2_2026-11-10.lean (src 340f8204…, raw 4abd202a…), which imports the involutions file (src 70c3e9f0…, raw d88d2eff…) and the official real-vertex-set frames file (src 2e84adfe…, raw b9c6d8ce…). It is not in this folder and has not been rebuilt from this folder.

"In the imported official icosahedral group there are exactly 15 elements g ≠ 1 with g·g = 1 (Nat.card); each fixes some official edge vector, any two official edge vectors it fixes agree up to sign, and two such elements fixing the same official edge vector are equal, so they correspond bijectively to the 15 pairs {p, −p} of official edge vectors, each g fixing both points of its pair (src 340f8204…, raw 4abd202a…) [P, Lean, scratch, not peer reviewed]. Lean does not prove that g fixes exactly the line through p, that these pairs are distinct one-dimensional subspaces, or anything about g on p⊥."

"Among the 20 official face sums u+v+w (official vertices at pairwise squared distance 4), the 8-point sets whose pairwise squared distances all lie in {s, 2s, 3s} for some s are exactly five, namely officialCube i := the face sums with equal squared projections onto every vector of officialFrame i; any two points of officialCube i at squared distance 14+6√5 differ by a vector parallel to a vector of officialFrame i (src 340f8204…, raw 4abd202a…) [P, Lean, scratch, not peer reviewed]. 'Cube' here names the {s, 2s, 3s} test; Lean does not prove these sets are cubes, that they are inscribed in any solid, or that the group permutes them."

## Files

| File | Role | sha256 of the copy in this folder |
|---|---|---|
| `IcosahedralFramesGeometric_v2_2026-11-10.lean` | Geometric frames for the I ≅ A5 table, version 2. Comments redacted; comment-stripped code is byte-identical to the original. | 67c898ed267e0abc91c688cedfcb6b33cf1f5bf5400ac257d76ce700fba2d60f |
| `README.md` | This file. | (see SHA256SUMS) |
| `SHA256SUMS` | sha256 of every file in this folder except `SHA256SUMS` and `MANIFEST`. | (see MANIFEST) |
| `MANIFEST` | List of files and sha256, including `SHA256SUMS`. | not listed inside this file |

This README is a new public file. Its hash is in `SHA256SUMS` and `MANIFEST`.

## Depends on

This module has a single import:

`import «IcosahedralRotationGroupIsoAlternatingFive_v2_2026-11-10»`

That name matches the filename of the table-driven I ≅ A5 module in the C1 Lean-chain public copy. The rest of the chain, and Mathlib, are imported through that module. This folder does not repeat those files. The copies to use, with sha256 of the copies in that public-copy folder (MANIFEST 62342986cfd8410689b7fde41fada69752e9fc4aeff095c7286e22a3ebe18a56), are:

- `IcosahedralRotationGroupIsoAlternatingFive_v2_2026-11-10.lean`: 37faea30eb0caccd3712fe3cd7f54b620ee862b6e6b3b9380adfb0bf15b86278
- `IcosahedralRotationGroupImportedMulEquiv_2026-11-10.lean`: 72424b02c07958f7ec5f6827c215c5f51cdd05381287b96fe2481dd0153b5c90
- `IcosahedralRotationGroup_2026-11-09.lean`: fe54b0312e751037ca217ab7e84657c4e0e8b230051bfc818b954184efd597c9

The simplicity module in that copy is not imported here.

## Build instructions

Toolchain recorded for the official chain and for the clean rebuild of the C1 Lean-chain public copy: Lean 4 v4.36.0-rc2, Mathlib v4.36.0-rc2 at git 9d581dfff2e41de989072ea63abf3daf69311520.

A clean rebuild of an earlier public copy of this file, against the three dependency modules from the C1 Lean-chain public copy on the Lean module search path together with Mathlib, exited 0 with empty standard error. The emitted output is byte-identical to 0175eef93a3264ec2f293b0668de6bd7921a4bdf152bc36e9a4f9453362c7e9d (15 `#print axioms` lines, each depending on `propext`, `Classical.choice` and `Quot.sound` only). A clean rebuild of the original, unredacted version-2 source likewise exited 0 with empty standard error and emitted the same output. Compiled artifacts of this comment-redacted copy can differ in compiled-module bytes from the original; the emitted output remains identical to that pin. That rebuild is not a Lake build. This file is not a Lake target. Recorded build texts and compiled artifacts are omitted.

A clean rebuild of the copy in this folder (67c898ed…) against the same three dependency modules exited 0 with empty standard error; the emitted output is byte-identical to 0175eef9….

To repeat the command-line rebuild, once the three dependency modules from the C1 Lean-chain public copy are on the Lean module search path together with this file and Mathlib, compile in dependency order: the official module, the imported multiplicative equivalence, the table-driven I ≅ A5 module, then this file. This folder is not a Lake target. Recorded build texts and compiled artifacts are omitted.

## Provenance

Original unredacted source: `IcosahedralFramesGeometric_v2_2026-11-10.lean`, sha256 4970f35c0a3cf2dbc0276d1e73c6dad64ebbde9e96e8c41e0477a53c0e3f842d (15802 B). Recorded build text of that original: 0175eef93a3264ec2f293b0668de6bd7921a4bdf152bc36e9a4f9453362c7e9d.

The copy in this folder differs only in comments and docstrings, as recorded below. Comment-stripped code is byte-identical to the original. Public copy: 67c898ed267e0abc91c688cedfcb6b33cf1f5bf5400ac257d76ce700fba2d60f (15869 B).

Edits (comments and docstrings only; the import line is unchanged):

1. Opening block comment. Internal identifiers and a compiled-module recipe sentence were dropped. An internal piece label was replaced with "the listed vertices". A parenthetical after a count was dropped. A classical-solid phrasing was replaced with "no classical solid claimed". The three added lemmas are named.
2. `frame` docstring. The classical-correspondence sentence was replaced with "A classical solid correspondence is not stated or proved in Lean."
3. `frameRep` docstring. A parenthetical naming internal checks after "outside comparison" was dropped. An outside attribution before "script order" was replaced with "the", so the docstring now reads "the script order".
4. Opening block comment and the `frame`, `edgeSums_orthogonal_count` and `orthogonal_edgeSums_same_frame` docstrings. Counts and descriptions of edge sums were reworded in terms of sign-pairs ±x and of 6 vectors, closed under negation, pairwise orthogonal or parallel.
5. Opening block comment, `frame` docstring and the edges section heading. The two comments that repeated the phrase from edit 4 were shortened so it appears once: "Each frame has 6 vectors, closed under negation, pairwise orthogonal or parallel." and "each is 6 vectors, closed under negation, pairwise orthogonal or parallel: the edge sums `±m₁, ±m₂, ±m₃`." The edges section heading now reads "Edges and edge-sum vectors".

The `edgeSums` docstring keeps one informal name for an edge sum, marked there as a name only; no order-2 rotation statement is proved.

## Not in this folder

The C1 Lean-chain public-copy modules themselves, working notes, recorded build texts, version 1 of this frames file, the official real-vertex-set frames source (src 2e84adfe…), the involutions source (src 70c3e9f0…), the face-sum-sets source (this version, src 340f8204…), and any compiled artifacts are omitted on purpose. Frozen preprint files are not modified by this folder. The C1 Lean-chain public copy is not modified by this folder.
