# Notes on the icosahedral rotation group chain (public, 2026-11-10)

These notes record the mathematical content of the four Lean modules in this folder. They are derived from a development working note on the table-driven I ≅ A5 module (version 2). That working note is omitted, as working notes are not part of a public copy. This file is not a proof and not a build log.

Toolchain recorded for the original builds: Lean 4 v4.36.0-rc2, Mathlib v4.36.0-rc2 at git 9d581dfff2e41de989072ea63abf3daf69311520. A clean rebuild of the four modules from this folder alone, in dependency order, with Lean 4 v4.36.0-rc2, exited 0 on each module with empty standard error; the emitted outputs are byte-identical to the recorded build texts d76e67603a856894c2cbc774b5ffe2054d9c639f24ce4ae6a03d6a1a20c7e877, 063ea0f5ce5a4c8e8e9566fd787d30db274a37aa84d802b471c5146fdfac8a67, dc8609b86b28a1505a2ae5dca1fb70ba8bb9a0ef9af6e494a1a28d37abc4d31d and 0196b7345dbb3e52a7451c26d1f82da37e287b3032cd8996faaaf60df5d65e22. The retargeted simplicity import built under that rebuild. The axioms recorded for the simplicity module are `propext`, `Classical.choice` and `Quot.sound` only. The files themselves are not a Lake target.

## Official module (2026-11-09)

`IcosahedralRotationGroup_2026-11-09.lean` (sha256 fe54b0312e751037ca217ab7e84657c4e0e8b230051bfc818b954184efd597c9) defines `icosahedronVertexSet` as the usual twelve vertices (cyclic permutations of `(0, ±1, ±φ)` with `φ = Real.goldenRatio`) and `icosahedralRotationGroup` as the stabilizer of that set in `Matrix.specialOrthogonalGroup (Fin 3) ℝ`. It proves that the stabilizer is a subgroup. It does not prove that the vertex set has twelve elements, that the group has order 60, or that the group is isomorphic to `alternatingGroup (Fin 5)`. A historical sentence in its header, left unedited, records that those identifications were then unproved in Lean.

## Order 60 and the multiplicative transfer

`IcosahedralRotationGroupImportedMulEquiv_2026-11-10.lean` imports the official module. It lists sixty explicit scaled rotation matrices over `ℤ[√5]`, proves they are distinct, are scaled rotations, preserve the listed vertices, and are complete for that scaled stabilizer, and transfers them onto the official `SO(3, ℝ)` stabilizer. It constructs `scaledIcosahedralMulEquiv`, a multiplicative equivalence between the sixty and the official group, and shows that the official group has `Nat.card` 60.

The matrix-list body follows an earlier exact-arithmetic development, with one change: the real vertex set is the imported official definition rather than a second local copy. This file does not prove a homomorphism to `alternatingGroup (Fin 5)`.

## I ≅ A5, table-driven

`IcosahedralRotationGroupIsoAlternatingFive_v2_2026-11-10.lean` imports the file above. The map is table-driven. A 60-entry list of permutations of `Fin 5`, in the same order as the scaled matrices, was computed by the exact script `a5_exact_qsqrt5_v2.py` from the action on the five orthonormal triples of 2-fold axes. That geometric action is not defined or proved in Lean. `decide +kernel` re-checks that the table is multiplicative over all 60 × 60 products (in six chunks), that every entry is even, and that only the scaled identity maps to `1`. The resulting injective homomorphism `icosahedralRotationGroup →* alternatingGroup (Fin 5)` is bijective because `Nat.card` of each side is 60. The main declaration is

`icosahedralRotationGroupMulEquivAlternatingGroup : icosahedralRotationGroup ≃* alternatingGroup (Fin 5)`.

Version 2 changes only comments and docstrings, to this table-driven wording; the declarations are unchanged from the first version of the module. The recorded build text of the unredacted version-2 source is identical to that of the first version (sha256 dc8609b86b28a1505a2ae5dca1fb70ba8bb9a0ef9af6e494a1a28d37abc4d31d). The copy in this folder has a further public redaction of comments and therefore a different source hash. A clean rebuild of this folder's copy exited 0 with empty standard error, and its emitted output is byte-identical to that recorded build text.

The unchanged docstring of `frameHomA5` in that copy still says "The frame homomorphism"; the map is table-driven, as in the wording above.

## Simplicity (C1)

`IcosahedralRotationGroupIsSimple_2026-11-10.lean` proves

`icosahedralRotationGroup_isSimpleGroup : IsSimpleGroup icosahedralRotationGroup`

by transporting Mathlib's `alternatingGroup.isSimpleGroup` at `Fin 5` along `icosahedralRotationGroupMulEquivAlternatingGroup` (`MulEquiv.isSimpleGroup_congr`). This covers C1 only for the imported official 2026-11-09 definition. The five frames remain not defined geometrically in Lean. The formalisation is not a Lake target.

The copy in this folder imports the version-2 module (the original source imported the first version; the declarations of those two modules are the same). It has a public redaction of comments and therefore a different source hash. A clean rebuild of this folder's copy, including the retargeted import, exited 0 with empty standard error, and its emitted output is byte-identical to the recorded build text 0196b7345dbb3e52a7451c26d1f82da37e287b3032cd8996faaaf60df5d65e22. The axioms recorded for that module are `propext`, `Classical.choice` and `Quot.sound` only. This remains not a Lake target.

## Labels

Under the recorded rulings, I ≅ A5 and C1 are [P, Lean], scratch, not peer reviewed, with the table-driven caveat above. See README.md for the wording.

## How to quote

I ≅ A5. [P, Lean, scratch, not peer reviewed]: `icosahedralRotationGroup ≃* alternatingGroup (Fin 5)` on the imported official 2026-11-09 definition (src fe54b0312e751037ca217ab7e84657c4e0e8b230051bfc818b954184efd597c9), via a table-driven map of 60 permutations checked in-kernel; the table matches the five-frame action of `a5_exact_qsqrt5_v2.py`, but the frames are not defined geometrically in Lean. This rests on the scratch import chain in this folder; it is not a Lake target.

C1. [P, Lean, scratch, not peer reviewed]: `IsSimpleGroup icosahedralRotationGroup`, on the imported official 2026-11-09 SO(3, ℝ) stabilizer (src fe54b0312e751037ca217ab7e84657c4e0e8b230051bfc818b954184efd597c9), by transporting Mathlib's `alternatingGroup.isSimpleGroup` at Fin 5 along `icosahedralRotationGroupMulEquivAlternatingGroup` (`MulEquiv.isSimpleGroup_congr`). Rests on the scratch import chain; not a Lake target.
