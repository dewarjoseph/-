# Icosahedral rotation group: C1 Lean chain (public-copy candidate, 2026-11-10)

This folder is a public-copy candidate of four Lean modules that, together, identify the official 2026-11-09 icosahedral rotation group with the alternating group on five letters and prove that group is simple. It is staged only. It is not a Lake package. A clean rebuild of the four modules from this folder alone, in dependency order, with Lean 4 v4.36.0-rc2, exited 0 on each module with empty standard error; the emitted outputs are byte-identical to the recorded build texts listed under Build instructions. The files themselves are not a Lake target. No licence is granted or implied.

## Labels

[P] proved, [C] computed or certified, [E] evidence, [X] conjecture, [A] analogy, [F] falsified.

A paper label may be weaker than its source, never stronger.

Under recorded rulings dated 2026-11-10, the two claims below are [P, Lean], scratch, not peer reviewed. Frozen preprint text is unchanged by those rulings. Nothing in this folder is published by being staged here.

## Public wording

### I ≅ A5

[P, Lean, scratch, not peer reviewed]: `icosahedralRotationGroup ≃* alternatingGroup (Fin 5)` on the imported official 2026-11-09 definition (src fe54b0312e751037ca217ab7e84657c4e0e8b230051bfc818b954184efd597c9), via a table-driven map of 60 permutations checked in-kernel; the table matches the five-frame action of ToE's `a5_exact_qsqrt5_v2.py`, but the frames are not defined geometrically in Lean. This rests on the scratch import chain in this folder; it is not a Lake target.

Do not quote this as "given by its action on the five inscribed cubes". Use the table-driven wording above.

### C1 (I is simple)

[P, Lean, scratch, not peer reviewed]: `IsSimpleGroup icosahedralRotationGroup`, on the imported official 2026-11-09 SO(3, ℝ) stabilizer (src fe54b0312e751037ca217ab7e84657c4e0e8b230051bfc818b954184efd597c9), by transporting Mathlib's `alternatingGroup.isSimpleGroup` at Fin 5 along `icosahedralRotationGroupMulEquivAlternatingGroup` (`MulEquiv.isSimpleGroup_congr`). File `IcosahedralRotationGroupIsSimple_2026-11-10.lean`. The src and recorded build-text hashes in the adopted wording, `c0fdfc579fbcb755c94a01b18e2643d668e1ba78ecc8776cdb92aa1e769dc828` and `0196b7345dbb3e52a7451c26d1f82da37e287b3032cd8996faaaf60df5d65e22`, are those of the original unredacted source; the copy in this folder differs as recorded under Provenance below. This covers C1 only for that imported official definition. Rests on the scratch import chain; not a Lake target.

## Files

| File | Role | sha256 of the copy in this folder |
|---|---|---|
| `IcosahedralRotationGroup_2026-11-09.lean` | Official 2026-11-09 module: the `SO(3, ℝ)` vertex-set stabilizer. Byte-identical to the original (sha256 fe54b0312e751037ca217ab7e84657c4e0e8b230051bfc818b954184efd597c9, 4842 B). Its header still says that I ≅ A5 was then unproved in Lean (`[X]`); that sentence is historical to that file, superseded by the rulings' wording in this README, and was left unedited. | fe54b0312e751037ca217ab7e84657c4e0e8b230051bfc818b954184efd597c9 |
| `IcosahedralRotationGroupImportedMulEquiv_2026-11-10.lean` | Order 60, transfer onto the official group, and a multiplicative equivalence. Comments redacted; declarations unchanged. | 72424b02c07958f7ec5f6827c215c5f51cdd05381287b96fe2481dd0153b5c90 |
| `IcosahedralRotationGroupIsoAlternatingFive_v2_2026-11-10.lean` | Table-driven I ≅ A5 (version 2 wording). Comments redacted; declarations unchanged. | 37faea30eb0caccd3712fe3cd7f54b620ee862b6e6b3b9380adfb0bf15b86278 |
| `IcosahedralRotationGroupIsSimple_2026-11-10.lean` | C1: `IsSimpleGroup` of the official group, by transport. Comments redacted; one import retargeted as below; the theorem body is unchanged. | 17a2c2a05d1d640479485092b0249bd370084add488333ce1abfea216eb0ee21 |
| `NOTES.md` | Public-safe notes: statements, caveats, and toolchain pin. Substituted for a working note that is not included. | (see SHA256SUMS after this file is hashed) |
| `README.md` | This file. | (see SHA256SUMS) |
| `SHA256SUMS` | sha256 of every file in this folder except `SHA256SUMS` and `MANIFEST`. | (see MANIFEST) |
| `MANIFEST` | List of files and sha256, including `SHA256SUMS`. | reported with the staging note, not inside this file |

`NOTES.md` and this README are new public files. Their hashes are in `SHA256SUMS` and `MANIFEST`.

## How the modules import each other

1. The official module imports only Mathlib (`UnitaryGroup`, `GoldenRatio`, `VecNotation`).
2. `IcosahedralRotationGroupImportedMulEquiv_2026-11-10` imports `«IcosahedralRotationGroup_2026-11-09»`, plus Mathlib.
3. `IcosahedralRotationGroupIsoAlternatingFive_v2_2026-11-10` imports `«IcosahedralRotationGroupImportedMulEquiv_2026-11-10»` and Mathlib's `alternatingGroup`.
4. `IcosahedralRotationGroupIsSimple_2026-11-10` imports `«IcosahedralRotationGroupIsoAlternatingFive_v2_2026-11-10»` and Mathlib's `GroupTheory.SpecificGroups.Alternating.Simple`.

The quoted import names match the filenames in this directory. The original development compiled these modules with the Lean 4 command-line tool and a module search path, using those filename modules, and not as a registered Lake package. The copy of the simplicity file in this folder is retargeted at the version-2 isomorphism module (see Provenance).

## Build instructions

Toolchain recorded for the original builds: Lean 4 v4.36.0-rc2, Mathlib v4.36.0-rc2 at git 9d581dfff2e41de989072ea63abf3daf69311520.

A clean rebuild of the four modules from this folder alone, in the order below, with Lean 4 v4.36.0-rc2, exited 0 on each module with empty standard error. The emitted outputs are byte-identical to these recorded build texts:

- `IcosahedralRotationGroup_2026-11-09.lean`: d76e67603a856894c2cbc774b5ffe2054d9c639f24ce4ae6a03d6a1a20c7e877
- `IcosahedralRotationGroupImportedMulEquiv_2026-11-10.lean`: 063ea0f5ce5a4c8e8e9566fd787d30db274a37aa84d802b471c5146fdfac8a67
- `IcosahedralRotationGroupIsoAlternatingFive_v2_2026-11-10.lean`: dc8609b86b28a1505a2ae5dca1fb70ba8bb9a0ef9af6e494a1a28d37abc4d31d
- `IcosahedralRotationGroupIsSimple_2026-11-10.lean`: 0196b7345dbb3e52a7451c26d1f82da37e287b3032cd8996faaaf60df5d65e22

The retargeted simplicity import built under that rebuild. The axioms recorded for the simplicity module are `propext`, `Classical.choice` and `Quot.sound` only. Compiled artifacts of the three comment-redacted modules can differ in compiled-module bytes from earlier builds, because comments and source positions changed; the emitted outputs remain identical to those pins. That rebuild is not a Lake build. The files themselves are not a Lake target. Recorded build texts and compiled artifacts remain omitted from this folder.

To repeat the command-line rebuild:

1. Place the four `.lean` files in one directory (as they already are).
2. Use Lean 4 v4.36.0-rc2 with Mathlib at the pin above.
3. Put this directory, and Mathlib, on the Lean module search path, so each quoted import resolves to the file of the same name.
4. Compile in this order, using paths relative to this directory:
   - `IcosahedralRotationGroup_2026-11-09.lean`
   - `IcosahedralRotationGroupImportedMulEquiv_2026-11-10.lean`
   - `IcosahedralRotationGroupIsoAlternatingFive_v2_2026-11-10.lean`
   - `IcosahedralRotationGroupIsSimple_2026-11-10.lean`

A minimal Lake package is an alternative; it has not been tried on this folder. Example `lean-toolchain` line: `leanprover/lean4:v4.36.0-rc2`. Example `lakefile.toml`:

```
name = "icosahedral-rotation-group"
version = "0.1.0"

[[require]]
name = "mathlib"
scope = "leanprover-community"
rev = "v4.36.0-rc2"

[[lean_lib]]
name = "IcosahedralRotationGroup"
globs = [
  "IcosahedralRotationGroup_2026-11-09",
  "IcosahedralRotationGroupImportedMulEquiv_2026-11-10",
  "IcosahedralRotationGroupIsoAlternatingFive_v2_2026-11-10",
  "IcosahedralRotationGroupIsSimple_2026-11-10",
]
```

Do not add a compiled cache or a Lake manifest to this folder. The files themselves are not a Lake target.

## Provenance

Original source hashes (unredacted files; independently rehashed):

- Official module `IcosahedralRotationGroup_2026-11-09.lean`: fe54b0312e751037ca217ab7e84657c4e0e8b230051bfc818b954184efd597c9 (4842 B). The copy in this folder is byte-identical. No edits.
- `IcosahedralRotationGroupImportedMulEquiv_2026-11-10.lean`: 1247b38a49958db51dab3fefa3db13bf484730409724b9f4d78ed40b7d346065 (46559 B). Recorded build text of that original: 063ea0f5ce5a4c8e8e9566fd787d30db274a37aa84d802b471c5146fdfac8a67. Public copy: 72424b02c07958f7ec5f6827c215c5f51cdd05381287b96fe2481dd0153b5c90 (46074 B). Comment-stripped code is byte-identical to the original.
- `IcosahedralRotationGroupIsoAlternatingFive_v2_2026-11-10.lean`: 6b7cce0c46ffbed065977f4d3fe517437648c138002c2b2a268461136461b573 (12808 B). Recorded build text of that original, identical to the first version of the module: dc8609b86b28a1505a2ae5dca1fb70ba8bb9a0ef9af6e494a1a28d37abc4d31d. Public copy: 37faea30eb0caccd3712fe3cd7f54b620ee862b6e6b3b9380adfb0bf15b86278 (12413 B). Comment-stripped code is byte-identical to the original version 2. The first version of the module (sha256 eac373cdf63816fd5037ab6b318d936efaaaae25a8b1f19de6498a96bd20041d) is not in this folder; version 2 changes only comments and docstrings.
- `IcosahedralRotationGroupIsSimple_2026-11-10.lean`: c0fdfc579fbcb755c94a01b18e2643d668e1ba78ecc8776cdb92aa1e769dc828 (1185 B). Recorded build text of that original: 0196b7345dbb3e52a7451c26d1f82da37e287b3032cd8996faaaf60df5d65e22. Public copy: 17a2c2a05d1d640479485092b0249bd370084add488333ce1abfea216eb0ee21 (964 B). The theorem body after the imports is unchanged.

Edits made in the public copies (comment and import lines only; no declaration changes except the one import retarget):

1. `IcosahedralRotationGroupImportedMulEquiv_2026-11-10.lean`. The opening block comment was replaced with a public header that keeps the mathematical caveats (imported official constants, not local copies; the matrix-list body follows an earlier exact-arithmetic development, with one change to use the imported official vertex set; no homomorphism to A5 is proved here) and drops internal identifiers and private build-recipe text. Three section titles were shortened by dropping internal identifiers:
   - new: `/-! ### Bridge to the official `ℝ` vertex set`
   - new: `/-! ### Transfer to the official `SO(3, ℝ)` stabilizer -/`
   - new: `/-! ### Multiplicativity -/`
   The removed title suffixes are not repeated here. The import lines are unchanged: `import «IcosahedralRotationGroup_2026-11-09»`.
2. `IcosahedralRotationGroupIsoAlternatingFive_v2_2026-11-10.lean`. The opening block comment was replaced with a public header that keeps the table-driven route and the import description, and drops internal identifiers and private build-recipe text. The `framePermList` docstring was shortened to name the script and to state that Lean does not define the geometric action. The new docstring is:

```
/-- Sixty permutations of `Fin 5`, listed in the same order as `scaledRotationList`.
Entry `i` is the table entry for matrix `i`. The table was computed by
`a5_exact_qsqrt5_v2.py` from the frame action; Lean does not define
that geometric action. Every property used below is re-checked here by `decide +kernel`. -/
```

   The import lines are unchanged: `import «IcosahedralRotationGroupImportedMulEquiv_2026-11-10»`.
3. `IcosahedralRotationGroupIsSimple_2026-11-10.lean`. The opening block comment was replaced with a public header. The first import was retargeted so the public chain uses the version-2 isomorphism module already in this folder:
   - old: `import «IcosahedralRotationGroupIsoAlternatingFive_2026-11-10»`
   - new: `import «IcosahedralRotationGroupIsoAlternatingFive_v2_2026-11-10»`
   The original simplicity source imported the first version of the isomorphism module. Version 2 of that module has the same declarations. The retargeted import was used in the clean rebuild recorded under Build instructions: that module exited 0 with empty standard error, and its emitted output is byte-identical to 0196b7345dbb3e52a7451c26d1f82da37e287b3032cd8996faaaf60df5d65e22.
4. `NOTES.md` is a public-safe substitute for the version-2 working note (original sha256 856695ddb28883eb7e8a854f8d082833cba24a74256e9e25c82de0aecada5e9b). That working note is not copied. `NOTES.md` keeps statements, caveats, and the toolchain pin, and omits development internals.

The official module's header still says that I ≅ A5 was then unproved in Lean. That sentence is historical to that file and was left unedited.

## Not in this folder

Working notes, recorded build texts, the first version of the isomorphism module, and any compiled artifacts are omitted on purpose. Frozen preprint files are not modified by this folder.
