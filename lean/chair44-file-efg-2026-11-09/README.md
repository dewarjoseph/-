# Chair44 Lean sources (public-safe subset, 2026-11-09)

Suggested landing path: `lean/chair44-file-efg-2026-11-09/`. This folder is a source record with labels and hashes, not a Lake package. The files import other Scratch modules that are not included here, so they will not build as landed. No `SPDX-License-Identifier` headers were added to the `.lean` files.

```
Folder: lean/chair44-file-efg-2026-11-09/ (Chair44 Lean sources: public-safe subset as listed by Lean Proof Lab, inventory sha256 582c36ceadde3d3ebe08c307981519a4fa1d06c9542e4704c1a53c04b1eea07d; the inventory file itself is not in this folder)
Inventory tag (BIP, proposed): RESEARCH-SOFTWARE
Employer screen: not-employer-device-subject-matter-on-current-text (text-limited; NOT a §2870 determination)
Evidence labels: [P, Lean] items are kernel-checked as stated (conditional hypotheses stay stated); everything else [C]/[E]/[X] as in the source; weakest wins
Hashes: per-file sha256 as listed below
Licence/notice: see the repository root README and LICENSE as they stand at the commit you received; this folder adds no licence grant and changes none.
```

Licence status for this repository is unsettled (no root LICENSE file at 6d91f2f). Independently confirmed: still no root LICENSE at a6462b0c [C].

## Files and labels

### FILE E — `LemmaDOrbitLowerBoundCubic.lean`

- sha256 `445f37ba981b4fd98ce169804ba3156298a1c102a1d805af45c28009a280a614`
- **[P, Lean]** The explicit `‖F‖ ≥ c0 / N³` bounds at the six one-conjugate-pair representatives transfer to every signed-permutation orbit image, with the same rational `c0`: (2,2,0) `1/30`; (3,3,0) `1/34`; (1,1,0) `1/38`; (6,1,0) `1/38`; (5,2,0) `1/30`; (4,3,0) `1/34`.
- After the FILE F erratum below, quote `1/N³` as the current numerical lower bound at those orbits. The `c0` theorems remain correct [P, Lean] but weaker.
- Infima and sharpness stay [X]. Not peer reviewed. ETH false stays [X].

### FILE F — `LemmaDUniversalLowerBoundN3.lean`

- sha256 `365b8809a4d60132250f1c6b6c0ed53f1b0470a8654496064c4247e4e60c9cf1`
- **[P, Lean]** For every integer wavevector and every equal-weight D-form box, if `F ≠ 0` then `‖F‖ ≥ 1/N³`.
- The docstring sentence at lines 31–33 that specialised one-pair `c0/N³` constants "remain the sharper statements there" is documentation [F]. See the erratum. The theorems themselves are unchanged.
- Infima and sharpness stay [X]. Not peer reviewed. ETH false stays [X].

### FILE G (public-screen copy) — `LemmaDConditionalN2_330_public_2026-11-09.lean`

- sha256 `224a279654e9ccde550c8c198d6d52edc111dce70a8a5b6931dca2066dec7c36`
- Official FILE G pin sha256 `d6e426acc26a618e8be0a893180825148b16888c740c282cae4bf78009a31dcd` is not in this folder and is not replaced by this copy. Header only was redacted; theorem bodies are unchanged. The official and public-copy raw build texts share sha256 `bc4a51173cbb584f13e8ba17c7bd554f310c904a1915627295de32407378efa5`.
- **[P, Lean, conditional]** If `hBA` holds (an unclaimed open hypothesis: `cos(6π/7)` badly approximable with an explicit positive `κ`), then at `q = (3,3,0)` every nonempty equal-weight D-form box satisfies `‖F‖ ≥ c(κ)/N²` with `c(κ) = min(κ, 2/5)`. The same constant transfers to the signed-permutation orbit of `(3,3,0)`.
- This file does not claim `hBA`, does not inhabit `hBA`, and states no unconditional numeric `c`. Sharpness stays [X]. Not peer reviewed. ETH false stays [X].

### FILE F wording erratum (public landing copy) — `FILE-F-sharper-sentence-erratum-public-2026-11-09.md`

- sha256 `b4d899fb9ba802cf3b429e626df4db7aa225f9e10e60668bafc28624a6566a35`
- Documentation [F] only. It does not change FILE F's theorems. The pinned source erratum (sha256 `a3da34b3c53f5e3dcea0a019300c88f95822b64b69ce36c53869a06f62a9aa0a`) is not rewritten.

## Not in this folder

The whole `lake-ef` package, any `.lake` cache, and unpublished working notes are omitted on purpose. Frozen v0.6 is not modified by this folder. No v0.7 scratch is included.
