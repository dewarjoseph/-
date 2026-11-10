# Chair44 Lean Scratch import-closure (public-screen v2.2, source-only, 2026-11-10)

Suggested landing path: `lean/chair44-scratch-closure-v2.2-2026-11-10/`. This folder is a source-only follow-up to the unedited v2.1 pack. It is the same seventeen header-redacted public-screen copies, with two further docstring-only wording fixes described below, plus this README. It is not a Lake package and not a standalone build. Do not add a `lakefile` or a `.lake` cache. No `SPDX-License-Identifier` headers were added to the `.lean` files.

The files use dated public filenames. Their import lines still name `LeanLab.Scratch.<Module>`. As a flat folder they will not compile until laid out under that module path. Official `lean -R` builds of these copies, under the official module names in a temporary tree, succeeded and are recorded by hash below; those build logs are not in this folder. This pack is not a replacement for the official pins, and it is not a rebuild of the already-landed E/F/G folder or of the v2 landing. The earlier v2 and v2.1 staging folders are left unedited and are not this folder. Frozen preprints are not modified by this folder.

Each `.lean` header says the file is source-only and is not a Lake package, and that it claims nothing beyond the theorems stated below. Headers were redacted; theorem bodies are unchanged from the official pins.

## What this pack changes

Relative to the unedited v2.1 folder, this v2.2 pack:

1. Fixes the in-body section doc at the GeneralLowerBound corollaries (v2.1 L452): the same "weaker than the specialised cubics" sentence now names the crossings, so `1/(30 N³)` is larger only for `N ≥ 4` and `1/(65 N³)` only for `N ≥ 5`, and records that FILE F's `1/N³` supersedes both. The v2.1 header L26–33 is already accurate and is unchanged here.
2. Makes the Classification sharpness bullet name its constants: the `1/(30 N³)` (LemmaDLowerBound220) and `1/(65 N³)` (LemmaDLowerBound330) cubics are larger than `1/N⁶` only for `N ≥ 4` and `N ≥ 5` respectively, and LemmaDLowerBound330Sharper's `1/(34 N³)` at `(3,3,0)` is larger from `N ≥ 4`. FILE F's `1/N³` supersedes these cubics for every `N ≥ 1`.
3. Leaves the other fifteen `.lean` files byte-identical to their v2.1 public copies (new filename only), including the L1 header fix, the L3 L1SevenCubic representatives sentence, and the L5 sentence below. `(public-screen)` stays on its own line after each title.

Docstrings in this pack also name five Scratch modules that are not part of this import-closure and are not included here: `LemmaA.lean`, `LemmaDAxisMultiple`, `LemmaSevenBox`, `LemmaDInfZero220`, and `LemmaDL1Ge4`. None of the seventeen files imports them. A citation of `sInf = 0` at `(2,2,0)` in the LowerBound220 header points at `LemmaDInfZero220`, which is outside this pack.

## Files, hashes, and labels

For each file: public-copy sha256 and size; official pin sha256 (the official file is not in this folder and is not replaced); official `lean -R` raw-build sha256 of the comparable build text (axiom prints, and any path-free messages), which matches the public copy. Axioms named are only `propext`, `Classical.choice`, and `Quot.sound`. Infima and sharpness stay `[X]` where the file says so. Not peer reviewed. ETH false stays `[X]`.

### `LemmaAInt_public_v2.2_2026-11-10.lean`

- Public-copy sha256 `bcd726af4ea2fd6457b2b58e42ca9aaf894278cc6ead9a163a198e40fe37ffb0` (11673 B).
- Official pin sha256 `d0c0078207007a1f893448be8dd5cda9ee613c4aaacfd3aec684d9b31d4a5239` (11985 B) is not in this folder.
- Official `lean -R` raw-build sha256 `d380d285f04eab6b24df88d410faa2d0a42cffc1421ac39ea349ada66515ae86` (1306 B, 12 axiom prints), matching the public copy.

### `LemmaD_public_v2.2_2026-11-10.lean`

- Public-copy sha256 `d97d1b4d7031038c838a580fd37f41f780e79bd61db26af2ed39a5ca311a36bb` (9695 B).
- Official pin sha256 `ecef2a10bd37fdb3ebfe32052166a80d33d65dc9aeffbbc6b703fb1bad472990` (9814 B) is not in this folder.
- Official `lean -R` raw-build sha256 `0d0bcae742ac97ed5af63ee8a96b49b6ca8260318c4d8b2abe7fb7a8e69679e9` (1135 B, 5 axiom prints), matching the public copy.

### `LemmaD4_public_v2.2_2026-11-10.lean`

- Public-copy sha256 `3b2232b7357f92bbe0bfaaa237f905be374f77caeb11c920246df023d8c03d52` (13452 B).
- Official pin sha256 `f55f3bbea8023c14f21e7ff42b891b89f79dd4a520392f66a553c0c2ccf6f80a` (13750 B) is not in this folder.
- Official `lean -R` raw-build sha256 `539c15d91b19cac8e494b6f99c6b43bbe262654cec02462ca3d095e65b69e531` (1448 B, 8 axiom prints), matching the public copy.

### `LemmaDLink_public_v2.2_2026-11-10.lean`

- Public-copy sha256 `035274f6988f78e7ec45fadcbb6d6c1f485f0aa71555580efef34c448a4095a0` (5011 B).
- Official pin sha256 `5db448f9f66b023b17edff40114ca4fff3bdb75c3207acace9e46a618749e9b7` (4862 B) is not in this folder.
- Official `lean -R` raw-build sha256 `6042d00316930675c4bdce6586cb2841bcf5850e59d0c6b65bc64217d491ecb5` (811 B, 7 axiom prints), matching the public copy.

### `LemmaDIntVec_public_v2.2_2026-11-10.lean`

- Public-copy sha256 `1f4491993d5e6cd2c56d8fc324387560d0b0e54c9c4ffa48a8c4455421687337` (23054 B).
- Official pin sha256 `281acaebdedf37d574f04e1f42da77b917280d597671dc1f5e3d5afa1e64997e` (22821 B) is not in this folder.
- Official `lean -R` raw-build sha256 `df36447dd8f6b2befc64f817d0aaaa0fcb0f8d74ed554daa882699aeb4cb3eef` (2186 B, 19 axiom prints), matching the public copy.

### `LemmaDNoZero220_public_v2.2_2026-11-10.lean`

- Public-copy sha256 `f36b800408b15f884f9857a3dba0a8a5a012f0e984361b78e4973236db7cf552` (18964 B).
- Official pin sha256 `d95476a191c502b8193bab35af9a00616169eedf85f410a4eb0528be4f579e2c` (18745 B) is not in this folder.
- Comparable official `lean -R` raw-build sha256 `5c9ef7a8f801727bf904e9af2b002b0d32bfc12cab966b5ae5cdf58f7d8e5258` (759 B, 6 axiom prints). The official pin already emits unused-simp-argument warnings whose messages include source line numbers; those line numbers shift with the longer public header, so the full warning logs are not byte-identical. The axiom-print text matches. The theorem body was not edited to silence the warnings.

### `LemmaDNoZero310211_public_v2.2_2026-11-10.lean`

- Public-copy sha256 `53667ac13a4087e7a5bbcc7a99c7c21edc4e48c5ae06ca3df3fb12ec70f1f61a` (18596 B).
- Official pin sha256 `5ff6fcae83ea327b6e1b7a20351f97451a7e0254974b759ce1189d9d094ee62b` (18389 B) is not in this folder.
- Official `lean -R` raw-build sha256 `ac6f1a41a5e17781dda5e4b57a2e674dab6f8e8e06a965f3bfc41077502f2ba7` (1065 B, 8 axiom prints), matching the public copy.

### `LemmaDOrbitNoZero_public_v2.2_2026-11-10.lean`

- Public-copy sha256 `3587dbee4cb0d3f9607a6464ac334b2e96d19af7f0f5b89df082dd119b578065` (25703 B).
- Official pin sha256 `eb4783276ef7c0a88b08c15670c24dd74a895cb61dfc8178618e4e2120649fc5` (25496 B) is not in this folder.
- Official `lean -R` raw-build sha256 `585b169ace286156970b6e538ae2a0d359bc8f3c8ff6182b0edce07ecd807167` (1849 B, 14 axiom prints), matching the public copy.

### `LemmaDOddL1Seven_public_v2.2_2026-11-10.lean`

- Public-copy sha256 `ed4a508242139d7cc3dde555d835718ef226a19c3d6621a2cad3bd374ffbf61c` (11501 B).
- Official pin sha256 `f4036d29c74fb509d402294620bb21f48ffc3bc89bd1040f11ac806f15e2e068` (11253 B) is not in this folder.
- Official `lean -R` raw-build sha256 `494442bb5d8dbc47540ce130a9fe8f6d43c29e6b34f05d93d6ff1526dfb94b7d` (774 B, 6 axiom prints), matching the public copy.

### `LemmaDL1Six_public_v2.2_2026-11-10.lean`

- Public-copy sha256 `e3e1c0971ba1ca78ef11768b29ffa91c25c1e1806107d7af6ee99bbec5f15b0b` (22334 B).
- Official pin sha256 `1b4c1abf7a22a4474e925e5f2bc615d6b0e46c135b227278284e8f327fe92476` (22370 B) is not in this folder.
- Official `lean -R` raw-build sha256 `b2e6efc4f6b1217f82ebe0807554fa15102c15d812ddfc94ceee0c86682ca70d` (1992 B, 16 axiom prints), matching the public copy.

### `LemmaDL1SevenMore_public_v2.2_2026-11-10.lean`

- Public-copy sha256 `cb335666e28e2aaf83d8ab233cb528a9101dde6a7114408e81f0f4138e2b303e` (21332 B).
- Official pin sha256 `51a3e9f7e40e8c3cf1eb4ccaa5bdfb741636fadb93f197ed5f63b58895185408` (21517 B) is not in this folder.
- Official `lean -R` raw-build sha256 `58fd3d17536933a0dab43c7af6f4934fc4de78f41df7596b98aa4bd4a4d098bc` (1186 B, 9 axiom prints), matching the public copy.

### `LemmaDGeneralLowerBound_public_v2.2_2026-11-10.lean`

- Public-copy sha256 `e0f15f87ce82e3ab55c0afd718975b303e09f6b8adbe20ea078a77ef45ef4300` (21685 B).
- Official pin sha256 `884d0aceccc2000ea93d77fcae48caff6c61178a4083d1845b1a601a6ef9d394` (21046 B) is not in this folder.
- Official `lean -R` raw-build sha256 `c5a09bcacf70df381e11e65f5c81f22fcef9185339ea1212fd6c1333f717e006` (735 B, 5 axiom prints), matching the public copy.

### `LemmaDLowerBound220_public_v2.2_2026-11-10.lean`

- Public-copy sha256 `378e5bc5ad4899486f3172e6c652cf553fa75f24379d0cf7e3c3dd7a6b0095be` (28115 B).
- Official pin sha256 `0e05234ecae80955f385e4cc11c07b0e6af7f043031d05407e0e25a7426af2bb` (27866 B) is not in this folder.
- Official `lean -R` raw-build sha256 `386e12bfe0bc4f257c9842c94de99a5985a60cc792b79d0f559438694a6c1c38` (865 B, 7 axiom prints), matching the public copy.

### `LemmaDLowerBound330_public_v2.2_2026-11-10.lean`

- Public-copy sha256 `31197159da5c0b680ac0e35d910d84a7b681ef5baaa5b568d2e1355efcc90c05` (32317 B).
- Official pin sha256 `a919b91a65bd14b0060bf0f514f523ab96252245f09fa0bc7aee87fe426f69bc` (32068 B) is not in this folder.
- Official `lean -R` raw-build sha256 `ecd9ee60d8957cd3b950fb8ceb7871e1aea70f0730ff735cf865a0f3c4c81358` (773 B, 6 axiom prints), matching the public copy.

### `LemmaDLowerBound330Sharper_public_v2.2_2026-11-10.lean`

- Public-copy sha256 `075013f87d4f2bd57aa130e6a80c55c2f2ea94b5172ffd07759e4d2c51fe697a` (19641 B).
- Official pin sha256 `6e0751833d278eda9ee84ad5d55e130d31e7d05f95031b136ec5e26d421d41ea` (19381 B) is not in this folder.
- Official `lean -R` raw-build sha256 `46b0eafcfe5390915449c46eafac85f7919d3c572a862083c87cdb8fa75a850a` (672 B, 5 axiom prints), matching the public copy.

### `LemmaDL1SevenClassification_public_v2.2_2026-11-10.lean`

- Public-copy sha256 `3ef850e65f547a539e9eca724cb625f0b11206de4f1bb7b9723ee598d49fd094` (59780 B).
- Official pin sha256 `c26fbbd6ae052f49d3fe2d642b1c9d2bb413e1bce606cd5d2f8e7439b22f159a` (59365 B) is not in this folder.
- Official `lean -R` raw-build sha256 `b261a5e9eaa66b908bdaf8b8e70894b08c316a2a581ed37df3089dc12e4e4c99` (4598 B, 33 axiom prints), matching the public copy.

### `LemmaDLowerBoundL1SevenCubic_public_v2.2_2026-11-10.lean`

- Public-copy sha256 `08538a53c2ac5ececd5b0513c1e72d0821785612f0cc461c138b825465ffb417` (77377 B).
- Official pin sha256 `290a95355a66d676ca23aab4a0ef7fcda567362a97c6a85bb97c4bd3a494c6fd` (77026 B) is not in this folder.
- Official `lean -R` raw-build sha256 `10b47bbc49af074ae8873c2303e2e2b9f7769a3af0bd7bedb5cae213e9d5c750` (1526 B, 10 axiom prints), matching the public copy.

## Not in this folder

The official pins, the private build package, any `.lake` cache, build logs, working notes, and the earlier seven-file, v2, and v2.1 staging folders are omitted on purpose. FILE E, FILE F, and FILE G public copies already landed elsewhere are not repeated here.
