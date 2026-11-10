# Chair44 Lean sources (public-screen v2 / FILE F v2.1, source-only, 2026-11-09)

Suggested landing path: `lean/chair44-file-efg-v2-2026-11-09/`. This folder is a source-only record. It is not a Lake package and not a standalone build. Each `.lean` file imports unpublished `LeanLab.Scratch` modules that are not in this folder and are not published with it; the files will not compile as landed. Do not add a `lakefile` or a `.lake` cache to make them build. No `SPDX-License-Identifier` headers were added to the `.lean` files.

## What these files are, and what they do not build

They are public-screen v2 copies of FILE E and FILE G, and a public-screen v2.1 copy of FILE F (a one-sentence header correction of public v2 F). Headers were redacted; theorem bodies are unchanged from the official pins (FILE G also adds a three-line comment docstring above one theorem). Stored official `lean -R` raw-build texts of these copies hash-match the official pin build texts; this folder does not include those build logs and does not itself compile.

A later header-redacted import closure would be a different landing, and is not this folder.

## Files and labels

### FILE E (public-screen v2) — `LemmaDOrbitLowerBoundCubic_public_v2_2026-11-09.lean`

- sha256 `5e1a8413249f2583a4783c0c37fcd9813944c5be96ce9274b750a012e83a308e`
- Official pin sha256 `445f37ba981b4fd98ce169804ba3156298a1c102a1d805af45c28009a280a614` is not in this folder and is not replaced by this copy. After the header, the remainder is byte-identical to the pin. Stored raw-build text sha256 `0915de88288ff71a6583ecf8353a3510bb6f9c52427b7e01e50d97d8a26de8bc` matches the official pin raw.
- **[P, Lean]** The explicit `‖F‖ ≥ c0 / N³` bounds at the six one-conjugate-pair representatives transfer to every signed-permutation orbit image, with the same rational `c0`: (2,2,0) `1/30`; (3,3,0) `1/34`; (1,1,0) `1/38`; (6,1,0) `1/38`; (5,2,0) `1/30`; (4,3,0) `1/34`.
- After the FILE F erratum below, quote `1/N³` as the current numerical lower bound at those orbits. The `c0` theorems remain correct [P, Lean] but weaker.
- Infima and sharpness stay [X]. Not peer reviewed. ETH false stays [X].

### FILE F (public-screen v2.1) — `LemmaDUniversalLowerBoundN3_public_v2.1_2026-11-09.lean`

- sha256 `7b84edcff13f068d47b03f4d473b3eb61155edd043750800c6d5cb7b970aff1c`
- Official pin sha256 `365b8809a4d60132250f1c6b6c0ed53f1b0470a8654496064c4247e4e60c9cf1` is not in this folder and is not replaced by this copy. After the header, the remainder is byte-identical to the pin. Stored raw-build text sha256 `e8b1b50cdf2dac62794f1414197a302f5e18f1a499f37acfdff9ad6178e97683` matches the official pin raw and the public v2 F raw.
- This copy is a one-sentence header fix of public-screen v2 F (sha256 `64e0835ab902666c0151e2a795bb4273a7f51246ba86c7fc0527643261196300`, not in this folder). Official pin and that v2 copy still contain the backwards "remain the sharper statements" sentence and were left unedited on purpose.
- **[P, Lean]** For every integer wavevector and every equal-weight D-form box, if `F ≠ 0` then `‖F‖ ≥ 1/N³`.
- The header at v2.1 lines 37–40 states that the specialised one-pair `c0/N³` constants are strictly weaker than this file's constant-1 bound, and cites the pinned erratum. See also the public landing copy of that erratum in this folder.
- Infima and sharpness stay [X]. Not peer reviewed. ETH false stays [X].

### FILE G (public-screen v2) — `LemmaDConditionalN2_330_public_v2_2026-11-09.lean`

- sha256 `174a81ea842f183445b0144c83ed4559b285890255cb238d71f1f4510c050635`
- Official pin sha256 `d6e426acc26a618e8be0a893180825148b16888c740c282cae4bf78009a31dcd` is not in this folder and is not replaced by this copy. Header redacted; a three-line comment docstring was added above `normSq_structureFactor_ge_c_of_kappa_sq_div_N_pow_four`. After removing that comment, the remainder after the header is byte-identical to the pin. Stored raw-build text sha256 `bc4a51173cbb584f13e8ba17c7bd554f310c904a1915627295de32407378efa5` matches the official pin raw (and the earlier public copy).
- **[P, Lean, conditional]** If `hBA` holds (an unclaimed open hypothesis: `cos(6π/7)` badly approximable with an explicit positive `κ`), then at `q = (3,3,0)` every nonempty equal-weight D-form box satisfies `‖F‖ ≥ c(κ)/N²` with `c(κ) = min(κ, 2/5)`. The same constant transfers to the signed-permutation orbit of `(3,3,0)`.
- This file does not claim `hBA`, does not inhabit `hBA`, and states no unconditional numeric `c`. Sharpness stays [X]. Not peer reviewed. ETH false stays [X].

### FILE F wording erratum (public v2 / v2.1 landing copy) — `FILE-F-sharper-sentence-erratum-public-v2-2026-11-09.md`

- sha256 `684522be4e4ecacd0d5437aaf410e38b767938a2f9cd5a087e97d3c25725804c`
- Documentation [F] only. It does not change FILE F's theorems. The pinned source erratum (sha256 `a3da34b3c53f5e3dcea0a019300c88f95822b64b69ce36c53869a06f62a9aa0a`) is not rewritten.

## Not in this folder

The whole `lake-ef` package, any `.lake` cache, official FILE G, unpublished working notes, the public-screen v1 copies, and the uncorrected public-screen v2 FILE F are omitted on purpose. Frozen v0.6 is not modified by this folder. No v0.7 scratch is included. Commit `77b460f` is not this landing.
