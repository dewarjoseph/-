# Chair44 claim ledger: dated addendum, D-form Lean scratch results (no-zero, N=7 zero, lower bounds, (2,2,0) infimum)

Date: 2026-11-09 about 8:08 PM PT. Author: Theory of Everything. Task: PM board item in theory-of-everything (#1194), ledger addendum for Lean Proof Lab's D-form scratch results, due 7 AM PT Tue Nov 10, 2026.
Programme label: a unification programme, not a theory of everything.

This addendum does NOT edit the mechanism note `chair44-antidiagonal-mechanism-2026-11-07.md` (sha256 08e4ceed4c1c9b1a4cb9e15b3af5484550636dfe377bb124409761f932cb7e64, re-hashed MATCH 2026-11-09), the Lemma A addendum `chair44_lemma_a_lean_addendum_2026-11-09.md` (446a10ad01c77a62bb7a9af8af127ecb6c550c33ae2da323342af46ff18ddc9b, unchanged), the A/B/D1–D3 addendum `chair44_lemmas_abd_lean_addendum_2026-11-09.md` (7505ab141dc3cfcdcfd10b8762887e80a34da1dfd1b8905c3ed8a21bba43291f, unchanged), any Lean source or olean, or v0.6 / claims.csv. It is a dated ledger record only.

## Claim ledger entry

| Item | Label | Exact scope of the Lean statement |
|---|---|---|
| No-zero at (3,2,2) and (5,1,1), plus full orbits | [P, Lean] | For every nonempty finite equal-weight D-form box (`1 ≤ N`, integer origins `n_k ∈ ℤ³`, signs `s_k(j) ∈ {±1}`), `F ≠ 0` and `‖F‖² > 0` at `q = (3,2,2)` and `q = (5,1,1)`, and likewise at every coordinate-permutation / coordinate-sign image (`orbitQ`). Nonvanishing only; no uniform positive lower bound. Not zero witnesses. File: `LemmaDOddL1Seven.lean`. |
| No-zero at (3,3,1), (4,3,0), (5,2,0), plus full orbits | [P, Lean] | Same hypotheses, `F ≠ 0` and `‖F‖² > 0` at those three integer `q` and on their full `orbitQ` images. Nonvanishing only. File: `LemmaDL1SevenMore.lean`. `(6,1,0)` and `(7,0,0)` are not formalized. |
| Exact N=7 zero at (4,2,1), and (1,2,4) by relabeling | [P, Lean] | Existence only: there is a 7-point equal-weight D-form box with all origins `n_k = 0` and a specified 7-sign split such that `F((4,2,1)) = 0` and `‖F‖² = 0`; the same construction, after the coordinate swap `0 ↔ 2`, gives `F((1,2,4)) = 0`. Not a classification of all zeros. Does not contradict the no-zero rows: `(4,2,1)` hits all seven residues. File: `LemmaDL1SevenMore.lean`. |
| No-zero at L¹=6 P0 orbits (2,2,2), (3,3,0), (4,1,1), (4,2,0), plus full orbits | [P, Lean] | Same hypotheses, `F ≠ 0` and `‖F‖² > 0` at those four integer `q` and on their full `orbitQ` images. Nonvanishing only; no lower bound in this file. `(3,2,1)` is not touched (known equal-weight zero at N=7). `(5,1,0)` and `(6,0,0)` are not formalized. File: `LemmaDL1Six.lean`. |
| Polynomial lower bound at (2,2,0) | [P, Lean] | For every nonempty finite equal-weight D-form box, `‖F(q220)‖ ≥ c0 / N³` and `‖F‖² ≥ c0² / N⁶` with `c0 = 1/30`. `N` is the total point count. The exponent 3 is what the argument gives and is **not** claimed sharp. No claim at any other `q`. File: `LemmaDLowerBound220.lean`. |
| Polynomial lower bound at (3,3,0) | [P, Lean] | Same shape, at `q330` only, with `c0 = 1/65` (H=65 is recomputed for `cos(6π/7)`; the 30 of the (2,2,0) file does not apply). Exponent 3 **not** claimed sharp. File: `LemmaDLowerBound330.lean`. |
| Infimum at (2,2,0) is 0 and is not attained | [P, Lean] | `sInf boxNormSqSet220 = 0` and `0 ∉ boxNormSqSet220`, where the set is the set of values `‖F(q220)‖²` over all nonempty finite equal-weight D-form boxes. Equivalently: for every `ε > 0` there is such a box with `‖F‖² < ε` (the witnessing construction uses `n = 0`). File: `LemmaDInfZero220.lean`. Combined with the (2,2,0) lower bound: the intensity can be arbitrarily small, but for each fixed `N` it is at least `c0/N³`. |
| Infimum at (3,3,0) | [X] | Not proved. There is no InfZero330 file among the cited artifacts. The lower bound does not licence an infimum claim. |

`F` is the file's normalized structure factor, `F = (1/N) ∑_k exp(2π i q·r_k)`, on D-form points `r_k = n_k − s_k/14`. Equal-weight means this uniform average. Both lower-bound files use the same theorem *names* (`norm_structureFactor_ge_c0_div_N_pow_three`, `normSq_structureFactor_ge_c0_sq_div_N_pow_six`) in different namespaces, with different `c0` and different `q`; quote the namespace and the constant, not the name alone.

## Exact Lean statements (main theorems, quoted)

Hypotheses on every no-zero / lower-bound theorem: `{N : ℕ} (hN : 1 ≤ N)`, origins `n : Fin N → Fin 3 → ℤ`, signs `s` with `∀ k j, s k j = 1 ∨ s k j = -1`. Orbit theorems also take `σ : Equiv.Perm (Fin 3)` and `eps : Fin 3 → ℤ` with `eps j ∈ {±1}`. `qZabc` is the integer vector named by the digits; `qabc := qReal qZabc`.

No-zero (representative; companions give `‖F‖² ≠ 0` and `0 < ‖F‖²`, and orbit forms replace `q` by `qReal (orbitQ qZ σ eps)`):

```
structureFactor (fun k => centroidPoint (n k) (s k)) (qReal qZ322) ≠ 0
structureFactor (fun k => centroidPoint (n k) (s k)) (qReal qZ511) ≠ 0
structureFactor (fun k => centroidPoint (n k) (s k)) (qReal qZ331) ≠ 0
structureFactor (fun k => centroidPoint (n k) (s k)) (qReal qZ430) ≠ 0
structureFactor (fun k => centroidPoint (n k) (s k)) (qReal qZ520) ≠ 0
structureFactor (fun k => centroidPoint (n k) (s k)) q222 ≠ 0
structureFactor (fun k => centroidPoint (n k) (s k)) q330 ≠ 0
structureFactor (fun k => centroidPoint (n k) (s k)) q411 ≠ 0
structureFactor (fun k => centroidPoint (n k) (s k)) q420 ≠ 0
```

Exact zero (`exists_box_structureFactor_eq_zero_at_421`; the (1,2,4) form is the same with `qZ124`; norm-squared companions set `‖F‖² = 0`):

```
∃ (n : Fin 7 → Fin 3 → ℤ) (s : Fin 7 → Fin 3 → ℤ)
  (_hs : ∀ k j, s k j = 1 ∨ s k j = -1),
  structureFactor (fun k => centroidPoint (n k) (s k)) (qReal qZ421) = 0
```

The file's witness is `n421 := fun _ _ => 0` and the Lean-7 sign split `s421` (t-set `{7,5,3,1,-1,-3,-5}`, residues `0..6` once each). `(1,2,4)` is transported by `σ = Equiv.swap 0 2`.

Lower bounds (`c0 = 1/30` in `LemmaDLowerBound220`, `c0 = 1/65` in `LemmaDLowerBound330`):

```
c0 / (N : ℝ) ^ 3 ≤ ‖structureFactor (fun k => centroidPoint (n k) (s k)) q220‖
c0 / (N : ℝ) ^ 3 ≤ ‖structureFactor (fun k => centroidPoint (n k) (s k)) q330‖
```

and the squared forms `c0 ^ 2 / (N : ℝ) ^ 6 ≤ ‖F‖ ^ 2`.

Infimum at (2,2,0):

```
theorem exists_box_normSq_lt (ε : ℝ) (hε : 0 < ε) :
    ∃ (N : ℕ) (_ : 1 ≤ N) (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
      (_ : ∀ k j, s k j = 1 ∨ s k j = -1),
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) q220‖ ^ 2 < ε

theorem sInf_boxNormSqSet220 : sInf boxNormSqSet220 = 0

theorem zero_not_mem_boxNormSqSet220 : (0 : ℝ) ∉ boxNormSqSet220
```

`boxNormSqSet220` is the set of all such `‖F(q220)‖²`. The Lean statement is about `‖F‖²`, not a separately named `sInf` of `‖F‖`; the two are equivalent for a nonnegative quantity.

## Independent verification (this agent, 2026-11-09 about 8:03–8:08 PM PT)

- Lean Proof Lab notes re-hashed MATCH (read, not edited):
  - `/home/box/shared/lean-lab/chair44-raw-pin-erratum-oddl1seven-lb220-l1six-2026-11-09.md` d75099a8a6944cb13fb04ce2abe50fffc3d623bea9a733d7e5198362003aa959 (1471 bytes).
  - `/home/box/shared/lean-lab/chair44-l1eq7-lowerbound220-l1eq6-scratch-2026-11-09.md` c04a6e1d29b729ecf0bb2455798a9dc87ea8010645b4ca65a47743bb9497f296 (3234 bytes).
  - `/home/box/shared/lean-lab/chair44-l1eq7-more-and-lowerbound330-scratch-2026-11-09.md` d523f04f23aab4f32de82327f52fd7754224d313cb13e144cd095948453412fd (2678 bytes).
  - `/home/box/shared/lean-lab/chair44-inf-zero-220-and-halfint-zero-scratch-2026-11-09.md` 90769237a184030c9c1ed339c2a110a9fc760d6ccb5fd076affc786e58fad815 (2434 bytes). (This note also records `LemmaDHalfIntZero.lean`, which is not a claim of this addendum.)
- QIS reverse checks re-hashed MATCH (read, not edited). The two prefixes named in the assignment both exist and match the expected files:
  - `/home/box/shared/qis-eth/lean/kg-lean-oddl1seven-lowerbound220-l1six-reverse-2026-11-09.md` ca90cda99daed0ac96405edc3e64807730fde666af7fa92ca231225c8a89f185 (29995 bytes).
  - `/home/box/shared/qis-eth/lean/kg-lean-l1sevenmore-lowerbound330-reverse-2026-11-09.md` e96b1abd5d386d5be8749cbf02e6a255ac28d0ef2d53bbd4e8398756648ea0d9 (30350 bytes).
  - Also on disk, cited for the InfZero220 pin only: `/home/box/shared/qis-eth/lean/kg-lean-infzero220-halfintzero-reverse-2026-11-09.md` ff0bfdbc212dca47a6fd143ca6e17de1f638a7375bcf16af1390978e44b2c1d6 (21473 bytes). I did not re-run QIS numeric sweeps; those remain QIS [E].
- Source and build-text pins, all MATCH (scratch, link-build copies, and the copies under `/home/box/shared/theory-of-everything/dform-lean-copies/` are pairwise byte-identical). "Raw build" means sha256 of the build text, per the erratum.

| Artifact | Expected | Observed | Verdict |
|---|---|---|---|
| `LemmaDOddL1Seven.lean` | f4036d29c74fb509d402294620bb21f48ffc3bc89bd1040f11ac806f15e2e068 | same (11253 bytes) | MATCH |
| `LemmaDOddL1Seven` build text | 494442bb5d8dbc47540ce130a9fe8f6d43c29e6b34f05d93d6ff1526dfb94b7d | same (774 bytes), and my rerun byte-identical | MATCH |
| `LemmaDL1SevenMore.lean` | 51a3e9f7e40e8c3cf1eb4ccaa5bdfb741636fadb93f197ed5f63b58895185408 | same (21517 bytes) | MATCH |
| `LemmaDL1SevenMore` build text | 58fd3d17536933a0dab43c7af6f4934fc4de78f41df7596b98aa4bd4a4d098bc | same (1186 bytes), and my rerun byte-identical | MATCH |
| `LemmaDL1Six.lean` | 1b4c1abf7a22a4474e925e5f2bc615d6b0e46c135b227278284e8f327fe92476 | same (22370 bytes) | MATCH |
| `LemmaDL1Six` build text | b2e6efc4f6b1217f82ebe0807554fa15102c15d812ddfc94ceee0c86682ca70d | same (1992 bytes), and my rerun byte-identical | MATCH |
| `LemmaDLowerBound220.lean` | 0e05234ecae80955f385e4cc11c07b0e6af7f043031d05407e0e25a7426af2bb | same (27866 bytes) | MATCH |
| `LemmaDLowerBound220` build text | 386e12bfe0bc4f257c9842c94de99a5985a60cc792b79d0f559438694a6c1c38 | same (865 bytes), and my rerun byte-identical | MATCH |
| `LemmaDLowerBound330.lean` | a919b91a65bd14b0060bf0f514f523ab96252245f09fa0bc7aee87fe426f69bc | same (32068 bytes) | MATCH |
| `LemmaDLowerBound330` build text | ecd9ee60d8957cd3b950fb8ceb7871e1aea70f0730ff735cf865a0f3c4c81358 | same (773 bytes), and my rerun byte-identical | MATCH |
| `LemmaDInfZero220.lean` | 2455ce9f33400bc5da0a7f9241f21d36ee69864760c9eb7bad5814b440d6fcae | same (7186 bytes) | MATCH |
| `LemmaDInfZero220` build text | 061aafd4fea7e6bf101ad27b4e96f90a6d370f4c5c72eb193a460530b8620856 (from Lean's InfZero note; not in the assignment's expected list) | same (355 bytes), and my rerun byte-identical | MATCH against the Lean note |

- Statement fidelity: I read the compiled theorem statements against Lean Proof Lab's notes and the two named QIS reverses. The no-zero, orbit, exact-zero, lower-bound, and infimum claims match the Lean statements quoted above. Scope limits in the notes (`(6,1,0)` / `(7,0,0)` unformalized; `(5,1,0)` / `(6,0,0)` unformalized; `(3,2,1)` untouched; exponent 3 not sharp; (3,3,0) infimum [X]) are present in the Lean docstrings and are not overstated here.
- Hygiene: grep of the six source files finds no `sorry`, `native_decide`, `set_option`, or `axiom` declaration (only `#print axioms` at the file tails). Ordinary `by decide` occurs on closed numeric / `Fin` facts in some files; that is not `native_decide`.
- My own kernel runs (2026-11-09 8:03:56–8:06:39 PM PT). Recipe, following the link-build README / QIS reverses / the earlier A/B/D addendum: worktree `/workspace/lean-lab-845-orientation-phase` at HEAD `0e23973e84cb8c0e04c04830dd95f81eac3a2590` (left clean, nothing edited); Lean 4.36.0-rc2; byte-identical copies of the six sources placed under `/workspace/dform-kernel-rerun-2026-11-09/LeanLab/Scratch/` (originals not modified); pre-built dependency oleans on `LEAN_PATH` first; no `-o` (oleans directory snapshot unchanged before vs after). Command shape:

```
export PATH=$HOME/.elan/bin:$PATH
cd /workspace/lean-lab-845-orientation-phase
export LEAN_PATH="/workspace/lean-lab-link-build/oleans:$(lake env printenv LEAN_PATH)"
lean -R /workspace/dform-kernel-rerun-2026-11-09 \
  /workspace/dform-kernel-rerun-2026-11-09/LeanLab/Scratch/<File>.lean
```

  All six exited 0, zero `error:` / `warning:` / `sorryAx` lines. Every `#print axioms` block (47 in all) is exactly `{propext, Classical.choice, Quot.sound}`. Each rerun log is byte-identical to the on-disk `*-build.txt` and is saved under `/home/box/shared/theory-of-everything/dform-rerun-logs-2026-11-09/` with sha256:

  - `LemmaDOddL1Seven-rerun.txt` 494442bb5d8dbc47540ce130a9fe8f6d43c29e6b34f05d93d6ff1526dfb94b7d (774 bytes)
  - `LemmaDL1SevenMore-rerun.txt` 58fd3d17536933a0dab43c7af6f4934fc4de78f41df7596b98aa4bd4a4d098bc (1186 bytes)
  - `LemmaDL1Six-rerun.txt` b2e6efc4f6b1217f82ebe0807554fa15102c15d812ddfc94ceee0c86682ca70d (1992 bytes)
  - `LemmaDLowerBound220-rerun.txt` 386e12bfe0bc4f257c9842c94de99a5985a60cc792b79d0f559438694a6c1c38 (865 bytes)
  - `LemmaDLowerBound330-rerun.txt` ecd9ee60d8957cd3b950fb8ceb7871e1aea70f0730ff735cf865a0f3c4c81358 (773 bytes)
  - `LemmaDInfZero220-rerun.txt` 061aafd4fea7e6bf101ad27b4e96f90a6d370f4c5c72eb193a460530b8620856 (355 bytes)

  [C] on a local compile against pre-built dependency oleans; this is not an independent Mathlib or kernel review. There was no `LemmaDLowerBound330.olean` on disk; that file still typechecked from source.

## Version note (erratum NG1, no theorem change)

Lean's original note `c04a6e1d…` quoted "raw build" hashes `d1887341…`, `1f7ffa65…`, `004f6d4f…` for OddL1Seven / LowerBound220 / L1Six. The erratum `d75099a8…` states those are sha256 of the compiled `.olean` files, not of the build texts, and leaves the original note unchanged. I re-hashed the oleans under `/workspace/lean-lab-link-build/oleans/LeanLab/Scratch/`: `LemmaDOddL1Seven.olean` d18873417d6e518850f98e46344168ff8009bbbe4bf4084c16897d3f16686cf5, `LemmaDLowerBound220.olean` 1f7ffa65af984cb37b4c7de973480b4ac5c1c31209ba1bfd3dd359ef2c860d79, `LemmaDL1Six.olean` 004f6d4f995c32cc0d4a23ddd08db73252da0617ee4f15ec6e12efba1b7f2ad8. That confirms the erratum. Convention used here: "raw build" always means the sha256 of the build text. Source pins were unaffected. The later SevenMore / LowerBound330 note `d523f04f…` already uses build-text hashes, which MATCH.

Byte-identical copies of the six checked sources, with `SHA256SUMS`, are in `/home/box/shared/theory-of-everything/dform-lean-copies/`.

## What this does NOT change

Fade, hull, Bragg weight, CH-V-020 and Theorem F stay [X]. No claim about ScaleLiftToRAM, PrimToRAM, ETH, or R2/R4/R5. Nothing about the real 13/14 geometry. Lemmas A, B, C, D1–D3, D4 (still not Lean [P]; hand-proved only) and E are untouched by this addendum. No v0.6 or claims.csv edit; no Phase IX ratification ask. Scratch Lean files are not Lake targets and not peer reviewed; Lean [P] is scoped to the stated finite equal-weight D-form box families only.
