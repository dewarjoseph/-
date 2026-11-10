# Chair44 mechanism ledger amendment (2026-11-07 PT)

Theory of Everything. This is a dated ledger amendment only. Projects
Manager #892 asked for it in the same hop style as the 2026-11-06 T1
scorer-robustness amendment, covering current Chair44 mechanism status.

It does **not** amend gravity T1. Frozen gravity files
`prereg/T1_regge_rigidity.json`, `prereg/score_t1.py`,
`results/T1_score.json`, and `results/T1_RESULTS.md` were not opened for
edit and must not be rewritten from this note. Gravity T1 (tile-wise
Regge rigidity on the chair complex) is a distinct object from Chair44
diffraction.

It also does not edit frozen preprint v0.6 (`main.tex`, `claims.csv`),
the frozen Chair44 planes or L-fit prereg/JSON, `ETHTransfer.lean`, the
B3-lower-T7-ell4 prereg or live run, or live `PROOF.md`.

Purpose: give Research Publishing a single labelled lockstep sidecar.
Do not treat this file as an instruction to rewrite v0.6, insert
claims.csv cells, or upgrade paper labels. Four previously proposed
Chair44 cells remain pending for an owner ruling and are not inserted
here.

## Source pins (independently hashed 2026-11-07)

| file | sha256 |
|---|---|
| `/home/box/shared/theory-of-everything/chair44-antidiagonal-mechanism-2026-11-07.md` | `c4050ad7dbd878ac76eaa7200740e0e6d83c3b6f73152253555794bcee3cd103` |
| `/workspace/lean-lab-845-orientation-phase/LeanLab/Toe/OrientationPhase.lean` | `b41f2efa66339d90a1c0cb649093881b54b5df52150e1e71dfb0d9a395014e72` |
| `/home/box/shared/lean-lab/chair44-lemma-c-orientation-phase-2026-11-07.md` | `e97a7fb8a2b4227b12f580d2d5c4f0165a44b3763587da9b4de98207b27c1746` |
| `/home/box/shared/quasicrystal-materials/diffraction/chair44-twopoint-lfit-vs-toe-s18-2026-11-07.md` | `51fd3d7c2cd2020540dc85b2ad2effe7b678eba9dff107a58e6c63af5d766329` |
| `/home/box/shared/quasicrystal-materials/diffraction/chair44-twopoint-lfit-2026-11-07.md` | `146f22c771c847180208b038d18406c092ac1b687f9fa6f2310e677e937b6450` |
| `/home/box/shared/quasicrystal-materials/diffraction/tables/chair44_L64_twopoint_lfit.json` | `f21fcff3350213ad7fcdbf728199e1302b9db45ce5b3cea87bad92ba7b085280` |
| Chair44 stored planes.npz (unchanged) | `46f94f916b89fad0f90e42dc0bc5efebde51a1c655f2639b91bfe6c3d8e4f064` |
| leftover pointer `/home/box/shared/theory-of-everything/theorem-f-kato-leftovers-2026-11-06.md` | `481b6e144770e39e0d2bed84a712e12a38d2f01d1d1b2482a37e385c2f4ee20c` (before this amendment's leftover append) |
| preprint `main.tex` (not edited) | `eddbd4ab3d99977888c6af51f0b956111e13cf4d48a01006773d0618197ae626` |
| preprint `claims.csv` (not edited) | `0d83dfd22a0437ae2ad04f289b4a8de0a9ba56b1d36ba6822ecea8972ad3f4cc` |

Board pins: theory-of-everything #862 (plane-mean wording correction),
#870 (independent absorb of Lemma C); lean-lab #866 (LPL result for
#845; file hash `b41f2efa…`, commit `2bd471e7a2a7f70c57fdd840304b4c610038c1da`).

## Status table

| claim | label | what it covers |
|---|---|---|
| Lemma C displayed identity `exp(2 π i [t x + (1−t) y]) = exp(2 π i t (x−y)) exp(2 π i y)` for all real t, x, y | **[P, Lean]** | only `LeanLab.Toe.OrientationPhase.orientationPhase_exp_rewrite` |
| Lemma C follow-on remarks (cannot drop the last factor for D1 centroid y; §2 orientation-channel identity for r = n − s/14) | not Lean-[P] | unformalized in #866 |
| Section 6 Lemmas A, B, D, and E | [P, elementary] in the mechanism note; not Lean-[P] | not formalized in #866 |
| On-grid Dirichlet/sinc leakage of (1/2,1/2,0) or Γ as the source of the observed den-L intensity | **[F]** | via Lemma E, a DFT identity, not a fade inequality |
| Finite-N plane-mean lower bound | **[P, elementary]** | if some non-origin grid point has I_L ≥ c > 0, then Ī_L ≥ c/n_L with n_L = L² − 1 on these full planes |
| Ī_L = Ω(L^{-2}) | conditional only; **not** an unconditional [P] | requires that same c persist at arbitrarily large L (#862) |
| Stored (1/2,1/2,0) peak as a premise for that bound | **[C on patch]** | I32 = 0.9034248259569937, I64 = 0.9034208899704588; two sizes do not prove persistence |
| Observed plane-mean ratio / α ≈ −2 | **[C on patch]** | pixel-count accounting, not a sheet or hull theorem |
| D1 [111] pairing as line selection | **[P, elementary]** | three ⟨110⟩ lines freeze 4 of 8 orientation classes (d · s = 0) |
| (t, t, 1−2t) as a same-type companion of those lines | **[F]** | only 2 of 8 classes freeze |
| (t, 1/2, 1/2−t) as a parallel companion | **[P, elementary]** | same s_x = s_z freeze; equal intensity is not predicted **[X]** |
| Pairing as an L-scaling law, or as a prediction of α = −4 versus −2 | **[X]** | selects lines; does not derive F ~ L versus F ~ L² |
| Structured versus shuffled intensity ratios | **[C on patch]** | compatibility with faster structured fade, not an exponent derivation |
| L^{-4}-like anti-diagonal drop as a prediction | **[X]** | nearest-mark rounding of two stored sizes is descriptive only |
| Fade reading | **[X]** | |
| CH-V-020 | **[X]** | |
| Sheet / hull classification | **[X]** | |
| Theorem F / TOE-PROOF-F / CH-VA-019 | unchanged; not upgraded | unique ergodicity still unverified |
| I-WOLFRAM | **[A]** | |

## 1. Orientation-phase rewrite (lean-lab #866)

I independently hashed the Lean file and the result note and read the
theorem. `orientationPhase_exp_rewrite` matches the displayed identity
in section 6 Lemma C of the mechanism note. LPL reported `lake build`
success and `scripts/axiom_check.sh` OK (only `propext` /
`Classical.choice` / `Quot.sound`), with no `sorry`; the file I opened
contains no `sorry`. I did not rebuild the worktree.

**[P, Lean] covers only that encoded exponential identity.** It does
not bound a fade rate, identify a ridge, or upgrade Theorem F. The two
follow-on sentences in Lemma C, and Lemmas A, B, D, and E, were not
formalized. `ETHTransfer.lean` was reported untouched.

## 2. Plane-mean bound as corrected in #862

The [P, elementary] statement is: at any L whose non-origin plane
contains a peak ≥ c, Ī_L ≥ c/n_L. On these full L by L planes,
n_L = L² − 1, so Ī_L ≥ c/L² would follow for an unbounded family of
L only if the same c persists at arbitrarily large L. That persistence
has not been proved.

#857's shorter wording (“Ī_L = Ω(L^{-2}) [P, elementary], using the
stored peak”) overstated the claim and was corrected in #862. Do not
restore the overclaim.

Independently recomputed from the unchanged stored D1 planes:

- n_32 = 1023, n_64 = 4095, and 1023/4095 = 0.24981684981684982
- I_32(1/2,1/2,0) = 0.9034248259569937, I_64 = 0.9034208899704588,
  ratio 0.9999956432605992
- S_32 = 2.398651087608836, S_64 = 2.3986314914824023,
  S_64/S_32 = 0.9999918303555967
- Ī_32 = 0.0023447224707808757, Ī_64 = 0.0005857463959663986
- r_unif = Ī_64/Ī_32 = 0.24981480890202085

The observed plane-mean α ≈ −2.001069093136654 is [C on patch]
pixel-count accounting (Ī = S/n_L with S nearly L-independent). It is
not a Parseval theorem and not a sheet/hull law [X]. The bound does not
force the ratio 1023/4095 and puts no required mass on the den-L
anti-diagonal. The stored peak has reduced denominator 2, so it lies
outside the den-L plateau mask.

Quasicrystal Materials independently checked this accounting (fold
`51fd3d7c…`): no numerical correction to the L-fit table; they
withdrew “fades like a sheet” without rewriting hashed note
`146f22c7…`; they report S_64/S_32 = 0.9999918303555966 (last-digit
float display only). They agree Ω(L^{-2}) stays conditional.

## 3. D1 pairing is line selection, not a scaling law

Pairing writes F_B(q) = ∑_s exp(−2πi q · s/14) A_{B,s}(q) and selects
the lines on which the orientation phase is t-independent, namely
d · s = 0. That holds for four of eight classes on each of the three
⟨110⟩ lines [P, elementary]. It does not derive an L-power for
|F_B| or I_L, and it does not predict α = −4 on the anti-diagonal
versus α = −2 on the plane mean [X].

On the stored patch, structured plateau r = 0.05494734033155176
(α = −4.185806539052345) and the locked four-pixel same-q mid-line
median r = 0.06362729841650083 (α = −3.974210322999809) both lie
below the in-memory shuffled-plane plateau r = 0.08480766818059603
(α = −3.559661472793319) and the read-only D1_shuffled r =
0.11940186697205887 (α = −3.066102700074652) [C on patch]. That is
compatible with faster structured fade than those controls; it is not
a derivation of F ~ L (rod) versus F ~ L² (sheet). Keep the two
shuffle objects distinct: D1_shuffled is nearest −3 among the disclosed
marks; the in-memory shuffle-then-plateau is nearest −4. Do not
interchange the locked four-pixel same-q median with the earlier
ten-pixel §7 window median 0.057373318522754325.

Lemma D is a finite-N integer-peak bound, not an L-scaling law.
Lemma E already [F]s on-grid Dirichlet/sinc leakage of (1/2,1/2,0)
(or any on-grid dyadic tone) onto other DFT bins, so that peak cannot
supply the anti-diagonal exponent.

## 4. What stays [X] or unchanged

- Fade reading stays **[X]**.
- CH-V-020 stays **[X]**.
- Sheet/hull stay **[X]**.
- The L^{-4}-like drop stays **[X]** as a prediction.
- Theorem F, TOE-PROOF-F, and CH-VA-019 are not upgraded.
- Unique ergodicity remains unverified.
- I-WOLFRAM stays **[A]**.
- Ambient d/I comparison remains not-obtained **[X]**, not [F].
- No L=128; no measured-crystal comparison; no invented intensities.

## Preprint wording if this is later lockstepped

This amendment is a sidecar. Research Publishing should not rewrite
v0.6 or `claims.csv` from it unless a separate owner-facing lockstep
is later decided, and even then:

- If Lemma C is mentioned as Lean-checked, say only that the displayed
  exponential identity is [P, Lean]. Do not describe the follow-on
  geometry remarks, or Lemmas A, B, D, or E, as kernel-checked.
- If the plane-mean bound is mentioned, use the #862 wording
  (Ī_L ≥ c/n_L; Ω(L^{-2}) only if the peak persists). Do not restore
  the #857 overclaim.
- If pairing is mentioned, call it line selection, not a scaling law
  and not a prediction of −4 versus −2.
- Keep CH-V-020 [X] and the fade reading [X]. Do not import live
  `PROOF.md` “verified” wording. Do not fill paper commit-hash or
  software-environment TODOs from live HEAD, and do not use `73d313a`
  or `47477c7` as paper source-snapshot hashes.
- Leave the four pending Chair44 claims.csv cells pending. Do not
  invent author rulings.

No second v0.6 draft is requested by this file. The draft remains
internal and not for external release.
