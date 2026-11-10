# CHANGES-v0.6 (2026-11-07, America/Los_Angeles)

Internal draft only. NOT submitted, NOT published, NOT peer-reviewed, not for external release.
Folds in honesty already landed by Theory of Everything and Quasicrystal Materials. No paper label
changed (counts still [P] 33, [C] 12, [E] 33, [X] 5, [A] 5, [F] 11; 15 label changes; 2 pending).
No new claim IDs, no new ledger IDs, no ledger edits. Frozen `v0.0/`, `v0.1/`, `figs_v1.0/` and
the T1 prereg copies were not touched. A snapshot of the v0.5 working files is in `v0.5/`.

## 1. K4 Lean honesty (ToE note `k4-lean-honesty-2026-11-06.md`, live Cookies `73d313a`, not pushed)

- The v0.5 K4 **paragraph** in §2.2 already matched the ToE note (Lean certifies only the encoded
  finite predicates `octant_bound`, `total_bound`, `bound_attained` in
  `certificates/Phase7Counting.lean`; the file is not in the toe tree; the geometric English is not
  a Lean theorem statement). **That paragraph is unchanged.**
- Real drift found in the K4 **claim text** (`claims_data.py` → `claimdefs.tex`, `claims_table.tex`,
  `claims.csv` short text). It still said "(finite predicate, kernel-checked in Lean)", which is the
  wording ToE removed from the CORE.md K4 evidence cell. Changed to:
  - tex: "… so the connection is never pure gauge. Lean kernel-checks only encoded finite predicates;
    this geometric statement is not itself a kernel-checked Lean theorem."
  - csv short: "forced curvature: >=12 of 21 centre-octant two-cycles non-trivial (Lean checks
    encoded finite predicates only; geometric statement not kernel-checked)"
- K4 stays [P]. Only the short-text cell of K4 changed in `claims.csv`; the id, paper label, source
  label, pending and ledger-id columns are identical to v0.5 for all 99 rows. `claims_flags.tex`,
  `claims_counts.tex`, `label_changes.tex` are byte-identical to v0.5.
- The `.lean` file was not imported. `73d313a` / live HEAD is not used as a source-snapshot hash.

## 2. New paragraph "Computed diffraction checks (outside the framework)" (§2.3, after "What does not fit")

Recorded so the materials runs are not misread; no labelled claim is added to Appendix A.

- **Chair44 at L=64** (QM README Turn 3; `tables/chair44_L64.json` sha256 `b7997ed7…`; prereg
  sha256 `10253440709fbe6dfe9c716d010fa1127e1fb2fb73cb72cbe7079a9435fbb547`). H1 dyadic controls pass
  [C on patch]. H2 (3/16,5/32,1/64) falls, D1 0.0180 / D2 0.0451 printed with stored values
  0.01796463270465118 / 0.045059895785677664 [C on patch]; not a resolved Bragg peak. H3 FAIL at
  (1/3,0,0) ratio 0.2500777662631863 vs locked 0.25; cut not moved. Limit-periodic cubic on
  Z[1/2]^3, not icosahedral; no comparison with icosahedral lists. CH-V-020 stays [X]; unique
  ergodicity still unverified.
- **L=64 q_z=0 streak** (QM's already-landed image; not rerun here; H1–H3 not rerun by QM):
  `tables/chair44_L64_qz0_streak.json` sha256 `705d9d2d84c8a5a304e797e1bf961d95d5fc4433a2dc2bc8543a19fe7995d729`.
  D1 anti-diagonal fades: median 4.21e-6 (L=32) → 2.31e-7 (L=64); median I64/I32 ≈ 0.064
  (p10 0.056, p90 0.53); ~400× above off-diagonal den-64 controls (5.59e-10) [C on patch]. Exact JSON
  values in a footnote. Reading "finite-box feature that fades, not a Bragg or diffuse sheet" is [X]
  and not a hull statement. D2 X-pattern dyadic den ≤ 32 peaks stay (median ratio ≈ 0.855); D2
  den-64 anti-diagonal median ≈ 2.45e-7 [C on patch].
- **New figure** (`fig:streak`): `figs_v0.6/chair44_L64_qz0_streak.png`, byte copy of QM's
  `figures/chair44_L64_qz0_streak.png` (sha256 `446f7757c07502e679e041ff44ad97b23683f76e5925396bc03f28f7f4bc2fb5`).
  Caption: computed [C on patch], not observation, not a measured crystal, not icosahedral, not a
  Bragg peak, no hull claim, CH-V-020 stays [X], not a scored hypothesis. `\graphicspath` gains
  `{figs_v0.6/}`.
- **Multi-window P/F** (QM README Turn 4; `multiwindow_pf.json` sha256
  `d6668b047dcefc95792e6ed6b698c773bf104a4729312360c9bcc23819d84d51`; prereg sha256
  `c8e0a3c0589e3b01b0ce63d2d1d81b3c522463d9df013134d571e1b2f4b83b9f`). Placed on the icosahedral
  cut-and-project side that "What does not fit" leaves outside the framework; stated as independent
  programme work, no Chair44 file used, CH-V-020 untouched, not a Chair44 / E_* / Theorem F
  statement. Assumptions kept [A]. P-type vs Maezawa–Kashimoto–Ishimasa Table 1 [E]: ρ = 0.338
  (stored 0.3378353860555397; geometric 0.336) vs same-run AKN 0.553, H1 FAIL Δ = −0.215 (cut +0.05);
  H2 PASS (70,113) I = 2.27, (6,5) I = 3.28 < 20 [C]. F-type vs Bindi et al. 2011 Table 1 [E]:
  ρ = 0.574 vs 0.603, H3 FAIL Δ = −0.029; H4 FAIL (60,96) I = 66.3 > 20. QM's [X] readings kept [X].
  Newly mentioned window-parameter sources are not named or cited.

## 3. Solomyak [S] scope paragraph (§3.2 "Scope of the cited theorems")

Replaced the Solomyak half with the sharper caveat from `solomyak-S-scope-check-2026-11-07.md` §3 F.
It no longer asserts what the 1997 theorem covers (its body was not opened). Unique ergodicity of
this framed-chair hull remains an unverified input; [S] is not treated as checked [P]; Theorem F /
TOE-PROOF-F stays [P, hand, unverified]. The Wiener cube-versus-ball sentences and the Dunford /
Zygmund sentence are unchanged. The §6.1 "(ii)" sentence is unchanged.

## 4. refs.bib (+3 keys, 27 → 30)

- `maezawa2004zntsc`, `bindi2011icosahedrite`: copied byte-for-byte from the shared verified
  bibliography (Crossref/arXiv-verified 2026-10-31). Cited only as the sources of the transcribed [E]
  powder lists that QM opened; this pass did not re-open them.
- `lee2003consequences` (LMS 2003, DCG 29(4) 525–560, doi 10.1007/s00454-003-0781-z, arXiv
  0910.4450): verified this pass via arXiv API and Crossref; Theorem 4.1 statement read in the arXiv
  PDF. Cited only for that theorem's statement; explicitly does not check [S] or this hull.
  `dynamics97.pdf` not cited. Kato not added.

## Locked / unchanged

G2 Part A self-energy sentence (no verified C/β reference) unchanged; TOE-G2-D1, G2A-SELFENERGY stay
[E]. I-WOLFRAM stays [A]. CH-V-020 [X]. Kato unwired. All author, third-party-repo, Lean-audit label,
K5-split, D2, G6-O2, G1-RARE, G2B-DERIV, commit-hash and software-environment TODOs left as TODOs
(10 red TODOs). No live-HEAD hashes. `/workspace/apply_v02.py` not run. No excluded-lineage or
confidential material.

## Build

`python3 build_claims.py` then `latexmk -pdf`: exit 0, 35 pages (v0.5: 32; +3 from the new
paragraph, footnote and full-width figure), no errors, no undefined references or citations, BibTeX
0 warnings. CreationDate Sat Nov 7 08:14:07 2026 PST.

| file | sha256 |
|---|---|
| `main.tex` | `eddbd4ab3d99977888c6af51f0b956111e13cf4d48a01006773d0618197ae626` |
| `main.pdf` | `9b016160d256f38dc6953ecd77a34a2006887ca9530dc1e64cce8b2be6b76e0d` |
| `claims.csv` (K4 short text only) | `0d83dfd22a0437ae2ad04f289b4a8de0a9ba56b1d36ba6822ecea8972ad3f4cc` |
| `refs.bib` (+3 keys) | `cee840b3bced28ec4266ec28b5f4f5b19ed42d32539780194fcf8cfc7da97e59` |
| `claims_data.py` (K4 text only) | `6cc9683ed1041fc46153e2581be744e4b0d426caa68c44c2b5e879680db1a076` |
| `figs_v0.6/chair44_L64_qz0_streak.png` | `446f7757c07502e679e041ff44ad97b23683f76e5925396bc03f28f7f4bc2fb5` |

Still not for external release.
