# Unification-programme preprint, draft v0.6 (internal, not submitted)

**Status: internal draft v0.6 (2026-11-07 PT). NOT submitted, NOT published, NOT peer-reviewed. NOT READY FOR EXTERNAL RELEASE.** v0.6 folds in already-landed honesty: K4 claim text now says Lean checks only encoded finite predicates (K4 stays [P]; the v0.5 K4 paragraph was already correct and is unchanged); a new §2.3 paragraph and Figure `fig:streak` record the Chair44 L=64 computed diffraction and QM's q_z=0 streak image as [C on patch] (CH-V-020 stays [X]) and the multi-window P/F tables as independent work outside the framework; the Solomyak scope paragraph carries the 2026-11-07 [S] caveat (unique ergodicity still unverified; LMS 2003 cited for its statement only). No paper label changed. See `CHANGES-v0.6.md` and `v0.6-wording-constraints-2026-11-07.md`. The v0.5 working files are snapshotted in `v0.5/`.

## Hashes (v0.6)

| file | sha256 |
|---|---|
| `main.tex` | `eddbd4ab3d99977888c6af51f0b956111e13cf4d48a01006773d0618197ae626` |
| `main.pdf` (35 pages) | `9b016160d256f38dc6953ecd77a34a2006887ca9530dc1e64cce8b2be6b76e0d` |
| `claims.csv` (K4 short text only) | `0d83dfd22a0437ae2ad04f289b4a8de0a9ba56b1d36ba6822ecea8972ad3f4cc` |
| `refs.bib` (30 keys: + maezawa2004zntsc, bindi2011icosahedrite, lee2003consequences) | `cee840b3bced28ec4266ec28b5f4f5b19ed42d32539780194fcf8cfc7da97e59` |
| `claims_data.py` (K4 text only) | `6cc9683ed1041fc46153e2581be744e4b0d426caa68c44c2b5e879680db1a076` |
| `figs_v0.6/chair44_L64_qz0_streak.png` (copy of QM figure) | `446f7757c07502e679e041ff44ad97b23683f76e5925396bc03f28f7f4bc2fb5` |

Compile: latexmk exit 0, 35 pages, no undefined references or citations.

---

Historical v0.5 header follows.

Author: Research Publishing (bot) for Joey D. v0.5 built 2026-11-06 (PST) by closing three prose TODOs that could be finished from files: the K4 Lean file and theorem names with a statement-scope caveat, the [S] novelty-note scope check, and Phase summaries that omit excluded-lineage material. Paper labels and `claims.csv` are unchanged from v0.4. Nothing has been pushed, published or submitted. The v0.1 snapshot is unchanged in `v0.1/`; the v0.0 skeleton remains in `v0.0/`. See `CHANGES-v0.5.md` for this pass, `CHANGES-v0.4.md` for the ledger-id lockstep, `CHANGES-v0.3.md` for the T1 and cite-TODO pass, `CHANGES-v0.2.md` for the owner first pass, and `CHANGES-v0.1.md` for the previous draft.

> **Release-readiness update (2026-11-06 PST): NOT READY FOR EXTERNAL RELEASE.** Draft v0.5 closes the K4 Lean-name TODO (with a statement-scope caveat), the [S] scope-check TODO, and the Phase summaries TODO. Kato stays unwired. Leftovers that still block any public or external use include the Kato cite-TODO, author and commit metadata, and a possible later G6-O2 relabel.

## Files

| file | what |
|---|---|
| `main.tex` | the paper; every labelled claim enters via `\useclaim{ID}` |
| `main.pdf` | compiled output (32 pages; v0.4 and v0.3 were 31; v0.2 was 30) |
| `refs.bib` | 27 cited entries copied from the verified bib (15 from v0.2 plus 12 owner-approved cite-TODO keys; Kato not added) |
| `claims_data.py` | all 99 labelled claims. The source label (`label`) is never edited; paper labels may be weaker. v0.2 adds FIG5-ESTAR as paper [E] and a short-text revision for the outward enclosure |
| `build_claims.py` | generates claims.csv, claimdefs.tex, claims_table.tex, claims_flags.tex, claims_counts.tex, label_changes.tex (Appendix C) |
| `claims.csv` | id, paper label, source label, pending marker, ledger id, short text, evidence pointer |
| `build.log` | last latexmk log |
| `v0.0/` | the skeleton as it was before v0.1 |
| `v0.1/` | unchanged snapshot of draft v0.1 |
| `CHANGES-v0.1.md` | what changed in v0.1, per referee issue |
| `CHANGES-v0.2.md` | lockstep application of the 2026-11-06 owner first pass |
| `CHANGES-v0.3.md` | T1 scoped wording and owner cite-TODO wiring |
| `CHANGES-v0.4.md` | ledger-id fill from the 2026-11-06 owner ledger sync |
| `CHANGES-v0.5.md` | K4 Lean names, [S] scope check, and Phase summaries |
| `CHANGES-v0.6.md` | K4 claim-text honesty, computed-diffraction paragraph and figure, [S] caveat |
| `v0.6-wording-constraints-2026-11-07.md` | constraints for Theory of Everything and Quasicrystal Materials |
| `v0.5/` | snapshot of the v0.5 working files |
| `figs_v0.6/` | QM streak figure copy used by v0.6 |
| `owner-first-pass-2026-11-06.md` | Theory of Everything's science-owner mark-up (does not edit pinned artifacts) |
| `owner-cite-todos-2026-11-06.md` | sentence-level cite-TODO marks (not a fresh page-by-page re-read) |
| `owner-ledger-sync-2026-11-06.md` | Theory of Everything's ledger/scorecard sync (Cookies `7e6a508`) |

## Historical hashes (v0.5)

| file | sha256 |
|---|---|
| `main.tex` | `dba09b3a5415fdded82cce8187df11ff64a053f4890a36c09c9d9882656d2e5c` |
| `main.pdf` | `c5c46bfa25b99c5b8f39626d17f57b308dd778da886eeb850c141e9fde9580bb` |
| `claims.csv` (unchanged from v0.4) | `d54beaef4d70848b2b31fb75d4c08986e912b9d961d2aad7caa6f98a2f19296f` |
| `refs.bib` (unchanged from v0.3) | `1fa341add231635a81f3265b3702843efc24a85d494af305fe1af20165d4b366` |
| `claims_data.py` (unchanged from v0.4) | `1dda19e495aebd6f8bab03f5b94fc14e5ca8389383860610f13a838989bd277e` |

Historical Draft v0.4 hashes:

| file | sha256 |
|---|---|
| `main.tex` | `8366dc906d3107f280706cffc472ae998831ee93c312056c0159260a8879032d` |
| `main.pdf` | `0e36b60cbe7de59f4ac92f38c5265b4c7525ad14dffe888d0bd0ac346c483e2c` |
| `claims.csv` | `d54beaef4d70848b2b31fb75d4c08986e912b9d961d2aad7caa6f98a2f19296f` |
| `refs.bib` (unchanged from v0.3) | `1fa341add231635a81f3265b3702843efc24a85d494af305fe1af20165d4b366` |
| `claims_data.py` | `1dda19e495aebd6f8bab03f5b94fc14e5ca8389383860610f13a838989bd277e` |
| `figs_v0.2/fig5_Estar_FR30_enclosure.pdf` (unchanged) | `65ff3b9c6a1c6288ca8568dd14219ada3d993d28c8e82fcab7a1d38350b42960` |
| `owner-ledger-sync-2026-11-06.md` | `d49ec6c5416a3e94d11cb79b618822252dc53d3ac60a67fe75de273988c92026` |
| `owner-first-pass-2026-11-06.md` | `e01165543f08f5b788d268abf6cfd2b3f7296fcc146f0a3138a8872b7294a30d` |
| `owner-cite-todos-2026-11-06.md` | `91c0f58e7bc958b0b9e32dccdbecd30aaf902aa1d1e693f59dd6e7a9bde450c8` |
| T1 amendment `T1_scorer_robustness_2026-11-06.md` | `106b756ebc6eea22021ef615dea83c2060b7ede9aa1c7d4689c41c7ab5e9ee96` |

Historical Draft v0.3 hashes:

| file | sha256 |
|---|---|
| `main.tex` | `49591ef1159c03a7f9556927e7e2348ac110076f7e4ba4337c51b878bb836705` |
| `main.pdf` | `6d53916d48895f5413fba4475730db3d6ea2a77566ed8affec91672a78f86679` |
| `claims.csv` | `53da5fbf3e14eae18bf83bdca00521a791df8ff97c47153733ff900287653d95` |
| `refs.bib` | `1fa341add231635a81f3265b3702843efc24a85d494af305fe1af20165d4b366` |
| `claims_data.py` | `8fdde6762cdd8abdfc9fe0f8464ac99c044e3cf6d3c2f48ae5eb4ce68f8dc6c6` |

Historical Draft v0.2 hashes:

| file | sha256 |
|---|---|
| `main.tex` | `8f222301c7810ec2c28dc6485e853ec93d4decbfab48493cb7d4cbbfcf06b9e3` |
| `main.pdf` | `ddb36829b9e9aed0273018ea26fd44f248ac25d6bb830a3117aa22b02bfe61b8` |
| `claims.csv` | `53da5fbf3e14eae18bf83bdca00521a791df8ff97c47153733ff900287653d95` |
| `refs.bib` | `63bd10fde224401447dcda9fb3f992a872e281908169dcba644957e0e7ae7055` |

Historical Draft v0.1 hashes (also snapshotted in `v0.1/`):

| file | sha256 |
|---|---|
| `main.tex` | `4cc48eafbed24cf0f3db8c64c1a9b532e92ee03429c8d78fff9221edc618af53` |
| `main.pdf` | `847fa355c96b33a7aec594a108da362c8b95dc989aded2a696fe5f895f627e78` |
| `claims.csv` | `0d9724e17b9e8439bbc4795a700f46774033b130dd913b0c29755539f2d01281` |
| `refs.bib` | `181e97f3229437b0c1a1d31fe690bae6c6bbc492ea6410b17bfaac1d28c5fb25` |

## Provenance (sha256)

Source documents were read from a snapshot at `/workspace/toe-repo-head/head/` (not a git checkout, so **the toe repository commit is unknown**).

| file | sha256 |
|---|---|
| `/workspace/toe-repo-head/head/TOE_ATTEMPT.md` | `2bb543b04624d72ae0a1a88614055ff6c09a06ba8d004440db5d3833a14b0603` |
| `/workspace/toe-repo-head/head/PROOF.md` | `dd992292fa9ca6c941f41acd84b67e601f15dd20a3172d902bdbd8c19fc30e0d` |
| `/workspace/toe-repo-head/head/CORE.md` | `cf1d5fd53e03d15615159402be1e76fb2736f08d83f020566e883b73ab29d1a5` |
| `/workspace/toe-repo-head/head/SCORECARD.md` | `9aafae111c111ad99a084f7dbbf1529ac4bce394e06e7560e8a4252c2337fdeb` |
| `/workspace/toe-repo-head/head/README.md` | `4f13ca6bbbca202b3e1a80eeb026d3089ccb5a7b398acd642f885de0f3cd7e9d` |
| `/workspace/toe-repo-head/head/ledger.json` | `46388050ac02faf9bb962adc47e7787646032564c3eaefc9e1fa720eea355730` |
| `/workspace/ledger/discrepancies.md` | `9417e835e3bce5f24209f1f58d6fdc08110d514975deec69d7d409d230886718` |
| `/home/box/shared/bibliography/bibliography.bib` | `53834922c0484682e5bc63e31b4ad49ceeb680d6f1a478388efb0663c9217d9b` |
| `/home/box/shared/research-publishing/figures/proof-brackets/README.md` | `44831fe9631e4b98786c1845426ac7fd4a4a5e2b46e61bf73c5dd7729acd9035` |
| `/home/box/shared/research-publishing/referee-checklist.md` | `26032dcc8fb2b1583e983afab922590c086a15c5e92ff647333ac9217059844d` |
| `/home/box/shared/research-publishing/figures/proof-brackets/figs_v1.0/fig1_mu_nu_vs_level.pdf` | `657fb00b27e31804257bf0a7651ab003ad62857e0f4d0e3540b57f606b5f40ac` |
| `/home/box/shared/research-publishing/figures/proof-brackets/figs_v1.0/fig2_bracket_widths.pdf` | `2b736bbd03a44c1905f129734ff76fea851ed857480662a28411ab91a9fdc8cb` |
| `/home/box/shared/research-publishing/figures/proof-brackets/figs_v1.0/fig3_limit_brackets.pdf` | `95cf92330966ddf67d1459203f13c3bc2554199ef2b52d1e8616d1ed6d2d6282` |
| `/home/box/shared/research-publishing/figures/proof-brackets/figs_v1.0/fig4_rounding_audit.pdf` | `6e5e64b9a6a36718cc3caf08fc2cd23c02420d3dc5cf23c6c47be9ff6cb622d2` |
| `/home/box/shared/research-publishing/figures/proof-brackets/figs_v1.0/fig5_Estar_FR30_enclosure.pdf` | `67c72d28d5df9c546dbb0d258c48cfeed147506d15c51cc7ec004bb932828654` |

Figures 1--4 in `figs_v0.2/` are byte-identical copies of frozen `figs_v1.0/` (hashes unchanged). Figure 5 was rebuilt with `make_figures.py --paper` from `brackets_v1.0.json` for the outward [E] enclosure. The paper includes them through `\graphicspath{{../figures/proof-brackets/figs_v0.2/}}`. `checksums.sha256` lists both sets.

## How to build

```bash
cd /home/box/shared/research-publishing/toe-preprint
export PATH=$HOME/.local/bin:$PATH   # TinyTeX
python3 build_claims.py              # not `python3 -I` (that drops cwd from the import path)
latexmk -pdf -interaction=nonstopmode main.tex
```

Compile status: **OK**. latexmk exit 0, 32 pages for v0.5 (v0.4 and v0.3 were 31; v0.2 was 30), no errors, no undefined references or citations. Underfull hboxes remain in the claims table; no overfull hboxes.

## Label counts (99 labelled claims)

| label | before (v0.0, label as in source) | after (v0.1, paper label) | after (v0.2, paper label) |
|---|---|---|---|
| [P] | 34 | 33 (32 hand proofs tagged "unverified"; K4 rests on Lean) | 33 |
| [C] | 15 | 13 | 12 |
| [E] | 26 | 32 | 33 |
| [X] | 2 | 5 | 5 |
| [A] | 5 | 5 | 5 |
| [F] | 11 | 11 | 11 |
| [P+C] | 2 | – | – |
| [P/C] | 1 | – | – |
| [P-level] | 1 | – | – |
| [P-level estimate] | 1 | – | – |
| [E, post hoc] | 1 | – | – |

15 claims have a paper label different from the source label (Appendix C). None is stronger than its source label. The extra change in v0.2 is FIG5-ESTAR, paper [E] against source [C]. Drafts v0.3 and v0.4 did not change paper labels. Draft v0.4 filled 33 previously empty ledger-id cells with the paper id (owner ledger sync, Cookies `7e6a508`); no ledger-id cell is empty. 2 claims carry "pending" markers: G1-RARE and G2B-DERIV ("label pending author ruling"). FIG5-ESTAR no longer carries a pending marker.

Correction to the v0.0 README: it said the two non-standard labels were "G1-RARE [P-level estimate] and G4-O1 [P-level]". In fact they are G1-RARE [P-level estimate] and **G2B-DERIV** [P-level]. G4-O1 is [P].

## Excluded items skipped

- The ledger has 332 excluded entries: 327 from Phase 0 and 5 Phase 3 [F] verdicts.
- Of these, **161 ledger entries belong to the EXCLUDED lineage named in the task**. They were skipped, and the 2 CORE.md §3 rows marked EXCLUDED were skipped as well, so **163 items** were skipped in total.
- The Phase 0 summary in TOE_ATTEMPT.md also refers to the excluded lineage. Those passages are not reproduced, and neither is the excluded example in the Lean-audit paragraph at l.34.
- The remaining excluded entries are [F] or retracted claims. The relevant ones appear in the draft with [F] and are never used as support.

## Open TODOs (red in the PDF): 10

Closed in v0.5: K4 Lean file/theorem names, with the caveat that the geometric English is not itself a Lean theorem statement; [S] scope check (still unverified, not newly checked [P]); Phase summaries (excluded-lineage passages not reproduced).

Prose and author input:
1. author list and affiliations
2. confirm that no repository counted in the ledger contains third-party results
3. labels for the Lean-audit facts (ledger owner)
4. split K5 into a [P] equivalence and a [C] computation (author)
5. label for D2 (author; no stronger than [X])
6.–8. toe commit and prereg commit hashes with timestamps (three places)
9. software environment of the original runs

Closed as documented gaps rather than new citations: Wiener (cube-versus-ball form remains unverified; Dunford/Zygmund not cited) and Dorodnyi (reworded without a bibliography key).

Cite TODOs: 1 (Kato, listed below).

## Cite requests

Still unwired (owner: NOT CHECKABLE; do not add):

- T. Kato, Israel J. Math. 13 (1972) 135, doi:10.1007/BF02760233 (K14)

Still not cited:

- F. Bruckmann, E.-M. Ilgenfritz, Phys. Rev. D 72 (2005) 114502 — dropped from the G2 Part A self-energy sentence; not cited and not replaced
- G. C. Papanicolaou, S. R. S. Varadhan (1981) and A. Bourgeat, A. Piatnitski (2004) — still not cited (owner: drop until verified)
- M. Dorodnyi, arXiv:2005.06516 — described in prose without a bibliography key (periodic homogenisation, including magnetic examples; does not cover the substitution hull)
- Nielsen--Ninomiya 1982 erratum — not cited; omitted from this draft's bibliography listing

Cited from the verified bib (27): the 15 v0.2 keys plus wilson1974confinement, nakamura2000lifshitz, luscher1977transfer, osterwalder1978gauge, nielsen1981absenceI, nielsen1981absenceII, kaplan1992chiral, witten1982su2, regge1961coordinates, ambjorn2004emergence, minami1996local, petcher1980montecarlo. Each of the twelve added keys is scoped to the clause in `owner-cite-todos-2026-11-06.md`. KogutSusskind1975 and DeserJackiwtHooft1984 remain in the shared bibliography unused. Kennedy is cited only for the heat-bath sampler.

## Checklist self-check (referee-checklist.md v1.1)

Current internal mock referee report: `../referee-reports/toe-preprint-v0.5.md` (2026-11-06, report dated ~10:10 PM PT): **Major revision; 11/43 MUST unresolved**, not real peer review. The report pins the 32-page v0.5 PDF at the hash above. Theorem F and its unique-ergodicity input remain unverified; this pass did not re-open every bibliography PDF, re-run `proof_bounds.py`, or re-diff the live owner ledger. No external-release upgrade follows.

Historical v0.1 authoring-bot self-check (not the current v0.5 referee count): **15 of 43** open MUST items (v0.0: 28 per the mock referee). The table and v0.1 closure list below preserve that earlier assessment; later deltas follow.

| § | v0.0 | v0.1 | open in v0.1 |
|---|---|---|---|
| §0 | 2 | 2 | toe commit and authors; Notion and ledger entries not linked (Notion off-limits) |
| §1 | 7 | 1 | [C] items lack commit and output log (scripts and results files are named) |
| §2 | 0 | 0 | – |
| §3 | 3 | 1 | cited statements not re-checked by me against the 4 sources (bib metadata verified via Crossref by the librarian) |
| §4 | 7 | 6 | code commit; data versions; environment; headline rerun log not attached and 1387 ℓ=6 not rerun; no `lake build` log; K4 Lean names now recorded, with the statement-scope caveat that the geometric English is not a Lean theorem |
| §5 | 3 | 2 | the ledger is not updated for the 14 label changes and the unmapped claims; new claims are not added to the ledger (I cannot edit it) |
| §6 | 2 | 0 | – |
| §7 | 4 | 3 | uncertainty is partial (no error on G3 R3c m_eff); prereg freeze order not verifiable without commits; fits: range, model and range sensitivity are reported, and the 3-point fit has no goodness-of-fit statistic by construction. Counted open until the referee accepts that |

Closed in v0.1: one label per claim from the six; hand proofs tagged unverified; overstated labels downgraded (14); wording ("floating point", conjectures as [X]); abstract scoped; Novelty note referenced (§sec:relwork) and missing homogenisation prior work flagged; seeds, parameters and run counts (Appendix D); figure captions (what is plotted, error bars, tolerance); no claim stronger than the ledger (TOE-PROOF-D now [C]); physics readings [X]/[A]; precision and tolerances stated.

Closed or narrowed in v0.2 (owner first pass, not a full re-score of the 43 MUST items): homogenisation prior work is now cited with wording caveats rather than flagged as missing; FIG5 paper label and printed interval match the outward enclosure; Bruckmann is no longer an unsupported citation; Dorodnyi wording no longer says "non-magnetic"; paper, PDF, figures, and `claims.csv` are back in lockstep. §3 is not marked closed: the newly wired sources follow the owner's first-pass notes and the earlier cite-support audit, not a fresh page-by-page re-read of every PDF.

Closed or narrowed in v0.3: eight of the nine remaining cite-TODOs are wired with owner caveats; T1 scope wording is in the G6 section. §3 is still not marked closed (same reason). Kato remains a cite-TODO.

Data issues found (for the ledger owner; source files unchanged):
- discrepancies.md §2.3 calls the ledger's 7.954292 safe. It is above the 7.954291278 certificate, so the paper prints 7.954291.
- The ledger copies disagree: 1288/332 (toe head) vs 1272/324 (read-only copy). Footnoted in §2.
- The figs_v1.0 legends show source labels. Paper figures 1--4 reuse those frozen files; figure 5 in `figs_v0.2/` is labelled [E] and uses the outward print.

## Confidentiality and exclusions

INVENTORY.md was not opened. Excluded-lineage and restricted-material terms were grepped in all outputs (main.tex, the generated .tex files, claims.csv, claims_data.py, refs.bib, README.md, CHANGES-v0.1.md, CHANGES-v0.2.md, CHANGES-v0.3.md, and the pdftotext of main.pdf): 0 hits. Neither is named in the paper.
