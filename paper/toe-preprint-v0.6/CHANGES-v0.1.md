# Changes v0.0 → v0.1 (toe-preprint)

Date: 2026-11-01 (PST). Responds to `referee-reports/toe-preprint-skeleton.md` (mock, Reject) and `novelty/theorem-F-novelty.md` (PARTIAL). The source files are unchanged. The `label` field in claims_data.py is never edited. v0.0 is in `v0.0/`; use `diff -r v0.0 .` to compare.

## Major 1: Theorem F, novelty and homogenisation
- Theorem F (TOE-PROOF-F) is now presented as an application of standard ergodic homogenisation. It cites solomyak1997dynamics, solomyak1999corrections, wiener1939ergodic and hancheolsen2010kolmogorov.
- New subsection "Related work: homogenisation and Theorem F" (`sec:relwork`). It references the novelty note by path and gives its PARTIAL verdict. It lists Kozlov, Papanicolaou–Varadhan, Künnemann, Owhadi, Bourgeat–Piatnitski, Braides–Riey–Solci, Telcs, Bartha–Telcs, Biskup 2011/2025 and Conca–Vanninathan ([A]), all as cite TODOs with DOIs.
- What is specific to this work: Perron-weighted pinned supertiles, a deterministic limit along T_L via unique ergodicity, and the θ² link. No rate is proved.
- The E brackets (TOE-PROOF-E-FR30/1387, Table, Fig. 3) are stated as [C] conditional on Theorems B, C, F [P, hand proof, unverified]. The same conditioning appears in the abstract.
- "Not claimed new" wording replaces the novelty claims. The novelty bullets were rewritten.

## Major 2: labels
- Only the six standard labels are printed. The paper label is stored separately from the source label, and the generator refuses any upgrade.
- 14 changes, listed in the new Appendix C "Label changes vs. source" (14 rows):
  - K6 [P/C]→C
  - K10 [P+C]→C
  - TOE-PROOF-D [P+C]→C (matches the ledger)
  - G1-RARE [P-level estimate]→X (pending)
  - G2B-DERIV [P-level]→E (pending; superseded by Theorem A)
  - G2B-POSTHOC [E, post hoc]→E
  - TOE-G2-B0 C→E
  - TOE-G5.1–5.4 C→E (floating point, no interval control)
  - G2B-LIMIT E→X
  - G2B-MASS E→X (reworded as conjectures)
  - TOE-G2-D1 P→E
- FIG5-ESTAR keeps [C] with the marker "pending ratification of Phase IX mapping".
- The non-standard \defclaimcolor entries were removed and a \pendingtag macro was added.
- The scorecard rows 3 and 4 were relabelled, with a caption note.
- Counts: P33 C13 E32 X5 A5 F11 (99).

## Major 3: rounding
- Table tab:munu now prints outward-rounded values (floor for lower bounds, ceil for upper bounds). Footnote a gives the ten PROOF.md printed values. Footnote b covers 15.465590 (PROOF.md) vs 15.465589 (ledger): both are safe, and the rerun gives 15.4655889035….
- The E_*(FR30) enclosure is printed as [7.954291, 8.7642270382]. The ledger printed [7.954292, 8.7642270381]; its lower end is above the 7.954291278 certificate and its upper end is truncated. Both are explained in the Fig. 5 footnote and in Appendix C, "Printed values changed".
- The headline brackets are unchanged: [13.232574, 15.465590] and [14.161980, 16.390966].
- New paragraph: the certified numbers rest on floating point plus the rounding lemmas, not on interval arithmetic.

## Major 4: physics wording and over-generalisation
- In the abstract, "continuum limit is a free massive field" becomes: "mass term [E]; the continuum limit itself is [X]".
- New "Reading [X]" paragraph in G2 Part B. It gives an alternative reading (an inert lattice / pre-asymptotic effect).
- G1: the extrapolation to ≈14 is marked as unlabelled and non-preregistered, and is refuted by T3.
- The l=7 result appears only as a provisional remark: [C] with the marker "PROVISIONAL: uncommitted run, rounding direction unverified". It is not used for the headline.

## Major 5: citations
- Added solomyak1999corrections, copied verbatim from the verified bib. refs.bib now has 4 entries.
- Everything else stays as `\todo{cite: …}` with DOIs where known: 15 cite TODOs. The full list is in README.md.

## Major 6: reproducibility
- New Appendix D: file hashes, and a table of seeds, parameters and run counts.
- New Table tab:R: G2 A R±SE with seeds, chains and sweeps from results/g2_score.json. G3 R2 standard errors come from results/g3_score.json (20,000 measurements per run).
- Solver tolerances are stated: CG rtol 1e-12 for c_L, eigsh tol 1e-13 for G5.
- For G2B-CL, extrapolation range sensitivity is given: (c3,c4,c5) gives 13.463 / 14.322, so the value moves by 0.10 / 0.04. A 3-point fit is exact, so there is no goodness-of-fit statistic.
- The internal reruns (2026-10-31) are recorded; 1387 at ℓ=6 was not rerun.
- Still TODO: toe commit and prereg commits, and the software environment.

## Major 7: ledger consistency
- claims.csv gains ledger-id, source-label and pending columns.
- The 1288/332 vs 1272/324 ledger-copy discrepancy is footnoted.
- Still open: ledger reconciliation and adding the unmapped claims (ledger owner).

## Other edits
- Written prose: introduction and roadmap, the object (CORE.md §1), the T3 proof (TOE_ATTEMPT.md l.93), "What does not fit", Falsification routes, "Where it stands", the Lean audit record, and a scope paragraph for the cited [S]/[W] theorems.
- Figures now come from figs_v1.0 (byte-identical to v0.0 figs). The Fig. 1, 3 and 5 captions were rewritten: the Fig. 3 stars are [X], the dashed line is [C], and the CG tolerance is stated. The provenance paths were updated.
- Fixed the README misattribution: the [P-level] claim is G2B-DERIV, not G4-O1.
- Corrected the Dorodnyi initial to M. (per TOE_ATTEMPT.md l.351).
- Overfull hboxes: 0 (v0.0 had 1).
- Peer Review Critic TODO removed from the abstract.

## Not done
Phase summaries are left as a TODO, because the Phase 0 summary mixes in excluded-lineage material. There is no ledger edit, no bot messages and no Notion; the figure legends are not changed.
