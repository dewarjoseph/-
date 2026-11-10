# Unification-programme preprint, draft v0.6 — release note

This folder is a byte-identical copy of the frozen v0.6 draft. Nothing in it was edited for publication.
Its own `README.md` still says "internal draft, NOT submitted, NOT peer-reviewed"; that remains true.
Publishing it here makes the draft readable. It does not mean it has been submitted or refereed.

The draft still has open `[TODO: …]` placeholders, including the author list, some preregistration commit hashes and a Kato citation.
They are left in place on purpose, so the record shows what is still unfinished.

## Frozen files (sha256)

| file | sha256 |
|---|---|
| `main.tex` | `eddbd4ab3d99977888c6af51f0b956111e13cf4d48a01006773d0618197ae626` |
| `main.pdf` (35 pages) | `9b016160d256f38dc6953ecd77a34a2006887ca9530dc1e64cce8b2be6b76e0d` |
| `claims.csv` | `0d83dfd22a0437ae2ad04f289b4a8de0a9ba56b1d36ba6822ecea8972ad3f4cc` |
| `refs.bib` | `cee840b3bced28ec4266ec28b5f4f5b19ed42d32539780194fcf8cfc7da97e59` |

## Build

`main.tex` reads figures from `../figures/proof-brackets/figs_v0.2/` (Figures 1–5) and `figs_v0.6/` (the streak figure).
Both folders are included at those relative paths.
`latexmk -pdf main.tex` run in this folder gives 35 pages with no undefined references.
`build_claims.py` regenerates `claims.csv` and the `claims_*.tex` / `claimdefs.tex` / `label_changes.tex` includes from `claims_data.py`.

## Notes on provenance comments

Some comments and older changelogs name internal working paths (`/home/box/...`) or a local machine name.
They are kept verbatim so that the frozen hashes still match, and they point to private working copies, not to files in this repository.

## Labels

[P] proved · [C] certified or computed (scope is stated, e.g. "on patch") · [E] evidence: numerical or simulated, and real measurements when marked "(measured)" · [X] conjecture or open · [A] analogy only · [F] falsified.
[S] marks a step taken from a cited source that has not been re-checked here.
A claim is never printed stronger than its source label.
