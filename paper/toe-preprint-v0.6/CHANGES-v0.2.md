# Changes in Draft v0.2 (6 November 2026)

Lockstep application of Theory of Everything's science-owner first pass
(`owner-first-pass-2026-11-06.md`). The v0.1 snapshot in `v0.1/` was not
overwritten. Frozen `figs_v1.0/` hashes are unchanged.

This draft is **not ready for external release**.

## Applied owner marks

1. Dropped Bruckmann from the G2 Part A self-energy sentence. No replacement
   weak-coupling $C/\beta$ reference was inserted. Kennedy 1985 is cited only
   for the heat-bath sampler.
2. Solomyak 1997/1999 and Wiener 1939 remain documented unverified inputs, not
   newly checked [P]. Unique ergodicity of the hull and the cube-versus-ball
   form of the ergodic input are restated as gaps at Theorem F.
   Dunford/Zygmund 1951 is not cited.
3. FIG5-ESTAR paper label is [E] (source remains [C]; Phase IX mapping
   unratified). The printed enclosure is the outward interval
   $[7.954291, 8.7642270382]$. The truncated ledger/CSV print $8.7642270381$
   is unused because it lies strictly below the exact rational upper bound.
   The owner re-checked the outward arithmetic [C]; this note does not
   re-derive the certificates.
4. Homogenisation keys copied into `refs.bib` from the shared bibliography and
   wired with the owner's wording caveats:
   `kozlov1987difference`, `kunnemann1983diffusion`, `kozlov1980averaging`,
   `owhadi2003periodization`, `braides2009penrose`, `telcs2010penrose`,
   `bartha2013penrose`, `biskup2011survey`, `biskup2025deterministic`,
   `conca1997bloch`, and `kennedy1985heatbath`.
   Not added: `bruckmann2005laplacian`, `dorodnyi2020operator`,
   Papanicolaou--Varadhan, or Bourgeat--Piatnitski.
5. Dorodnyi 2020 is described without a bibliography key: periodic
   homogenisation including magnetic examples; it does not cover the
   substitution hull. The earlier "non-magnetic" wording is gone.
6. G6-O1 is described as elementary geometry of the static complex
   ([P, hand, unverified]), not as T1 "no local moduli". G6-O2 remains a
   one-line TOE_ATTEMPT remark; its [P] label is unchanged pending a possible
   later owner relabel.

## Figures

- Graphic path: `../figures/proof-brackets/figs_v0.2/`.
- Figures 1--4 are byte-identical copies of frozen `figs_v1.0/`.
- Figure 5 rebuilt with `make_figures.py --paper` from `brackets_v1.0.json`:
  title [E], interval $[7.954291, 8.7642270382]$, zoom contrasting the unused
  ledger print against the exact rational bound and the paper's outward
  10-decimal print.

## Claims table

- `claims_data.py` `LABEL_CHANGES` now includes FIG5-ESTAR as paper [E].
- `SHORT_REVISIONS` updates the CSV short text to the outward interval.
- Regenerated: `claims.csv`, `claimdefs.tex`, `claims_table.tex`,
  `claims_flags.tex`, `claims_counts.tex`, `label_changes.tex`.
- Paper counts: [P] 33, [C] 12, [E] 33, [X] 5, [A] 5, [F] 11.
- 15 paper labels weaker than their source labels (was 14). Pending markers:
  2 (G1-RARE, G2B-DERIV). FIG5 no longer carries a pending marker.

## Compile

- `latexmk -pdf`, 30 pages, no errors, no undefined citations.
- Bibliography: 15 cited keys (the four from v0.1 plus eleven newly wired).

## Not done in this revision

- Ledger downgrades (Theory of Everything).
- Dated T1 amendment (Theory of Everything; separate Notion row).
- Possible later G6-O2 scope or relabel (Theory of Everything; this draft
  does not change the label).
- Remaining cite-TODOs: Kato; Wilson; Nakamura (two places);
  Lüscher/Osterwalder; Nielsen/Ninomiya, Kaplan, Witten; Regge/Ambjørn;
  Minami; Petcher.
- Author list, commit hashes, software environment, Phase 0--3 prose,
  [S] scope check, Lean-audit labels, K4 statement check, K5 split, D2 label.
- Paywalled re-reads not requested in the first pass.
- Day-14 target remains preprint v0 by 14 November 2026.

## Hashes (sha256)

| file | sha256 | bytes |
|---|---|---|
| main.tex | `8f222301c7810ec2c28dc6485e853ec93d4decbfab48493cb7d4cbbfcf06b9e3` | 50965 |
| main.pdf | `ddb36829b9e9aed0273018ea26fd44f248ac25d6bb830a3117aa22b02bfe61b8` | 704011 |
| refs.bib | `63bd10fde224401447dcda9fb3f992a872e281908169dcba644957e0e7ae7055` | 5029 |
| claims.csv | `53da5fbf3e14eae18bf83bdca00521a791df8ff97c47153733ff900287653d95` | 11883 |
| claims_data.py | `8fdde6762cdd8abdfc9fe0f8464ac99c044e3cf6d3c2f48ae5eb4ce68f8dc6c6` | 39545 |
| figs_v0.2/fig5_Estar_FR30_enclosure.pdf | `65ff3b9c6a1c6288ca8568dd14219ada3d993d28c8e82fcab7a1d38350b42960` | 19031 |
| make_figures.py | `74bc90062667c17a94fa9f9da4729fdb4e74a683598bce7205a433def04fcae5` | 14699 |
| owner-first-pass-2026-11-06.md | `e01165543f08f5b788d268abf6cfd2b3f7296fcc146f0a3138a8872b7294a30d` | 7098 |
| cite-support.md | `0ea45eaebe613a4e647c31608bbc2b1b107ffaaab74e76a6d6ffde29dbe49668` | 35756 |

Baseline v0.1 working copies (untouched snapshot also in `v0.1/`):
`main.tex` `4cc48eafbed24cf0f3db8c64c1a9b532e92ee03429c8d78fff9221edc618af53`,
`main.pdf` `847fa355c96b33a7aec594a108da362c8b95dc989aded2a696fe5f895f627e78`,
`refs.bib` `181e97f3229437b0c1a1d31fe690bae6c6bbc492ea6410b17bfaac1d28c5fb25`,
`claims.csv` `0d9724e17b9e8439bbc4795a700f46774033b130dd913b0c29755539f2d01281`.
