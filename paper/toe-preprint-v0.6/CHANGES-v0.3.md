# CHANGES-v0.3 (2026-11-06, America/Los_Angeles)

Internal lockstep only. Not submitted, not published, not for external release.

Applies Theory of Everything's dated T1 amendment
(`/home/box/shared/theory-of-everything/gravity/amendments/T1_scorer_robustness_2026-11-06.md`,
sha256 `106b756ebc6eea22021ef615dea83c2060b7ede9aa1c7d4689c41c7ab5e9ee96`)
and owner cite-TODO marks
(`/home/box/shared/research-publishing/toe-preprint/owner-cite-todos-2026-11-06.md`,
sha256 `91c0f58e7bc958b0b9e32dccdbecd30aaf902aa1d1e693f59dd6e7a9bde450c8`).
Draft v0.2 remains the record of the owner first pass (`CHANGES-v0.2.md`).
Frozen `figs_v1.0/`, `toe-preprint/v0.1/`, and the T1 prereg/scorer/results files were not edited.
`claims.csv` and `claims_data.py` are unchanged (no label edits in this pass).
The live Cookies ledger was not touched.

## T1 wording (G6 section)

Where the note mentions the T1 gravity run it now prints the owner-specified scope:

- the \(L=1\) interior count is 0, not 6;
- \(N_{\mathrm{int}}=6\) holds at \(L=2,\ldots,5\) [C];
- no local tile-wise moduli, and \(Q=0\), are [C] only at \(L=1,\ldots,5\)
  in this tile-wise constant, tangentially continuous metric model;
- the all-level claim is [X];
- this is not a classification of all Regge formulations.

Scorer internals are not described. G6-O1 remains an elementary geometry statement
(hand, unverified), not T1's "no local moduli" result. G6-O2 remains a one-line
TOE_ATTEMPT.md remark; its [P] label was not unilaterally changed.

## Cite-TODO marks

Twelve keys were copied from the shared bibliography into `refs.bib` and wired
only for the clauses the owner marked safe. Kato (`kato1972schrodinger`) was not
added; the K14 cite-TODO remains. The cite-TODO note is sentence-level support
for wiring, not a claim that journal bodies were newly checked.

| key | how it is used |
|---|---|
| `wilson1974confinement` | pointer for the Wilson action; normalisation and use with \(Q_8\) and \(2I\) are not checked from the abstract |
| `nakamura2000lifshitz` | related remark that \(\inf\sigma=0\) a.s. appears in a different model (i.i.d. \(U(1)\) on \(\mathbb{Z}^2\)); not the source of the finite-energy / Borel--Cantelli write-up, which stays the author's and is not claimed new |
| `luscher1977transfer` | \(SU(N)\) / hypercubic transfer-matrix mechanism, with the stated scope caveat |
| `osterwalder1978gauge` | abstract pointer beside Lüscher; proof, gauge choice, and group class not seen |
| `nielsen1981absenceI`, `nielsen1981absenceII` | pointers for the 1981 no-go (abstracts only); infinite-volume / translation-invariant proofs do not cover the finite-patch claim (G4-INFVOL) |
| `kaplan1992chiral` | a domain wall inserts chirality rather than deriving it; no overlap-operator citation |
| `witten1982su2` | abstract pointer matching the \(SU(2)\) odd-doublet inconsistency sentence |
| `regge1961coordinates` | pointer for the name "Regge calculus"; not support for the chair-complex deficit-zero calculation |
| `ambjorn2004emergence` | names causal dynamical triangulations as a way to make geometry dynamical; does not support G6-O2 |
| `minami1996local` | generic Poisson-statistics pointer, with the i.i.d. Anderson bulk-local-stats caveat; no novelty claimed |
| `petcher1980montecarlo` | \(2I\) freezing only (abstract); not cited for \(Q_8\) or the spherical-design argument |

R0's extension remains [P, unverified]. The 1982 Nielsen--Ninomiya erratum is not
cited; the `note` field that records it in the shared bibliography was omitted
from this draft's `refs.bib` listing so the printed bibliography does not list it.
Still not invented or added: a discrete-Kato substitute, an overlap paper,
Dunford/Zygmund 1951, Papanicolaou--Varadhan, Bourgeat--Piatnitski.

## Build

`latexmk -pdf` with TinyTeX: exit 0, 31 pages (v0.2 was 30), no errors, no
undefined citations. 27 bibliography entries are cited (15 from v0.2 plus the
12 above). Kato is absent from `refs.bib` and `main.bbl`.

| file | sha256 |
|---|---|
| `main.tex` | `49591ef1159c03a7f9556927e7e2348ac110076f7e4ba4337c51b878bb836705` |
| `main.pdf` | `6d53916d48895f5413fba4475730db3d6ea2a77566ed8affec91672a78f86679` |
| `refs.bib` | `1fa341add231635a81f3265b3702843efc24a85d494af305fe1af20165d4b366` |
| `claims.csv` (unchanged) | `53da5fbf3e14eae18bf83bdca00521a791df8ff97c47153733ff900287653d95` |

Paper labels are unchanged from v0.2: [P] 33, [C] 12, [E] 33, [X] 5, [A] 5, [F] 11.
13 red TODOs remain (12 prose/author items and the Kato cite-TODO).
Ledger downgrades, if they change printed claims, will need a later lockstep.
