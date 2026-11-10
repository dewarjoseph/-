# CHANGES-v0.4 (2026-11-06, America/Los_Angeles)

Internal lockstep only. Not submitted, not published, not for external release.

Applies Theory of Everything's owner ledger sync
(`/home/box/shared/research-publishing/toe-preprint/owner-ledger-sync-2026-11-06.md`)
to draft v0.3. Live Cookies `toe/` branch `toe-unification` commit `7e6a508`
(`7e6a508a4a0229418e1fda64ab62a8e34ab04812`) is not pushed. Frozen
`figs_v1.0/`, `toe-preprint/v0.1/`, and the T1 prereg/scorer/results files
were not edited. The live Cookies ledger was not edited from this side.

Paper labels were already matched to the downgrades and are unchanged from
v0.2/v0.3: [P] 33, [C] 12, [E] 33, [X] 5, [A] 5, [F] 11; 15 paper labels
weaker than source; pending markers on G1-RARE ([X]) and G2B-DERIV ([E]).
No author ruling was invented for the source's P-level wording.

## Ledger ids

Filled the 33 previously empty `ledger id` cells in `claims.csv` with the
paper id, via identity maps in `LEDGER_IDS` (`claims_data.py` is the source
of truth; `python3 build_claims.py` regenerated `claims.csv`). Generated
claim TeX fragments (`claimdefs.tex`, `claims_table.tex`, `claims_flags.tex`,
`claims_counts.tex`, `label_changes.tex`) are byte-identical to v0.3.

The 33 ids: K12, K13, K14, K15, I-TSEITIN, I-ENERGY, I-ENERGY-INST,
I-XIII-SCOPE, I-UG-EXT, I-QIS320-INST, I-GU-A, I-WOLFRAM, G1-T1, G1-T2,
G1-RARE, G1-FLOORS, G1-TRIVIAL, SC-8, G2B-DERIV, G2B-CL, G2B-LIMIT,
G2B-MASS, G2B-POSTHOC, PROOF-E-TABLE, PROOF-L7, G2A-SELFENERGY,
G3-SPECTRUM, SC-6, G4-INFVOL, G5-S1, G5-S4, G5-COUNT, G5-R63.

Existing mapped rows were left as they were (for example K6 remains
`CH10-X4-no-go`; FIG5-ESTAR remains `CH9-N3-enclosure`). After this fill,
`claims.csv` has no empty ledger-id cells.

## Labels left as printed

- G2B-LIMIT and G2B-MASS remain paper [X] (ledger [X]).
- FIG5-ESTAR remains paper [E] (source [C]) with outward enclosure
  `[7.954291, 8.7642270382]`.
- K6 remains paper [C] as the weakest component of a compound whose X4
  no-go stays [P] in the ledger.
- G6-O1 and G6-O2 remain [P]; O2 was not unilaterally relabelled.
- Unique ergodicity and Theorem F stay unverified. The Chair44 diffraction
  run is not treated as a new [P]. No Chair44-as-icosahedral or i-QC
  powder-list wording was added. No MHz nanoshell observation was added.

## Paper sentence

The limitations bullet that said several claims had no ledger entry now
records that those rows use the paper id as the ledger id, and that
G1-RARE / G2B-DERIV still await an author ruling on the source's
non-standard P-level wording.

## Build

`latexmk -pdf` with TinyTeX: exit 0, 31 pages, no errors, no undefined
citations. `refs.bib` is unchanged from v0.3 (27 cited keys; Kato not added).

| file | sha256 |
|---|---|
| `main.tex` | `8366dc906d3107f280706cffc472ae998831ee93c312056c0159260a8879032d` |
| `main.pdf` | `0e36b60cbe7de59f4ac92f38c5265b4c7525ad14dffe888d0bd0ac346c483e2c` |
| `claims.csv` | `d54beaef4d70848b2b31fb75d4c08986e912b9d961d2aad7caa6f98a2f19296f` |
| `claims_data.py` | `1dda19e495aebd6f8bab03f5b94fc14e5ca8389383860610f13a838989bd277e` |
| `refs.bib` (unchanged) | `1fa341add231635a81f3265b3702843efc24a85d494af305fe1af20165d4b366` |

13 red TODOs remain (12 prose/author items and the Kato cite-TODO).
Still not for external release.
