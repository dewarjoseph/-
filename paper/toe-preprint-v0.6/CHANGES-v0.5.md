# CHANGES-v0.5 (2026-11-06, America/Los_Angeles)

Internal draft only. Not submitted, not published, not for external release.

Closes three prose TODOs that could be closed from files already on hand, without
a new author or ledger-owner ruling. Paper labels, `claims.csv`, `claims_data.py`
and `refs.bib` are unchanged from v0.4. Frozen `figs_v1.0/`, `toe-preprint/v0.1/`,
and the T1 prereg/scorer/results files were not edited. No author ruling was
invented for G1-RARE, G2B-DERIV, D2, the K5 split, Lean-audit labels, or G6-O2.
Kato stays unwired.

## K4 Lean names, with a statement-scope caveat

Replaced the K4 naming TODO. The kernel-re-checked file recorded in
`toe/inventory/lean_recheck.json` / `lean_chair44.json` is
`certificates/Phase7Counting.lean`. The theorems that carry the encoded
counting predicates are `octant_bound`, `total_bound` and `bound_attained`
(Lean 4.35.0, standard axioms only, no `sorryAx`). That `.lean` file is not
in the source snapshot used for this note, so the names come from the Chair44
Lean audit and the re-check log (`Phase7Counting.out`), not from a fresh
reading of the Lean statements.

The audit's match note is that Lean certifies only those encoded finite
predicates (an encoded `trivial` test). The identification of that encoding
with geometric two-cycle holonomy, and the step from per-octant bounds to
"≥ 12 of 21", sit outside the kernel check. The geometric English of K4 is
therefore not itself a Lean theorem statement. `forced_proper` and
`forced_fails_improper` in the same file concern the proper-frame "nine
forced" count, which is not K4. The 1,679,616-assignment enumeration remains
a ledger record, not a Lean theorem.

## [S] scope check

Replaced the novelty-note TODO. The existing paragraph already treated unique
ergodicity of this framed-chair hull as an unverified input (Solomyak 1997
covers self-similar R^d tilings with finite local complexity; the
substitution-matrix identification and the R^3 → Z^3 suspension are stated
briefly; primitivity does not imply repetitivity). The novelty note
(`theorem-F-novelty.md` §5.3) finds both steps plausible but stated only
briefly. The paper now says that explicitly and still does not treat the [S]
step as newly checked [P]. No new citations were added.

## Phase summaries

Replaced the Phase summaries TODO with condensed prose for Phases 0–3 and
After Phase 4, including the required Phase 3 failures (G1 H1, H2, H3b;
G2 W3c, B4). Excluded-lineage passages and the Lean-audit example at
TOE_ATTEMPT.md l.34 are not reproduced; Phase 0 says only that the audit
confirms earlier refutations already marked [F]. Paper labels are used for
later scorecard wording: row 4 continuum/mass-term identification stays [X];
row 3 prints [P] S1/S4, [C] symmetry count, and [E] for G5.1–G5.4. Theorem F
is not called a new limit theorem. Hand proofs stay [P, unverified].

## Left unchanged

Commit hashes (three places) and the original-run software environment remain
TODOs: the source was a file snapshot with no git metadata, and no Python /
NumPy / SciPy / platform versions are recorded in the snapshot results files.
Short hashes mentioned inside `prereg/G7_gap.json` were not used, because they
are not freeze commits for G1, G2, G3 or G5 and were not matched to the
snapshot file hashes. Live Cookies `7e6a508` is the later ledger-sync commit,
not the snapshot this note was read from.

## Build

`latexmk -pdf` with TinyTeX: exit 0, 32 pages (v0.4 was 31), no errors, no
undefined citations. CreationDate Fri Nov 6 20:09:31 2026 PST.

| file | sha256 |
|---|---|
| `main.tex` | `dba09b3a5415fdded82cce8187df11ff64a053f4890a36c09c9d9882656d2e5c` |
| `main.pdf` | `c5c46bfa25b99c5b8f39626d17f57b308dd778da886eeb850c141e9fde9580bb` |
| `claims.csv` (unchanged) | `d54beaef4d70848b2b31fb75d4c08986e912b9d961d2aad7caa6f98a2f19296f` |
| `claims_data.py` (unchanged) | `1dda19e495aebd6f8bab03f5b94fc14e5ca8389383860610f13a838989bd277e` |
| `refs.bib` (unchanged) | `1fa341add231635a81f3265b3702843efc24a85d494af305fe1af20165d4b366` |

10 red TODOs remain (9 prose/author items and the Kato cite-TODO).
Still not for external release.
