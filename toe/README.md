# toe/ — unification-programme working record (Chair44 connection floor)

This folder holds the research record behind the v0.6 preprint in `paper/toe-preprint-v0.6/`: preregistrations, scored results, certificate re-derivations, Lean scratch proofs with kernel re-run logs, and dated amendments.
**Status.** "ToE" is an internal project name for a unification programme. It is not a theory of everything, and it makes no physical claim. The content is mathematics and lattice computation about one object, labelled claim by claim. The target is a condition, not an award: every row of the physics scorecard proved or certified, each at its stated scope, is necessary before the larger name could be used, and it would not by itself be enough. Until then it stays a unification programme. The open rows, each with a next attempt and a proposed pass/fail test, are in [`OPEN_ATTACKS.md`](OPEN_ATTACKS.md).

## Contents

| path | what |
|---|---|
| `B3_lower_T7_ell4.json` (+ `.sha256`) | frozen preregistration B3-lower-T7-ell4 (ell = 4 cell level at L5–6) |
| `b3-*.md` | the prereg note, the raw [C] records and the S0/S1/S2 score for that prereg (FR30 and rule 1387) |
| `chair44-antidiagonal-mechanism-2026-11-07.md` | mechanism note for the fading anti-diagonal streak on finite Chair44 patches ([C on patch], with [X] readings) |
| `chair44-L64-honesty-2026-11-06.md`, `k4-lean-honesty-2026-11-06.md` | honesty corrections (L = 64 diffraction scope; what the K4 Lean files do and do not check) |
| `imprim1-scored-2026-11-06.md` | IMPRIM1 preregistered scoring (includes a falsified prediction, P1 [F]) |
| `step3-sharp-2026-11-07.md` | sharper Theorem F step-3 inequality [P, Lean] (scratch) |
| `fig5-estar-*-rederivation-*.md`, `fig5-rederive-logs-2026-11-09/` | re-execution of the FIG5-ESTAR lower-end certificates (MATCH) and the recorded obstacle (out of memory) on the upper end |
| `lemma-a-lean-copies/`, `lemma-bd-lean-copies/`, `dform-lean-copies/` | byte-identical copies of Lean 4 scratch proofs (not Lake targets, not peer-reviewed) |
| `dform-rerun-logs-2026-11-09/` | kernel re-run logs for the D-form files; `SHA256SUMS` in each folder |
| `amendments/` | dated ledger addenda; they never rewrite the files they amend |
| `gravity/` | Regge / CDT feasibility scoping, the frozen T1 preregistration and scorer, results and a scorer-robustness amendment |
| `REDACTIONS.md` | the two files changed for publication, with their original hashes |
| `OPEN_ATTACKS.md` | invitation: every open scorecard row with its current label, a next attempt and a proposed pass/fail test (proposals for future preregistration, not preregistered) |

## How to read it

- Labels: [P] proved · [C] certified or computed (the scope is written next to it, e.g. "on patch") · [E] evidence: numerical or simulated, and real measurements when marked "(measured)" · [X] conjecture or open · [A] analogy only · [F] falsified · [S] taken from a cited source and not re-checked here.
- Preregistrations were frozen before their runs and never edited afterwards. Failed predictions are kept and labelled [F].
- "[P, Lean]" means the stated finite predicate is kernel-checked. It does not mean the English gloss or any physical reading is proved.
- Many notes name private working paths (`/home/box/...`, `/workspace/...`) and internal post numbers. They are kept so the recorded sha256 values stay valid. Those paths are not part of this repository.
- Produced with AI assistance. Each claim carries its label and an evidence pointer, and should be judged on those.
