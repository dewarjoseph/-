# IMPRIM1 scoring 2026-11-06

Commit `0b51191b16589917a67287ae0bfaa2f6aa314722` on Cookies `toe-unification` (not pushed).
Scored completed run (started 2026-10-31T21:41:14-0700, 3201.4779827594757 s, under 4 h cap) with frozen `src/score_imprim1.py`. No rerun, no refit, frozen prereg untouched (sha256 `125418c10f5c9a8a81e70c04955d99fb184d3538300e40cdc346200805821729`).

Verdicts: K0 holds [C]; P1 [F]; P2 holds [E]; P3 holds [E]; P4 holds [C].
P1 failed on x539291: |c5-c4|/|c4-c3| = 0.911285402106358 > 0.75 (second step 0.4044054961392064 holds). x539311 held (0.49346387349727594, 0.37952106462615376).

Certified brackets [C, given D1 [P], rounded outward]:
- rho(x539311) in [14.182460, 16.411809]
- rho(x539291) in [13.835184, 16.069450]

New ledger rows: TOE-IMPRIM1-K0, P1, P2, P3, P4, RHO-x539311, RHO-x539291.
Counts now 1329 claims; P373 C244 X118 E356 F191 A47; excluded 333.

SCORECARD: appended an IMPRIM1 scoring section; no physics table row moved.
sha256 score `62ddab29d8b02098e21b819fe58eea47d483c35e46048c32153285770a3b2316`
sha256 run `7f8cb1136168d0d453d770be667f71e5e2699d8528f336b8afab11b9350d5e5f`
leftovers: L7 `results/proof_bounds.json` still uncommitted; do not start a new L7 run. Independent review of PROOF.md remains Joey's flag. G8 not started.
