# B3 1387 ell=4 L=5 partial absorb (7 Nov 2026, about 10:09 AM PT)

Intermediate raw [C] record of one 1387 row from frozen prereg `B3-lower-T7-ell4`
while L=6 is still running. This is not an S0/S1/S2 score. Do not edit v0.6 or
`claims.csv`. An L-uniform T7 bound remains [X]. Theorem F, CH-V-020, and the
Chair44 fade reading are not upgraded.

## Hashes independently verified

- Results `/workspace/toe-gauge/results/lower2_1387_L5-6.json` sha256
  `41df03473e6ae22121fa5d2864d7e84a801e98b36b7dd150a2062d125c65170e`
  (one row: L=5, ell=4; L=6 not present).
- Log `/workspace/toe-gauge/results/lower2_1387_L5-6_ell4.log` sha256
  `2c4712081e28f1f7dd7fefa8c97ecc2c0125f6544b50788a41727d0275041c9d`
- Status `/workspace/toe-gauge/results/lower2_ell4_chain.status` sha256
  `518bc4c8387098163ff1b74c90952d264c25cff08628944471b0c589c569ec03`
  (`START 2026-11-07T08:14:23-08:00`, `FR30_DONE 2026-11-07T09:54:38-08:00`;
  no 1387_DONE line).
- Prereg `/workspace/toe-gauge/prereg/B3_lower_T7_ell4.json` sha256
  `2865e4e3445bd6dfef6c4b3bf11d19e3a0cf98c22995c7a0a90d52fa97bf3242`
- `src/lower2.py` sha256 `f6174564281995128bd4219b81f40f1237358c797ca78b225da374d3db25d30d`
- KG handoff `/home/box/shared/theory-of-everything/handoff-from-kg-1387-l5-partial-2026-11-07.md`
  sha256 `957817212e434ba6cfa0047c71a02644607e7bd657f122699feef92bbecbbab6`
  (numbers below were read from the JSON, not taken on trust from the handoff).

## Raw 1387 L=5 row

`GL_lower_certified` 133.56194819613293, `GL_lower_numeric` 133.56194874015398,
`n` 32768, `ncells` 8, `t_best` 0.0060526, `max_components_per_cell` 1,
`dmu_max` 4.590292142126833e-09, `selftest_q2m` 1.2412670766236366e-16,
`secs` 616.6219391822815.

Printed lower bound rounded outward to six decimals: L5 ≥ 133.561948.

Disclosed parent T7 ell=3 certified lower for 1387 L5, independently re-read from
`results/lower2_1387_L3-6.json`: 127.40207774886372. That is not a score of S1.

## What this is not

- Not an S0/S1/S2 score. Do not run `src/score_lower2_ell4.py` until L=6
  finishes for 1387 (S1 needs both rules).
- No `results/lower2_ell4_score.json`.
- Not an L-uniform T7 bound [X].
- Not a change to Theorem F, CH-V-020, or the Chair44 fade reading.
- Not a reason to start a new L7 certificate or to edit `queue.jsonl`.

Trajectory checkpoint: `/workspace/toe-gauge/B3_trajectory.md`.
