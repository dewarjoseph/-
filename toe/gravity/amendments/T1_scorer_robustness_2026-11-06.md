# T1 scorer robustness amendment (2026-11-06 PT)

Theory of Everything. This is a dated amendment only. It does not edit the frozen preregistration `prereg/T1_regge_rigidity.json` or the frozen scorer `prereg/score_t1.py`. It does not refit or rescore the historical run. Corrections that would change how a future run is scored belong in a new preregistration (v2) with its own hash, as the frozen prereg already says.

This note is based on the shared gravity tree under `/home/box/shared/theory-of-everything/gravity/` and on Meep's 2026-11-06 honesty review §4. That review, and this amendment, did not rerun the geometry pipeline or independently recertify ranks: the frozen scorer imports `chair.py` from outside this tree. This is not a full Cookies audit of the upstream toe repository.

## Frozen artifacts

Hashes checked on 2026-11-06 against the files on disk:

| file | sha256 |
|---|---|
| `prereg/T1_regge_rigidity.json` | `f369930bc5c855903d38a5596144dfceae69a844e3283c7a15fba2b096918e47` |
| `prereg/score_t1.py` | `9579ba79cb8aa9e73c101e7c79d90a4003e80d61e3793ede58c70aa6b69efa24` |
| `results/T1_score.json` | `0d83641fc32e6f2ee2872f2731f1a3320350be1b20a1c8b2e450fb487d073f07` |
| `results/T1_RESULTS.md` | `ced3bf94bca60c18c8948f800b238a28fd46f649fdf33e55804d95ae0ab16894` |
| `prereg/check_verdict_scope.py` | `7312921f0db63d49ef81eb9adae5601babbe3d772ae4e94ececf9fa334ee9bda` |

The saved output records the same prereg and scorer hashes. The prereg was frozen before the run (bus #474).

## What the historical run established [C]

All ten tile cases (FR30 and 1387 at L = 1..5) and all three cube controls (L = 1..3) are present. Every recorded `certified_K` and `certified_G` flag is true. Verdicts: V1, H1, H1b, H2, H3 all `pass`, and `all_ranks_certified_over_Q` is true.

Tile counts from `results/T1_score.json`:

| L | tiles | N FR30 / 1387 | N_int | interior tiles | G | Q |
|---|---|---|---|---|---|---|
| 1 | 8 | 6 / 6 | 0 / 0 | 0 / 0 | 6 / 6 | 0 / 0 |
| 2 | 64 | 6 / 6 | 6 / 6 | 11 / 11 | 6 / 6 | 0 / 0 |
| 3 | 512 | 6 / 6 | 6 / 6 | 225 / 225 | 6 / 6 | 0 / 0 |
| 4 | 4096 | 6 / 6 | 6 / 6 | 2765 / 2765 | 6 / 6 | 0 / 0 |
| 5 | 32768 | 6 / 6 | 6 / 6 | 27045 / 27045 | 6 / 6 | 0 / 0 |

Cube control: N = 60, 216, 816 at L = 1, 2, 3, matching 3n + 3n² with n = 2^{L+1}; Q = 27, 147, 675.

These [C] counts are not invalidated by the robustness finding below. "N_L = 6 for all L" remains [X]. "R1b has no local moduli" is [C] only at the tested levels L = 1..5 and only in this tile-wise constant, tangentially continuous metric model. It is not an all-level proof that every Regge route is impossible.

H1b is defined only for L = 2..5 (the frozen prereg already excludes L = 1). The L = 1 interior count is 0 because there are no interior tiles, not because the interior moduli vanished.

## Limitation of the frozen verdict block

In `score_t1.py` lines 283–295, rank certification is computed as a separate flag `all_ranks_certified_over_Q`. The hypothesis verdicts do not consult `certified_K` or `certified_G`.

Two consequences, reproduced against the live frozen verdict logic by `prereg/check_verdict_scope.py` (re-run 2026-11-06, exit 0; same three lines as `results/review-2026-11-06-verdict-scope.log`):

1. **Uncertified ranks can still pass.** Starting from the saved record and setting `tiles["1"]["FR30"]["certified_G"] = false` leaves `H3 == "pass"` while `all_ranks_certified_over_Q` becomes false. The frozen prereg already says an uncertified rank is only a lower bound (`rank_p ≤ rank_Q`). The verdict block does not enforce that on H1 or H3.
2. **Empty tile data can still read as a pass.** With `tiles = {}`, Python's vacuous `all([])` is true and `full` is false, so H1 becomes `"pass on run levels; incomplete"`. That string is not a complete-run pass, but it should not contain the word "pass" when no tile level was scored.

The historical run used neither of these paths: every planned level is present and every rank is flagged certified.

## Interpretation rule (in force for this frozen scorer)

Until a v2 preregistration replaces the verdict block:

- Do not read a frozen-scorer `pass` as a certified result unless `all_ranks_certified_over_Q` is true and every planned (level, rule) pair is present in `tiles` (and, for V1, all three cube-control levels).
- Do not read `"pass on run levels; incomplete"` as a pass when no tile data, or no data at the levels the hypothesis names, were scored. Treat that as no-data / incomplete.
- If any rank used by a hypothesis is uncertified, that hypothesis is unsupported / uncertified, not passed.
- The 2026-11-01 recorded run meets both gates, so its [C] verdicts stand.

## Proposed v2 gates (not implemented)

Do not patch `score_t1.py`. If a future run is needed, freeze a new preregistration whose scorer:

- returns `uncertified` (never `pass`) for any hypothesis that depends on G, Q, or rank_K when the corresponding `certified_*` flag is false;
- returns `not run` or `incomplete` (never `pass`, and never `"pass on run levels; incomplete"` via a vacuous `all()`) when `tiles` is empty or a planned (level, rule) pair is missing;
- keeps the existing V1 invalidation rule.

## Preprint wording

The scorer limitation itself does not need to appear in the paper. The historical run was complete and certified.

If the paper mentions T1 or Route 1b, use the scoped language already in `results/T1_RESULTS.md` and `FEASIBILITY_scoping.md` (T1 outcome, 2026-11-01, as corrected on 2026-11-06):

- The L = 1 interior count is 0, not 6.
- `N_int = 6` holds at L = 2..5 [C].
- No local tile-wise moduli, and Q = 0, are [C] only at L = 1..5 in this metric model.
- The all-level claim is [X].
- This is not a classification of all Regge formulations.

G6-O1 remains elementary geometry of the static complex (deficits vanish), not this T1 count. G6-O2 remains a separate one-line remark; this amendment does not relabel it.
