# T1 results: rigidity of tile-wise Regge metrics on the chair complex

- Prereg (frozen, read-only): `prereg/T1_regge_rigidity.json`, sha256 `f369930bc5c855903d38a5596144dfceae69a844e3283c7a15fba2b096918e47`. Freeze was posted on the bus as #474 before the run.
- Scorer: `prereg/score_t1.py`, sha256 `9579ba79cb8aa9e73c101e7c79d90a4003e80d61e3793ede58c70aa6b69efa24`.
- Raw output: `results/T1_score.json`.
- Run: box only, one process, 2 threads, about 8 s wall.
- Exactness: all ranks were certified over Q (exact nullspace plus an integer check).

## Counts [C]

The metric is constant on each chair tile, with tangential-tangential continuity across every shared unit face. Trivial value = 6.

| L | tiles | N_L FR30 / 1387 | N_int | G_L | Q_L = N - G |
|---|---|---|---|---|---|
| 1 | 8 | 6 / 6 | 0 / 0 (no interior tiles) | 6 / 6 | 0 / 0 |
| 2 | 64 | 6 / 6 | 6 / 6 | 6 / 6 | 0 / 0 |
| 3 | 512 | 6 / 6 | 6 / 6 | 6 / 6 | 0 / 0 |
| 4 | 4096 | 6 / 6 | 6 / 6 | 6 / 6 | 0 / 0 |
| 5 | 32768 | 6 / 6 | 6 / 6 | 6 / 6 | 0 / 0 |

Each of the six component graphs (g_ij) is connected at every tested level L = 1..5. As a result, the only admissible metrics are the global constant ones.

**Control V1 (cube complex, same rule).** N_cube = 60, 216, 816 for L = 1, 2, 3. This equals 3n + 3n² exactly [C], matching the [P] prediction.
- G = 33, 69, 141 and Q = 27, 147, 675 (reported, no prediction).
- So the pipeline does detect local moduli when they exist.

## Verdicts

- **V1: pass [C].** The run is valid.
- **H1: pass [C].** N_L = 6 for FR30 and 1387 at L = 1..5. There are no tile-local metric moduli.
- **H1b: pass [C].** N_int = 6 at L = 2..5.
- **H2: pass [C].**
  - Tile partitions are identical at every L (same sha256).
  - All counts are identical across the two rules.
  - This is consistent with the repo's statement "geometry does not depend on d".
- **H3: pass [C].** Q_L = 0. All admissible deformations are pure global gauge (G = N = 6).
- No failed predictions, no [F] items, and no refit.
- Nothing here is [P] for general L. "N_L = 6 for all L" is [X]: it is supported by L ≤ 5 but not proved.
  - A plausible induction route exists: each supertile's component graphs are connected and glue connectedly. It has not been carried out.

## Meaning

At the tested levels L = 1..5, in this metric space (constant per chair tile, Regge/FEM-type tt-continuity), chair tiles carry no local metric degrees of freedom. Every such metric at those levels is one global flat constant metric. The general-L claim remains unproved.

This is the frozen alternative H0 of FEASIBILITY T1: "Route 1b collapses to 1a."
- At the tested cube-control levels L = 1..3, Q = 27, 147, 675; this is consistent with O(n²) growth (∝ 4^L), not an all-level growth proof here.
- Coarse-graining to chair cells removes all of them.
