# Phase XII decision memo: what to run next, and why

## Where things stand (certified)

- Over all 1 679 616 Chair44 frame rules, **the maximiser of E_\* is one of 1387, 539311, 1389, 539291**, and the four intervals overlap:

  | rule | interval |
  |---|---|
  | 1387 | [9.1104981, 9.3679502] |
  | 539311 | [8.7999990, 9.3885938] |
  | 1389 | [8.7644993, 9.2104999] |
  | 539291 | [7.1408386, 9.2499401] |

  The lower bound of 1387 (radius 20, 24 571 balls) is reproduced by an implementation sharing no code with the certifying one.

- **The six-member S₃ orbit that topped the funnel is explained, and it is not a symmetry.**
  - The right action of the chair's point group is a gauge symmetry of one inflation step (Orbit Lemma).
  - It is a full symmetry on the conjugation stabiliser (and the closure of such moves), and it is certified broken in infinite volume for 1387 against 539288.
- **The localisation route has reached its limit for the remaining question.**
  - IMS certificates lose ∝ R⁻², and that is optimal for any method uniform over connections.
  - Sampled probes show that no IMS certificate at the probed radii up to 22 separates 1387 from 539311 in either direction.
  - A model extrapolation [X] puts the required radius near 63.

## The decision

**Run next: the level-7 frontier ordering test.**
- Compute the exact rational upper bound Y₇ (pinned T₇, 2 097 152 tiles) for the four frontier rules.
- Freeze the following prediction before any Y₇ value exists.

**The frozen prediction** (committed in `audit/results/phase12_preregistration_next.json` before any Y₇ value exists):
1. the order 539311 > 1387 > 539291 > 1389 of Y₅ and Y₆ persists at L = 7. At L = 4 it was 539311 > 1387 > 1389 > 539291, so this part can fail too;
2. Y₇(539311) − Y₇(1387) ∈ [0.010, 0.030]. Earlier values, from the stored exact bounds: 0.0054 (L = 4), 0.0230 (L = 5), 0.0206 (L = 6). The frozen file's context block gives 0.0231 for L = 5, a difference of rounded values; the band does not depend on it.

**It could fail.** The gap is not monotone in L: it rose by a factor of 4 from L = 4 to 5, then fell. A change of order or a gap outside the band falsifies it.

## Why this experiment, and not another

| option | why not, or why |
|---|---|
| another IMS certificate (1387 at R = 22, 539311 at R = 20 or 22) | the probes already show it cannot separate the co-leaders (Λ_R ≤ 9.17 and ≤ 9.19 against upper bounds 9.37 and 9.39); about 10 h for a result known in advance |
| Y₇ for the frontier | **chosen.** The Y_L sequence is the only data bearing on the ordering that is cheap enough (about 1.5 h per rule on 4 cores). It is exact rational, and its prediction can fail |
| a new lower-bound method that beats R⁻² (supertile-aligned or Schur-complement localisation) | the right long-term move, and the open bottleneck below. But it has no concrete construction yet, so no falsifiable prediction can be frozen today |
| more census statistics or prediction models | they can prioritise but never decide (§8 of the report); the frontier is already certified |

## What each outcome would mean

- **The prediction holds.** It is evidence [E], not proof, that E_\*(539311) > E_\*(1387). That is, the extremiser is the mirror twin, and **1387 is not the maximiser**. Turning this into a theorem needs a lower bound for 539311 above 9.3679502 (the exact upper bound of 1387), which no IMS certificate below R ≈ 63 provides. That is the bottleneck.
- **The gap closes or the order changes.** The working conjecture "the twin wins" fails. The extremal question is open in both directions, and the next target is an upper-bound method that converges faster than the supertile sequence.

## What it cannot do

Y₇ is a finite-supertile eigenvalue: an **upper bound** on E_\*. No outcome certifies an ordering of floors. It is evidence and must be labelled so.

## The open bottleneck it serves

A certificate of the form E_\* ≥ 𝓕 − 𝓔 with 𝓔 = o(R⁻²) for one fixed operator family (Chair44). Theorem C(iv) shows this is impossible uniformly over connections. Whether it is possible for a single hierarchical hull is the specific unresolved proof obligation.
