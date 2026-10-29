# Phase XII decision memo: what to run next, and why

## Where things stand (certified)

- Over all 1 679 616 Chair44 frame rules, **the maximiser of E_\* is one of 1387, 539311, 539291**, and the three intervals overlap:

  | rule | interval |
  |---|---|
  | 539311 | [9.2083494, 9.3817818] |
  | 1387 | [9.1104981, 9.3616608] |
  | 539291 | [7.1408386, 9.2483895] |
  | 1389 (excluded) | [8.7644993, 9.2083453], below the lower bound of 539311 |

  - The lower bound of 1387 (radius 20, 24 571 balls) is reproduced by an implementation sharing no code with the certifying one.
  - The lower bound of 539311 is the preregistered radius-24 certificate (39 117 balls, all certified), run by one implementation.
  - The upper bounds are exact rational Rayleigh quotients on the pinned level-7 supertiles (2 097 152 tiles).
- **The six-member S₃ orbit that topped the funnel is explained, and it is not a symmetry.**
  - The right action of the chair's point group is a gauge symmetry of one inflation step (Orbit Lemma).
  - It is a full symmetry on the conjugation stabiliser (and the closure of such moves), and it is certified broken in infinite volume for 1387 against 539288.

## The previous decision, and what it returned

The last version of this memo chose **the level-7 frontier ordering test**, with a prediction frozen before any Y₇ value existed (`phase12_preregistration_next.json`):
1. the order 539311 > 1387 > 539291 > 1389 persists at L = 7;
2. Y₇(539311) − Y₇(1387) ∈ [0.010, 0.030].

**Both held**: the order is unchanged, and the gap is 0.020121 (§14.1 of the report). As the memo said in advance, this is evidence [E], not proof, that **the extremiser is the mirror twin 539311, not 1387**.

A second protocol, frozen before the level-7 values and the new probes (`phase12_preregistration_extrapolation.json`), compared an extrapolation from above (Y₅–Y₇) with one from below (sampled radius-R probes). It reports **[X] evidence that E_\*(539311) > E_\*(1387) > E_\*(539291), E_\*(1389)**, and estimates the co-leaders' floors at 9.371–9.380 and 9.359–9.360 (§14.2).

## The decision now

**Run and passed: the radius-24 certificate of 539311 at μ = 9655658/2²⁰ = 9.2083530** (`phase12_preregistration_r24.json`, frozen before Y₇(1389) and before any radius-24 data of 539311).
- Every one of the 39 117 legal radius-24 balls passed: E_\*(539311) ≥ 9.2083494 > 9.2083453 ≥ Y₇(1389) ≥ E_\*(1389). **1389 is proven inferior, and the frontier is three** (report §14.3).
- Go/no-go had passed: the 60-ball probe gave 9.2177320 > μ.
- Cost: 39 117 balls, about 13 h on 4 cores, resumed three times from its checkpoint after the container was reclaimed.

**Next, if compute is available: the radius-28 certificate of 539311** (μ above Y₇(539291) = 9.2483895; about 70 000 balls, 60 h on 4 cores). It would leave 1387 against 539311. It must be preregistered before it is run.

## Why this, and not another

| option | why not, or why |
|---|---|
| a certificate separating 1387 and 539311 | needs radius 67–91 by the two models [X]: 10⁶–10⁷ balls and 10⁶–10⁷ core-hours. Out of reach, and Theorem C(iv) says no geometry-only method does better than R⁻² |
| **the radius-24 certificate of 539311** | **chosen, and passed.** It is the cheapest certificate that changes the certified frontier, its outcome was not known when it was frozen, and it can fail (any ball below μ) |
| a radius-28 certificate of 539311, to exclude 539291 as well | the same idea one step further (μ above Y₇(539291) = 9.2483895); about 70 000 balls and 60 h on 4 cores. The natural follow-up if radius 24 passes |
| Y₈ (16.8 million tiles) | it would sharpen the extrapolation from above, but it is 8× the memory of Y₇ (over the 13.7 GB available) and could not change any certified statement |
| a new lower-bound method that beats R⁻² | the only route to a theorem about the co-leaders, below. It has no concrete construction yet, so no falsifiable prediction can be frozen today |

## What each outcome means

- **The certificate passes (this happened).** E_\*(539311) ≥ 9.2083494 [C], 1389 is excluded, and 539311 also becomes the rule with the highest certified lower bound. The question of the maximiser is then 1387 against 539311 (and 539291, until radius 28).
- **It fails.** Some legal radius-24 ball of 539311 lies below μ. The frontier stays at four. The failing balls are recorded, and they show where the probe and the lower model were too optimistic.

## What none of this can do

No upper bound and no extrapolation certifies an ordering of floors. The question **is E_\*(539311) > E_\*(1387)?** stays open until a lower bound for 539311 exceeds 9.3616608.

## The open bottleneck

A certificate of the form E_\* ≥ 𝓕 − 𝓔 with 𝓔 = o(R⁻²) for one fixed operator family (Chair44). Theorem C(iv) shows this is impossible uniformly over connections. Whether it is possible for a single hierarchical hull is the specific unresolved proof obligation. The level-7 data give one hint where to look: the bottom of T₇ is a dense cluster (the lowest Ritz values lie within 2–7·10⁻⁵ of one another), and for three of the four rules the successive differences Y_L − Y_{L+1} shrink by almost exactly a factor 4 per level (Aitken's q = 0.250–0.262). The low-energy states behave like those of a Dirichlet box with an effective kinetic constant κ_eff ≈ 3.3–3.5 [X], against ≈ 7.8 implied by the IMS fits. A localisation adapted to them would improve the constant by a factor of about 2.3, yet would still need R ≈ 46–62 for the co-leaders (§14.3). **What is needed is a better rate, not a better constant**: for instance a hierarchical (renormalisation) lower bound that compares T_{L+1} with its eight copies of T_L and controls the gluing error by something smaller than R⁻².
