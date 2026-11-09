# Certified spectral floors of Q₈ connections on the Chair44 hull

## Certified frontier

Over all 1 679 616 Chair44 frame rules, the maximiser of the floor E_\* is one of three rules: 1387 ∈ [9.1104981, 9.3616608], 539311 ∈ [9.2083494, 9.3817818], 539291 ∈ [7.1408386, 9.2483895] [C].
Rule 1389 is excluded by the preregistered radius-24 certificate of 539311: E_\*(539311) ≥ 9.2083494 > 9.2083453 ≥ E_\*(1389) [C].
Lower bounds are IMS ball certificates; upper bounds are exact rational Rayleigh quotients on pinned level-7 supertiles.
Source: [deliverables/PHASE12_DECISION_MEMO.md](deliverables/PHASE12_DECISION_MEMO.md).

## Orbit Lemma

The right action of the chair's point group is a gauge symmetry of one inflation step [P].
It is a full symmetry on the conjugation stabiliser, and it is certified broken in infinite volume for 1387 against 539288 [C].
Source: [deliverables/PHASE12_REPORT.md](deliverables/PHASE12_REPORT.md) §2.1.

## Forced curvature

Every geometry-compatible frame field has at least 12 of the 21 centre–octant two-cycles of each level-1 supertile non-trivial, and 12 is attained [P].
The count is checked in Lean ([certificates/Phase7Counting.lean](certificates/Phase7Counting.lean)) and against all 6⁸ × 21 two-cycles.
Source: [deliverables/PHASE7_REPORT.md](deliverables/PHASE7_REPORT.md) §4, [certificates/](certificates/).

## Rate of the lower bound

Theorem C(iv): the R⁻² rate of localisation lower bounds is optimal uniformly over connections [P].
The open problem is a bound E_\* ≥ 𝓕 − 𝓔 with 𝓔 = o(R⁻²) for the Chair44 hull itself.
Source: [deliverables/PHASE12_DECISION_MEMO.md](deliverables/PHASE12_DECISION_MEMO.md), "The open bottleneck"; [deliverables/PHASE15_REPORT.md](deliverables/PHASE15_REPORT.md) measures the boundary weight of the low-energy states.

AI-assisted; every claim labelled [P]/[C]/[E]/[X]/[F]; reproduce with reproduce_open_audit.py.

Other programmes in this repo: [PROJECT.md](PROJECT.md).
