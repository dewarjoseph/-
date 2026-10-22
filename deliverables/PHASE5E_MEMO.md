# Phase V-E research memo

**Question.** Can the exact child-to-parent Schur recursion for the FR30/Chair44 pinned edge be compressed into a low-dimensional, gauge-invariant renormalization state that predicts the edge, explains FR30's anomaly, and controls the large-scale limit?

**Answer.**
- **No, for every compression defined from the child, the geometry or training rules at level 4.** That covers 6 families, 264 held-out rule classes and 18 controls under a protocol frozen in advance. The failure is sharp and quantified.
- **An exploratory "yes, asymptotically" for one form.** FR30 has a compact, environment-selected local state (about 34–56 variables per level-3 copy, out of 574). It saturates through level 7, and trained on levels 6–7 it predicts the level-5 edge to 0.019 at 10 % of the boundary dimension. It is not built from the child's spectrum, and it fails at level 4, where every copy touches the pinned wall.

## Strongest positive results (proved)

**The exactness half.** The Schur reduction is an exact spectral correspondence by inertia on all of ℝ \ spec H_II (Theorem E1). It handles poles, multiplicity and the kernel isomorphism, and K(E) is Loewner-decreasing and concave below λ_II.

**The approximation half.** This is a theorem about *every* gauge-covariant, Kramers-complete compression W of the boundary operator (Theorems E3–E4):

  μ₂ (1 − c) / |g_W′(E_W)|  ≤  E_W − E₀  ≤  (48 − E₀)(1 − c)/c,   with μ₂ ≥ min(λ₃(H), λ_II) − E₀,

where c is the fraction of the exact boundary ground pair that W captures. Compression is therefore exactly as good as its captured weight.

**The obstruction.** Theorem E5 gives the Eckart–Young bound for universal subspaces. Together with E2, which classifies gauge-invariant boundary data, it turns "no compression found" into a measurable obstruction. All bounds hold on 6606 (system, basis) pairs.

**A certified improvement.** The exact integer Rayleigh quotient of the level-7 vector gives E_∞ ≤ 8.7649120248, which tightens the certified bracket from 8.7701336 to 8.7649121 (lower end 4.008189).

## Strongest negative result (computational, scoped)

Tested on the 264 frozen rule classes and the 18 intervention controls at level 4, with the protocol frozen in advance:
- **No a-priori family reaches the frozen accuracy.** These are child modes, one- and two-sided face modes, face/hinge/corner and hierarchy patches. At ≤ 10 % of the boundary dimension none reaches calibrated RMSE ≤ 0.05; the best is 0.17–0.20.
- **Training-only tile selection** gives 0.176 at the cap. Even the target-ranked oracle gives only 0.140.
- **The best compression is still useful.** child(16), 5.6 % of the boundary dimension, beats V-D's target-free descriptors out of sample (CV-R² 0.925 vs 0.917), gets all 17 intervention directions right, and explains 65 % of FR30's residual. It fails exactly on the controls that randomise the coarse arrangement.
- **The obstruction is an area law.** The low spectrum of the supertile response crowds ∝ surface, and the support of the boundary ground pair tracks the seam area.
- **Only removing the pinned outer boundary is exact.** It reproduces the edge (0.035 RMS) and 98 % of FR30's residual, which places FR30's excess entirely in the seam region. FR30 has the most frustrated ground-state bonds of all 264 classes (exploratory).

## What remains unresolved

- **Whether the saturating local state is general.** At each level, the restrictions of the ground state to the copies of T₃ lie in a ≈ 20–40-dimensional subspace of 574. Through level 7 the union saturates (99.9 % in 56 dimensions). Trained on levels 6–7, this state predicts the level-5 edge to 0.019 at 10 % of the boundary dimension. That is the first compression meeting the accuracy bar, but it is exploratory, FR30-only, and fails at level 4 where every copy touches the pinned wall. Whether this asymptotic bulk state generalizes across rules, and how to construct it without solving deeper levels, is open.
- **The infinite-volume limit.** E_∞ is bracketed in [4.008189, 8.7649120248] (certified; the upper end is new in this phase, from the level-7 vector) and E₇ = 8.7649120 (Ritz bound; residual 1.5×10⁻⁷). The decrement ratio r₇ = 0.194, so by the frozen rule it keeps falling. No single power law with p = 2 fits levels 4–7, and the apparent D₂ ≈ 1.9 depends on the boundary condition. No phase is inferred.
- **Nonlinear or energy-dependent closures** are not excluded by anything here.

## Single most informative next experiment

**A pre-registered, cross-rule test of the bulk local-state renormalization at level 5.**

- *Setup.* Take a frozen subset of the 264 rule classes and the 18 controls. For each, compute the level-6 ground pair with the existing ChebFSI solver (17 s per rule at level 5 on this machine; minutes at level 6) and build the rule's own T₃-copy snapshot subspace (d ≈ 42–58).
- *Prediction.* Predict E₅ through the 64-copy reduction (`audit/phase5e_run.py closure5`, generalised per rule) and score it against a flux baseline at level 5.
- *What it settles.*
  - whether the saturated state exists for every rule, or only for FR30;
  - whether it meets C2 out of sample;
  - whether it explains FR30's level-5 residual and the intervention directions.

  That is, whether the one positive structure found here is a theory or a property of one rule.
- *A cheaper companion: the crowding density N_m(w)/|surf_m| at m = 5–7 by sparse inertia counting.* By E1, n₋(R_m(E) − w) = n₋(H − E − wΠ_S) − n₋(H_II − E). This would confirm that the child's own spectrum can never supply that state.
