# Phase VII protocol (frozen before any new value is computed)

Branch `claude/phase7-local-determinacy`, from main 9b72690 (V-E merged; V-I PR #7 open on its own branch). Two tasks:
**(I)** the local-determinacy experiment proposed in Phase VI §9, and **(II)** an adversarial re-certification of the
Phase VI claims (Phases 0–3 of the brief; the brief's text ends at "D. alternative admissible Q8 assignments").

## (I) Is the value of FR30's bulk floor fixed by finite-radius local data?

**Definitions.** R-star of a tile a: the tiles owning a cube at Chebyshev distance ≤ R from a cube of a; its type is the set of
relative poses (M_aᵀM_b, M_aᵀ(T_b − T_a)) (V-B). V_R = legal FR30 R-star types (V_1 = 72, V_2 = 165 from V-B; V_3 = Φ_3(V_2),
V_4 = Φ_4(V_2) by the collared closure lemma "r-star of a child ⊂ σ(⌈r/2⌉-star of its parent"), validated by the census of
complete stars in FR30 supertiles. 𝒯_R = chair tilings with geometry-compatible frames all of whose R-stars lie in V_R.
E(Y) = inf spec (24 − A_U) on Y.  E_inf(R) := inf_{Y ∈ 𝒯_R} E(Y);  E_FR30 = E(FR30) ∈ [4.008189, 8.7649120247] (certified).

**Facts used.** E_inf(R) ≤ E_FR30 and E_inf(R) is non-decreasing in R. A radius-R block decomposition (cube blocks of side
s = R + 1, weight 1/((s−1)s²)) gives a certified **lower bound L_R ≤ E_inf(R)** (it holds for every tiling in 𝒯_R, because it only
uses legal R-star types). A periodic tiling P whose R-stars are all legal is in 𝒯_R, so its Bloch band bottom gives an
**upper bound E_inf(R) ≤ E(P)**.

**Correction of the Phase VI §9 decision rule** (recorded before computing): "approximants converge to 8.76 while lower bounds
stall ⇒ hierarchy" is not a valid inference — converging approximants are evidence *for* locality, and stalling bounds may
only reflect looseness of the block method. The valid, asymmetric rule:
- **H (radius-R data does not fix the floor):** some P ∈ 𝒯_R has band bottom E(P) ≤ 8.70, i.e. clearly below FR30's floor
  (E_FR30 ≤ 8.7649 certified; ≈ 8.7635 by the V-E refits). This is rigorous only relative to a certified *lower* bound on E_FR30
  above E(P); the best available is 4.008 (V-B), so H will be stated as a computational result [E] unless such a bound is reached.
- **L (local determinacy at radius R), rigorous:** L_R ≥ 8.7649120247 − δ' would show radius-R data pins the floor to within δ'.
- **Inconclusive at radius R** otherwise; report L_R, the best E(P) over legal approximants, and the gap.
- Approximants that are *not* in 𝒯_R (illegal stars at the seams) are reported, with the fraction of illegal tiles per R, but are
  not used as witnesses for H.

**Approximants.** The V-A family P_k = σ^k(Λ₇ chair crystal) = level-k FR30 supertile on the lattice 2^kΛ₇ (exact Bloch theory,
band bottoms 8.3346, 7.5105, 8.2459, ≤ 8.3593 for k = 1..4, stored). New: the R-star legality of every tile of P_k, R = 1..4.
If the seams are illegal, search for legal approximants is reported as a separate, labelled attempt.

**Certification of L_R.** Block forms have Gaussian-integer entries. λ_min(k_c) ≥ μ_c is certified either exactly (Sylvester
minors by fraction-free Bareiss, V-B's routine) or by the rigorous floating-point Cholesky bound (Higham, *Accuracy and Stability
of Numerical Algorithms*, 2nd ed., Thm 10.3: R̂ᵀR̂ = A + ΔA, |ΔA| ≤ γ_{n+1}|R̂ᵀ||R̂|, γ_k = ku/(1 − ku)), with the exact method
cross-checked on a sample. R = 2 must reproduce V-B's 72147403/18000000.

## (II) Adversarial re-certification of Phase VI

| claim | independent check (new code, not phase6_*.py) |
|---|---|
| F′: 9 forced two-cycles per level-1 supertile, proper frames | enumerate the 6561 cases from the octant/frame definitions with integer-quaternion links and an explicit Q8 multiplication table; derive two-cycles from the panel incidence; test every one of the 9 in every case |
| improper frames | exhaustive enumeration of all 6⁸ = 1 679 616 compatible O(3) frame choices at level 1: pure-gauge or not (all fundamental cycles), smallest counterexample if any |
| F: D_U†D_U ⪰ 167/100 | re-certify all 6561 level-1 blocks with a different exact algorithm (Bareiss/Sylvester over ℤ[i]); attempt a sharper constant; state the local-to-global argument with all hypotheses |
| Lemma K | free (Neumann) vs pinned operators; connectedness; kernel dimension; infinite volume (ℓ² kernel vs bottom of spectrum) |
| F″: FR30 > Z₂ | same operator, same normalization (24 − A on the infinite tiling), certified bounds on both sides; controlled comparison trivial / Z₂ / FR30 / other Q8 decorations / random Q8 |

No threshold or decision rule above is changed after values are seen; anything added later is labelled exploratory.
