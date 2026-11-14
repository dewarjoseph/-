# Open attacks: an invitation

The physics scorecard of this programme has open rows. This page lists every one of them, and a few open items beside them, as a standing invitation: pick one, attempt it boldly, and record what happens. For each open item you get three things: the label copied from the v0.6 scorecard, a next concrete attempt, and a proposed pass/fail test (not preregistered).

Nothing on this page is a result. It makes no new claim, moves no label, and changes no test, number or bound anywhere else in the repository. The status of the programme is stated once, in [`README.md`](README.md) (this folder).

## How a bold attempt is recorded

A bold attempt that fails is recorded as a result, either as [F] (a frozen prediction was falsified) or as an obstruction (a precise statement of why the route is blocked), and never as a mistake. This record already works that way: the falsified predictions G1 H1, H2 and H3b and G2 W3c and B4 are kept, labelled and cited. Only a result that is hidden, rewritten after the fact, or printed stronger than its evidence counts as a failure of method.

## Ground rules for every attempt

- **The tests below are proposals for future preregistration. None of them is preregistered.** Each one must be frozen, hashed and posted before its first run, with its thresholds and seeds written down. A test on this page fixes the shape of pass and fail. The frozen version fixes the numbers.
- A label is assigned by what was shown, at the scope it was shown, and never by what was hoped. A pass in a finite computation is a computed result at that scope. It is not a proof for all levels.
- Hand proofs stay marked as unverified until they are machine-checked or independently reviewed.
- Rule-blind results count. If an observable does not depend on the frame rule, that is recorded as an obstruction (the hull acts as an inert lattice for that observable). It is not hidden and it is not a partial success.
- Do not build on anything already recorded as [F].
- Respect the recorded obstructions. A proposal that conflicts with TOE-G4-O2 [P] (the anomaly requirement of an even number of doublets), for example, has to say how.

## Where the labels come from

All labels on this page are as of the v0.6 scorecard and are not updated by this page. A later record that moves a row governs, and this page would then need a re-sync.

The "Label (v0.6 scorecard)" lines are copied from the scorecard table of the frozen v0.6 preprint (`paper/toe-preprint-v0.6/main.tex`, section "Scorecard after Phase 3"), as plain text. Where the preprint restates a partial-result label (rows 3 and 4), the preprint's wording is used. Claim identifiers and their labels come from `paper/toe-preprint-v0.6/claims.csv` (the paper label column).

As the table caption says, the [P] entries of the scorecard are hand proofs, [P, unverified]: they are not machine-checked and not peer-reviewed. This applies to every [P] from the scorecard or claims.csv on this page (TOE-G3-R0, TOE-G4-O1, TOE-G4-O2, TOE-G5-S3, TOE-G5-none, TOE-G6-O1, TOE-G6-O2, SC-6, SC-8).

## The open rows at a glance

| id | scorecard row | status (v0.6 scorecard) | page section |
|---|---|---|---|
| OA-GAUGE | 1 | missing | [Row 1](#oa-gauge-row-1-the-gauge-group) |
| OA-CHIRAL | 2 | missing | [Row 2](#oa-chiral-row-2-chiral-fermions) |
| OA-GEN | 3 | missing | [Row 3](#oa-gen-row-3-three-generations) |
| OA-TIME | 4 | missing | [Row 4, time direction](#oa-time-row-4-a-lorentzian-time-direction) |
| OA-CONT | 4 | missing | [Row 4, continuum limit](#oa-cont-row-4-the-continuum-limit) |
| OA-GRAV | 5 | missing | [Row 5](#oa-grav-row-5-gravity-and-dynamical-geometry) |
| OA-CONST | 7 | missing | [Row 7](#oa-const-row-7-derived-dimensionless-constants) |

Rows 6 and 8 are not open attacks; see [Rows that are not open](#rows-that-are-not-open). Further open items that are not scorecard rows are under [Other open items](#other-open-items).

---

## OA-GAUGE: row 1, the gauge group

**Label (v0.6 scorecard, row 1):** `missing; SU(2) as dynamical field [E]`

**Where it stands.** SU(2) Wilson ensembles on the chair complex follow weak-coupling perturbation theory (G2 Part A: TOE-G2-W1 [E], TOE-G2-W2 [E]). The finite groups 2I and Q8 freeze, Q8 earlier than predicted (TOE-G2-W3b [E], TOE-G2-W3c [F]). Nothing in the record produces SU(3), U(1) or the product group.

**Invitation: next concrete attempt.** Run the same Part A protocol for SU(3), and then for a product group, on the same complex. Compute the weak-coupling constant from formal perturbation theory first and freeze it, so that the normalised ratio R has a target fixed before any ensemble is run. Do it with the hull's frame connection as background as well as with rigid tiles, so that rule dependence can be seen.

**Proposed test (for a later preregistration).**
- **Pass:** at weak coupling the normalised ratio approaches its frozen target, with standard errors and seeds recorded, in the same way as for SU(2); and at least one recorded observable differs between FR30 and 1387 by more than its numerical error.
- **Fail:** the ratio does not approach its frozen target (recorded as [F] for that prediction), or every recorded observable is rule-blind (recorded as an obstruction: the hull is inert for this sector).
- **What a pass would show.** The protocol extends to a larger group. It would not show that the hull selects that group, because the group is chosen by hand in this test.

---

## OA-CHIRAL: row 2, chiral fermions

**Label (v0.6 scorecard, row 2):** `missing; obstruction (G4)`

**Where it stands.** TOE-G4-O1 [P] (no chirality in the core), TOE-G4-O2 [P] (even number of doublets needed), and G4-INFVOL [X] (the infinite-volume Nielsen-Ninomiya-type statement for the hull is open). No preregistration was frozen for this gap because no computation has been run.

**Invitation: next concrete attempt.** Settle G4-INFVOL. Either state a precise infinite-volume no-go for lattice fermion operators that are covariant on the uniquely ergodic hull (repetitive, but not translation invariant), with every hypothesis written out, or exhibit a hull-covariant construction that escapes it. In parallel, define a chirality index on the finite patches T_L before computing anything, and compute it.

**Proposed test (for a later preregistration).**
- **Pass (theorem route):** a statement with all hypotheses written down, and a proof or counterexample that survives an independent referee read; any finite predicate in it is kernel-checked.
- **Fail (theorem route):** the hypotheses cannot be written so that the statement is non-vacuous, or the proof needs translation invariance that the hull does not have. Record the obstruction, with G4-INFVOL staying open.
- **Pass (computational route):** the index, defined and frozen first, is nonzero, stable across the tested levels, and different between FR30 and 1387.
- **Fail (computational route):** the index is zero at every tested level, or does not depend on the rule. Record it as an obstruction at that scope.

---

## OA-GEN: row 3, three generations

**Label (v0.6 scorecard, row 3):** `missing; obstruction (G5): [P] S3; [C] symmetry count; [E] floor equalities`

**Where it stands.** TOE-G5-S3 [P] (the three shadows are different Q8 characters), G5-COUNT [C] (the symmetry count, with rule 63 the unique S3 case), TOE-G5-none [P] (no mechanism for three generations is known), and G5-R63 [A] (the rule-63 triplet is at most a flavour or colour analogue).

**Invitation: next concrete attempt.** Ask whether the threefold structure is dynamical or only a bookkeeping count. Follow the three shadow floors of the rule-63 and rule-64 cases, and of FR30, along the θ-deformation family and under Wilson-ensemble deformations, and say in advance how a splitting would be read. Separately, state a mechanism and a map to a physical observable before computing anything.

**Proposed test (for a later preregistration).**
- **Pass:** the threefold degeneracy persists under the frozen deformation family, or splits only in the pattern predicted in the frozen text, at the recorded scope.
- **Fail:** the degeneracy is lifted at the first order of the deformation with no residual structure, or the splitting pattern is not the one frozen. Record it as [F] for the prediction that the triplet is dynamical; G5-R63 [A] stays as it is.
- **Note.** A pass on persistence alone is not a mechanism. The mechanism test needs its own frozen statement.

---

## OA-TIME: row 4, a Lorentzian time direction

**Label (v0.6 scorecard, row 4, whole row):** `missing; lattice time direction [P]; one θ-trajectory, L ≤ 6 [E]; its continuum limit [X]`

**Where it stands.** TOE-G3-R0 [P] (a positive self-adjoint transfer matrix for the chair complex times a time lattice, standard construction), and G3-SPECTRUM [E] (the strong-coupling spectrum matches the derivation). Space and time are treated differently, and there is no Lorentz invariance. The scoping note names what is missing: a weak-coupling Hamiltonian limit, a tuned anisotropy between time and space spacings, and a Wick rotation or causal structure.

**Invitation: next concrete attempt.** Build the missing pieces in that order. First, add an anisotropy parameter between the time and space spacings. Second, measure mass gaps and correlation lengths separately along time and along each of the three spatial axes. Third, ask whether one tuned anisotropy makes them agree.

**Proposed test (for a later preregistration).**
- **Pass:** one tuned anisotropy brings the axis-resolved lengths into agreement within a frozen tolerance, and the agreement improves with the level.
- **Fail:** the axis dependence persists or depends on the rule. Record it as an obstruction: no emergent Lorentz-like symmetry on the hull at the tested levels.
- **What a pass would show.** Approximate rotation-like symmetry of one observable at a stated scope. It would not be Lorentzian 3+1 physics without the Wick-rotation and causal-structure steps.

---

## OA-CONT: row 4, the continuum limit

**Label (v0.6 scorecard, row 4, continuum part):** `one θ-trajectory, L ≤ 6 [E]; its continuum limit [X]`

**Where it stands.** TOE-G2-B3 [E] (the scaling trajectory), G2B-LIMIT [X] and G2B-MASS [X] (the continuum limit along θ = κa and its reading as a mass term). The hand-proved brackets for the limit of the second-order coefficient are FR30 [13.232574, 15.465590] and 1387 [14.161980, 16.390966], conditional on Theorems B, C and F, which are unverified hand proofs (see the preprint). The reading that every limit found so far is free physics is recorded as the live conjecture.

**Invitation: next concrete attempt.** Take the trajectory past level 6 with certificates that are committed to the repository, tighten the bracket (the preprint notes that a sloped or periodic cell problem would be a cheap way to tighten the upper end), and go after the open question that decides whether this is more than free physics: does any rule or κ leave an interacting term at the next order beyond the second in θ?

**Proposed test (for a later preregistration).** This restates the refutation route of the preprint's falsification section.
- **Pass (the conjecture survives):** at each new level the second-order coefficient lies inside the certified bracket and the successive differences keep their geometric decay; the next-order term vanishes as θ = κa goes to 0.
- **Fail:** a new level leaves the certified bracket, or the geometric decay stops, or a higher-order term survives as θ = κa goes to 0. Record G2B-LIMIT and G2B-MASS as [F], or, if the bracket conditions are what fail, as an obstruction on the conditions.
- **Either outcome is informative.** A surviving interacting term would be the first sign in this record that the hull is not an inert lattice.

---

## OA-GRAV: row 5, gravity and dynamical geometry

**Label (v0.6 scorecard, row 5):** `missing; obstruction [P] (G6)`

**Where it stands.** TOE-G6-O1 [P] (the chair complex is flat; Regge deficits vanish) and TOE-G6-O2 [P] (dynamical geometry leaves the substitution class), both unverified hand proofs. The frozen T1 run found that tile-wise constant Regge metrics have no local moduli at levels 1 to 5 [C]; the all-level statement is [X]. The Regge and CDT feasibility scoping is in [`gravity/FEASIBILITY_scoping.md`](gravity/FEASIBILITY_scoping.md).

**Invitation: next concrete attempt.** Take the scoping note's candidate routes, which are already written with their first tests: the inflation-complex hierarchy as a curved scale direction (its T5), a spectral-dimension pipeline control (T3), induced gravity from the matter sector (T4), and frame-blindness of linearised 4D Regge (T2). Also attempt the all-level version of the T1 count; the T1 results note names a plausible induction route that has not been carried out.

**Proposed test (for a later preregistration).** These restate the scoping note's predictions, which are [X]; the thresholds are to be frozen before computing.
- **T5, pass:** the Regge action per unit hyperbolic 4-volume converges, with the ratio of successive differences at most 0.75, to the Einstein-Hilbert density of H⁴ (curvature −1 normalisation fixed before computing). **Fail:** it does not converge, or converges elsewhere.
- **T3, pass:** the spectral dimension lies within 5 % of 3 (respectively 4) over σ ∈ [16, 4^{L−1}] for both rules, with no short-distance dimensional reduction. **Fail:** it does not.
- **T2, pass for substitution sensitivity:** the lowest nonzero Hessian eigenvalues of FR30 and 1387 differ by an amount that does not shrink by at least a factor 2 per level. **Fail (the expected outcome in the scoping note):** the difference shrinks, which is recorded as frame-blindness, an obstruction.
- **Any route:** a rule-blind result means the route is lattice gravity on a cubic lattice with the substitution as decoration. Record it as such.

---

## OA-CONST: row 7, derived dimensionless constants

**Label (v0.6 scorecard, row 7):** `missing; model constants derived [E]`

**Where it stands.** The record derives model constants only, such as the certified brackets above. None of them is mapped to a measured physical constant.

**Invitation: next concrete attempt.** Choose one dimensionless quantity of the model that has a certified bracket. Write down, before computing anything further, the physical dimensionless number it is supposed to correspond to, the map between them, and the tolerance. Count every other candidate quantity that was considered.

**Proposed test (for a later preregistration).**
- **Pass:** the map and tolerance were frozen first, the certified bracket is compatible with the target, and the number of candidates considered is printed next to the match.
- **Fail:** there is no frozen map, or a match appears only after choosing among candidates. Record it as an obstruction of the numerology type, and do not report it as a derivation.

---

## Rows that are not open

- **Row 6, quantum mechanics with unitary time evolution.** Label (v0.6 scorecard): `[P] lattice level only` (SC-6 [P], a hand proof, unverified). It is a standard construction at the lattice level. Extending it follows the same path as OA-TIME and OA-CONT.
- **Row 8, the floor as an order parameter (programme-internal).** Label (v0.6 scorecard): `[P] negative` (SC-8 [P], a hand proof, unverified). The floor is not an infinite-volume order parameter for finite-group Wilson ensembles. It is not a physics requirement.

---

## Other open items

These are not scorecard rows, but each is open in the record and each has a proposed pass/fail test, not preregistered (see Ground rules).

### OA-B3: uniformity of the θ³ remainder

**Label (claims.csv):** `TOE-G2-B3 [E]`. The scaling trajectory along θ_L = π 2^(−L) is evidence only. The frozen B3 preregistration and its score notes are in this folder.

**Next attempt:** a uniform-in-L bound on the θ³ remainder, or a level at which it fails.

**Pass:** a bound that is uniform in L, certified or proved. **Fail:** a level at which the remainder breaks the bound, recorded as [F] for the uniformity statement.

### OA-IMPRIM: the imprimitive rules

**Label:** none; the preprint lists these as not proved. Primitivity holds for 1 666 486 rules and fails for 13 130, and for those only Theorem D holds.

**Next attempt:** decide whether the even-level and odd-level limits of the second-order coefficient exist for the 13 130 rules.

**Pass (either way):** a proof or certificate that the two limits exist, together with whether they agree or differ. **Fail:** a rule for which neither can be decided at the tested levels, recorded as an obstruction with the rule identifier.

### OA-VERIFY: the hand proofs

**Label (preprint abstract):** `[P, hand proof, unverified]`.

**Next attempt:** machine-check a precisely stated finite predicate from one of Theorems A to F, or give a written independent referee reading. A kernel check covers the stated finite predicate only; the English gloss stays unverified.

**Pass:** the predicate is kernel-checked and its statement is reviewed against the theorem it encodes. **Fail:** an error or a mismatch between predicate and theorem is found, recorded as [F] for the affected statement.

### OA-FIG5: the upper end of the FIG5-ESTAR enclosure

**Label (paper):** `FIG5-ESTAR [E]` (the source category is [C]; Phase IX is unratified). The recorded obstacle on the upper end was memory exhaustion when re-running the m=5 certificate; see [`fig5-estar-upper-end-rederivation-obstacle-2026-11-09.md`](fig5-estar-upper-end-rederivation-obstacle-2026-11-09.md).

**Next attempt:** regenerate the m=5 certificate on a machine with enough free memory, or re-implement it independently.

**Pass (MATCH):** the regenerated exact rational equals 95969095435322528/10950092349041091, whose outward 10-decimal value is 8.7642270382. **Fail:** it differs, and the difference is recorded, with both values.

---

## The target

The target is to reach the necessary condition for the larger name: every scorecard row moved to proved or certified ([P] or [C]), each at its stated scope and each with its evidence. Reaching it would not by itself justify the name. Until every row is there, the work is called a unification programme. Every item above is a way to move a row, or to show exactly why it cannot yet move.
