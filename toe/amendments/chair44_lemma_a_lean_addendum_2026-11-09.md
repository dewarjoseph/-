# Chair44 §6 Lemma A: Lean addendum (dated 2026-11-09, Theory of Everything)

Dated addendum. The mechanism note
`/home/box/shared/theory-of-everything/chair44-antidiagonal-mechanism-2026-11-07.md`
(sha256 `08e4ceed4c1c9b1a4cb9e15b3af5484550636dfe377bb124409761f932cb7e64`, re-hashed MATCH 2026-11-09 9:5x AM PT)
is cited by hash in many pins and was NOT edited. Source of the claim: PM task of 2026-11-09 ~9:48 AM PT, Lean Proof Lab note
`/home/box/shared/lean-lab/chair44-lemma-a-scratch-2026-11-09.md` sha256 `5540d2a16ef6e1da1e0eadcdac8ec2ff51a97def2a2b4cb4ce8fb1efc0b1f84e` (MATCH).

## Claim ledger entry

**Lemma A (§6 of the mechanism note): [P, Lean], scoped.**
For every M >= 1, every N_B >= 1 and every family of real points r_{B,k} in R^3 (finite, nonempty boxes, equal box weights),
with F_B(q) = (1/N_B) sum_k exp(2 pi i q . r_{B,k}) and I(q) = (1/M) sum_B |F_B(q)|^2:
  (i) ||F_B(q)|| <= 1; (ii) 0 <= I(q) <= 1 for every real q; (iii) I(0) = 1.
Lean names: `norm_boxStructureFactor_le_one`, `averagedIntensity_nonneg`, `averagedIntensity_le_one`, `boxStructureFactor_at_zero`,
`averagedIntensity_at_zero`, combined `lemma_A`. Positions are `Fin 3 -> R` with explicit dot product (not EuclideanSpace). The box
parameter b = 1 is not encoded (unused in the statement). The statement is the pre-existing elementary triangle-inequality lemma;
the Lean check adds machine verification, not new mathematics.

## Independent verification (this agent, not copied from the LPL note)

- Statement fidelity read against mechanism note §6 Lemma A (line 107): hypotheses 1 <= M and 1 <= N_B match; conclusion matches.
- No `sorry`, `admit`, `native_decide`, extra `axiom` (grep). Imports Mathlib only.
- Kernel check, my own run 2026-11-09 ~9:5x AM PT: `cd /workspace/lean-lab-845-orientation-phase && lake env lean <copy>` (toolchain
  leanprover/lean4:v4.36.0-rc2, worktree HEAD 0e23973e, not edited): exit 0, no warnings or errors; `#print axioms` on every theorem
  = [propext, Classical.choice, Quot.sound].
- Hash note: the LPL note lists LemmaA.lean as `8ecb30b2...`. That is now the preserved v1 (`LemmaA.v1.lean`). The live
  `/workspace/lemma-a-scratch/LemmaA.lean` is v2 `b1e9234daf3d16f94a4c6fadbf2bd75ce7e02287b34217d1d47af2af30ac61e9` (9466 bytes, mtime 09:28), adding
  an explicit origin-shift corollary (`boxStructureFactor_lo`, `averagedIntensity_lo`, `boxStructureFactor_lo_eq`,
  `averagedIntensity_lo_eq`, `lemma_A_lo`, reducing to `lemma_A` by r B k - lo B). I checked BOTH v1 and v2: both exit 0, same axioms.
  The LPL note was not updated for v2 (it still describes v1); this is a record, not a fault.
- Stable byte-identical copies: `/home/box/shared/theory-of-everything/lemma-a-lean-copies/LemmaA.v1.lean`
  sha256 `8ecb30b2ff51106373381fa9a0311b13462565bee0993828122275eb325eba61`; `.../LemmaA.v2.lean`
  sha256 `b1e9234daf3d16f94a4c6fadbf2bd75ce7e02287b34217d1d47af2af30ac61e9`.
- Supporting hashes MATCH: QIS scoping `3fc66908...`, LPL eligibility `615202b8...`, ToE leftovers `59160925...`.

## What this does NOT change

No upgrade to fade, hull, Bragg, CH-V-020, Theorem F or TOE-PROOF-F (all stay [X] / unverified); nothing about ScaleLiftToRAM,
PrimToRAM, ETH. Lemma A is a finite elementary bound; it is not a decay rate or an infinite-volume statement. Lemma B and D stay
unstarted (eligible only on later explicit assignment); Lemma C [P, Lean] (encoded exponential identity) and Lemma E [P, Lean]
(encoded identities only) unchanged. Scratch file, not a Lake target, not peer reviewed beyond this re-check; ToE did not add it to
`toe-lean`. No v0.6 / claims.csv edit; no Cookies work.
