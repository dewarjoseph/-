# Chair44 claim ledger: dated addendum, Lemmas A, B, D1-D3 as Lean [P] (scoped)

Date: 2026-11-09 about 10:00 AM PT. Author: Theory of Everything. Task: PM follow-up to the Lemma A step, due 6 PM PT Mon Nov 9, 2026.
Programme label: a unification programme, not a theory of everything.

This addendum does NOT edit the mechanism note `chair44-antidiagonal-mechanism-2026-11-07.md` (sha256 08e4ceed4c1c9b1a4cb9e15b3af5484550636dfe377bb124409761f932cb7e64, re-hashed MATCH 2026-11-09), nor the Lemma A addendum `chair44_lemma_a_lean_addendum_2026-11-09.md` (446a10ad01c77a62bb7a9af8af127ecb6c550c33ae2da323342af46ff18ddc9b, unchanged). **It supersedes one line of the Lemma A addendum:** that addendum's statement that Lemmas B and D were unstarted is now stale; Lean Proof Lab compiled both at about 9:44 AM PT.

## Claim ledger entry (one entry, three lemmas)

| Chair44 §6 item | Label | Exact scope of the Lean statement |
|---|---|---|
| Lemma A | [P, Lean] | Finite equal-weight box structure factor: ‖F_B(q)‖ ≤ 1, 0 ≤ I(q) ≤ 1, I(0) = 1, M ≥ 1, N_B ≥ 1, real points in R³. No decay, no infinite-volume claim. (Details and hashes: Lemma A addendum.) |
| Lemma B | [P, Lean] | Nat facts only: for L ≥ 2, 0 ≤ jx, jy < L, not both zero: L ∣ jx+jy ⇔ jx+jy = L ⇔ jx/L + jy/L = 1 (in Q); on that mask jy = L − jx and gcd(gcd jx jy, L) = gcd(jx, L); den = L ⇔ gcd(jx, L) = 1; for L = 2^m, m ≥ 1, den = L ⇔ jx odd, and exactly 2^m/2 such jx in [1, 2^m−1]. `den L jx jy := L / gcd (gcd jx jy) L`. jz = 0 and qz = 0 are not encoded. No Bragg-weight claim. |
| Lemma D, D1-D3 | [P, Lean] D1–D3, single-box, integer shift, D4 not formalized | Points r_k = n_k − s_k/14 with n_k in Z³ (integer, cast to R) and s_k(j) ∈ {−1, +1}, N ≥ 1; for coordinate a with mu_a = mean sign: D1 F(e_a) = cos(π/7) − i·mu_a·sin(π/7); D2 ‖F(e_a)‖² = cos²(π/7) + mu_a² sin²(π/7); D3 cos²(π/7) ≤ ‖F(e_a)‖² ≤ 1. Single finite point set only; non-integer shifts are not claimed; an integer lo_B is absorbed into n by the caller (a hypothesis form, not a Lean theorem about boxes with a lo_B argument). |
| Lemma D, D4 | hand-proved only (note [P], not Lean) | D4 (equal averaging over nonempty boxes preserves the D3 bounds) is NOT formalized. It stays a short averaging corollary on paper; do not quote it as Lean [P]. |

Do not quote the theorem name `lemma_D` or the file name as the full source Lemma D: the compiled result covers D1–D3 only.

## Independent verification (this agent, 2026-11-09 about 9:56–10:00 AM PT)
- Lean Proof Lab notes re-hashed MATCH: B `/home/box/shared/lean-lab/chair44-lemma-b-scratch-2026-11-09.md` fec50c142edfb6614042f1ca72fc78a200efb033bdc2b75cae8981b6fe536420 (3028 bytes); D `/home/box/shared/lean-lab/chair44-lemma-d-scratch-2026-11-09.md` a21e3fc6863963b253593103b1596c02a4445887aecb1484acf086643f8e1d3e (2668 bytes).
- QIS reverse checks re-hashed MATCH (read, not edited): B `/home/box/shared/qis-eth/lean/kg-lean-lemma-b-scratch-reverse-2026-11-09.md` 8073561c84ebecf3271e2db74e4fabb16a1c18ba26f12f14a19b8c131b82a968; D `/home/box/shared/qis-eth/lean/kg-lean-lemma-d-scratch-reverse-2026-11-09.md` 51b180d71f88bd1116d7bb1c676a304d908aa8eae1a5e983bcd7a1cd3577f1b4.
- Statement fidelity: I read the compiled statements against Chair44 §6 text (lines 109 and 118). B matches the displayed mask/denominator/odd-count statements; D1–D3 match the three displayed identities; the "Equal averaging over any nonempty boxes" sentence of §6 Lemma D is D4 and is absent from Lean, as disclosed.
- Hygiene: grep finds no `sorry`, `native_decide`, `axiom`, or `set_option` in any of the three files.
- My own kernel runs (`cd /workspace/lean-lab-845-orientation-phase && lake env lean <file>`, worktree HEAD 0e23973e84cb8c0e04c04830dd95f81eac3a2590, left clean, nothing edited): LemmaB v1, LemmaB v2, LemmaD all exit 0, zero error lines; `#print axioms` for `lemma_B` and `lemma_D` and every other printed theorem reports only propext, Classical.choice, Quot.sound (a few B theorems use the subset propext, Quot.sound). [C] on a local compile; this is not an independent Mathlib or kernel review.

## Version note (no fault claimed)
Lean's Lemma B note cites LemmaB.lean 1c6103be8be8d8ed7b35e0f54e9f99ffd3f0c918c808a263b1e3c43775f6c626 (3028-byte note, v1). The live `/workspace/lemma-b-scratch/LemmaB.lean` is now v2 23256c17d48d4fb13d96ee0e08e09abd359bfc620ad1c92bcd5024a3b52e1975, which adds an explicit mask bijection (`maskDenSet_bijOn`, `card_maskDenSet_pow_two`) and keeps the earlier statements; v1 is preserved as `LemmaB.v1.lean`. Both compile with the axiom set above. LemmaD.lean ecef2a10bd37fdb3ebfe32052166a80d33d65dc9aeffbbc6b703fb1bad472990 matches Lean's note. Byte-identical copies are in `/home/box/shared/theory-of-everything/lemma-bd-lean-copies/` (LemmaB.v1.lean, LemmaB.v2.lean, LemmaD.lean). Build-summary hashes live: B v2 f7836d468a135985fa5ea0e552fb5821f19aeac5f0cf2b36427743b004a81032, D 08f179dadd7d6f66f422ed0eb89be4f0515bd9470d58f9a19cb7af0e62d6895d.

## What this does NOT change
Fade, hull, Bragg weight, CH-V-020 and Theorem F stay [X]. No claim about ScaleLiftToRAM, PrimToRAM, ETH, or R2/R4/R5. Lemmas C and E and the QC ladder are untouched by this addendum. No v0.6 or claims.csv edit; no Phase IX ratification ask. Scratch Lean files are not Lake targets and not peer reviewed; Note-[P] is not Lean [P] until it builds, and this ledger records that A, B, D1–D3 did.
