import LeanLab.Scratch.LemmaAInt
import LeanLab.Scratch.LemmaD4
import LeanLab.Scratch.LemmaDLink
import LeanLab.Scratch.LemmaDIntVec
import LeanLab.Scratch.LemmaDNoZero220
import LeanLab.Scratch.LemmaDNoZero310211
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.Ring.Int.Parity

/-!
# Chair44 D-form: odd-L¹ non-vanishing and orbit transfer
(public-screen)

Public-screen v2 copy of LeanLab.Scratch.LemmaDOrbitNoZero (official pin src
`eb4783276ef7c0a88b08c15670c24dd74a895cb61dfc8178618e4e2120649fc5`).
Header redacted; theorem bodies are unchanged. This copy is not a
replacement pin.

## Part 1 [P, Lean]. Odd ‖q‖₁ ≤ 5

For every integer wavevector `q` with `‖q‖₁` odd and `≤ 5`, and every
finite nonempty equal-weight D-form box, `F(q) ≠ 0` (also `|F|² > 0`).
In particular this covers the four named vectors
`q ∈ {(2,2,1), (3,1,1), (3,2,0), (4,1,0)}`.

**Argument.** `t = q·s` is odd (same parity as `‖q‖₁`) and `|t| ≤ ‖q‖₁ ≤ 5`,
so `t ∈ {±1,±3,±5}`. Then
`exp(−iπ t/7) = −ζ^k` with `t = 7 − 2k` (`exp_neg_pi_t_eq_neg_zeta`),
giving residues `k ∈ {1,2,3,4,5,6}` (never `0`). The global sign `−1` does
not affect vanishing: `∑ (−ζ^{φ}) = 0` iff `∑ ζ^{φ} = 0`, and the
cyclotomic key lemma forces equal counts, contradicting a missing residue
when `N ≥ 1`.

## Part 2 [P, Lean]. Orbit transfer

For `σ : Equiv.Perm (Fin 3)` and `eps : Fin 3 → ℤ` with `eps j = ±1`, set
`q' j = eps j · q (σ j)`. Non-vanishing of equal-weight D-form `F` at `q`
transfers to `q'`: given a box `(n',s')` at `q'`, the pulled box
`n i = eps(σ⁻¹ i)·n'(σ⁻¹ i)`, `s i = eps(σ⁻¹ i)·s'(σ⁻¹ i)` is admissible
at `q` and `q·r = q'·r'` pointwise, so `F_q = F_{q'}`. Corollaries: the
whole orbits of `(2,2,0)`, `(3,1,0)`, `(2,1,1)`, and every odd-`‖q‖₁≤5`
integer vector (hence of the four named odd vectors).

**Not proved / out of scope:**
* No uniform positive lower bound on `|F|²` (`[X]`).
* Nothing for even `‖q‖₁` beyond the previously proved representatives
  and their orbits; nothing for `‖q‖₁ ≥ 6` except the known `F=0`
  witnesses.
* D-form hypothesis class only. Scratch; not a Lake target; not peer
  reviewed.

This file is source-only and is not a Lake package. It claims nothing
beyond the theorems stated below.

Dated 2026-11-10.
-/

namespace LeanLab.Scratch.LemmaDOrbitNoZero

open Complex Finset
open LeanLab.Scratch.LemmaD4 (dot3 structureFactor centroidPoint)
open LeanLab.Scratch.LemmaDIntVec
  (qReal qL1 signedWeight exp_centroid_int_q zeta7
    exp_neg_pi_t_eq_neg_zeta abs_signedWeight_le_qL1 qL1_eq_sum_abs)
open LeanLab.Scratch.LemmaDNoZero310211
  (countRes countRes_sum_eq_card sum_zeta_eq_countRes
    sum_eq_zero_of_structureFactor_eq_zero
    zeta7_sum_eq_zero_iff_forall_eq
    qZ310 structureFactor_ne_zero_at_310
    qZ211 structureFactor_ne_zero_at_211)
open LeanLab.Scratch.LemmaDNoZero220
  (qZ220 structureFactor_ne_zero_at_220)

/-! ## Odd-t missing-residue criterion (global minus sign) -/

/-- `[P, Lean]` Same as `structureFactor_ne_zero_of_missing_residue`, but
each phase equals `−ζ^{φ(s)}` (odd-`t` case). -/
theorem structureFactor_ne_zero_of_missing_residue_neg {N : ℕ} (hN : 1 ≤ N)
    (qZ : Fin 3 → ℤ)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1)
    (φ : (Fin 3 → ℤ) → Fin 7)
    (hphase : ∀ k,
      exp (2 * Real.pi * I * dot3 (qReal qZ) (centroidPoint (n k) (s k))) =
        -(zeta7 ^ (φ (s k)).val))
    (r0 : Fin 7)
    (hmiss : ∀ (s' : Fin 3 → ℤ), (∀ j, s' j = 1 ∨ s' j = -1) → φ s' ≠ r0) :
    structureFactor (fun k => centroidPoint (n k) (s k)) (qReal qZ) ≠ 0 := by
  intro hF
  have hsum0 :=
    sum_eq_zero_of_structureFactor_eq_zero hN
      (fun k => centroidPoint (n k) (s k)) (qReal qZ) hF
  set φN : Fin N → Fin 7 := fun k => φ (s k)
  have hsumζ :
      (∑ k : Fin N,
          exp (2 * Real.pi * I * dot3 (qReal qZ) (centroidPoint (n k) (s k)))) =
        -∑ k : Fin N, zeta7 ^ (φN k).val := by
    calc
      (∑ k : Fin N,
            exp (2 * Real.pi * I * dot3 (qReal qZ) (centroidPoint (n k) (s k))))
          = ∑ k : Fin N, -(zeta7 ^ (φN k).val) :=
            sum_congr rfl fun k _ => hphase k
      _ = -∑ k : Fin N, zeta7 ^ (φN k).val := by rw [sum_neg_distrib]
  have hζ0 : (∑ k : Fin N, zeta7 ^ (φN k).val) = 0 := by
    have : -∑ k : Fin N, zeta7 ^ (φN k).val = 0 := by
      rw [← hsumζ]; exact hsum0
    exact neg_eq_zero.mp this
  have hcounts :
      (∑ k : Fin N, zeta7 ^ (φN k).val) =
        ∑ r : Fin 7, (countRes φN r : ℂ) * zeta7 ^ r.val :=
    sum_zeta_eq_countRes φN
  have hα :
      (∑ r : Fin 7, ((countRes φN r : ℤ) : ℂ) * zeta7 ^ r.val) = 0 := by
    rw [← hζ0, hcounts]
    refine sum_congr rfl fun r _ => ?_
    simp
  have hall : ∀ i j : Fin 7, (countRes φN i : ℤ) = (countRes φN j : ℤ) :=
    (zeta7_sum_eq_zero_iff_forall_eq (fun r => (countRes φN r : ℤ))).mp hα
  have hr0 : countRes φN r0 = 0 := by
    classical
    refine card_eq_zero.mpr ?_
    apply eq_empty_iff_forall_notMem.mpr
    intro k hk
    simp only [mem_filter, mem_univ, true_and, φN] at hk
    exact hmiss (s k) (hs k) hk
  have hNcard : ∑ r : Fin 7, countRes φN r = N := countRes_sum_eq_card φN
  have hall0 : ∀ r, countRes φN r = 0 := by
    intro r
    have hzi : (countRes φN r : ℤ) = (countRes φN r0 : ℤ) := hall r r0
    have : (countRes φN r : ℤ) = 0 := by simp [hzi, hr0]
    exact_mod_cast this
  have hN0 : N = 0 := by
    rw [← hNcard]
    simp [hall0]
  exact absurd hN0 (ne_of_gt (Nat.zero_lt_of_lt hN))

/-! ## Residues for odd |t| ≤ 5 -/

/-- Residue `k` with `t = 7 − 2k` (so `exp(−iπ t/7) = −ζ^k`), for
`t ∈ {±1,±3,±5}`. -/
def resOddT (t : ℤ) : Fin 7 :=
  if t = 5 then ⟨1, by omega⟩
  else if t = 3 then ⟨2, by omega⟩
  else if t = 1 then ⟨3, by omega⟩
  else if t = -1 then ⟨4, by omega⟩
  else if t = -3 then ⟨5, by omega⟩
  else if t = -5 then ⟨6, by omega⟩
  else ⟨0, by omega⟩

lemma odd_abs_le_five_cases (t : ℤ) (hodd : Odd t) (hle : |t| ≤ 5) :
    t = 5 ∨ t = 3 ∨ t = 1 ∨ t = -1 ∨ t = -3 ∨ t = -5 := by
  have hbound : -5 ≤ t ∧ t ≤ 5 := abs_le.mp hle
  rcases hodd with ⟨m, hm⟩
  have hmlo : -3 ≤ m := by omega
  have hmhi : m ≤ 2 := by omega
  interval_cases m <;> simp [hm]

lemma resOddT_ne_zero_of_mem (t : ℤ)
    (h : t = 5 ∨ t = 3 ∨ t = 1 ∨ t = -1 ∨ t = -3 ∨ t = -5) :
    resOddT t ≠ ⟨0, by omega⟩ := by
  rcases h with h | h | h | h | h | h <;> simp [resOddT, h]

lemma exp_neg_pi_odd_eq_neg_zeta (t : ℤ)
    (h : t = 5 ∨ t = 3 ∨ t = 1 ∨ t = -1 ∨ t = -3 ∨ t = -5) :
    exp (((-(Real.pi * (t : ℝ) / 7) : ℝ) : ℂ) * I) =
      -(zeta7 ^ (resOddT t).val) := by
  rcases h with h | h | h | h | h | h
  · simpa [h, resOddT] using exp_neg_pi_t_eq_neg_zeta 5 1 0 (by norm_num)
  · simpa [h, resOddT] using exp_neg_pi_t_eq_neg_zeta 3 2 0 (by norm_num)
  · simpa [h, resOddT] using exp_neg_pi_t_eq_neg_zeta 1 3 0 (by norm_num)
  · simpa [h, resOddT] using exp_neg_pi_t_eq_neg_zeta (-1) 4 0 (by norm_num)
  · simpa [h, resOddT] using exp_neg_pi_t_eq_neg_zeta (-3) 5 0 (by norm_num)
  · simpa [h, resOddT] using exp_neg_pi_t_eq_neg_zeta (-5) 6 0 (by norm_num)

/-! ## Parity: t and ‖q‖₁ have the same parity -/

lemma even_abs_iff (a : ℤ) : Even (|a|) ↔ Even a := by
  obtain h | h := le_total (0 : ℤ) a
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h, even_neg]

lemma even_mul_sign_iff (a s : ℤ) (hs : s = 1 ∨ s = -1) :
    Even (a * s) ↔ Even a := by
  rcases hs with h | h <;> simp [h, even_neg]

lemma signedWeight_even_iff_qL1_even (q s : Fin 3 → ℤ)
    (hs : ∀ j, s j = 1 ∨ s j = -1) :
    Even (signedWeight q s) ↔ Even (qL1 q) := by
  have hterm : ∀ j, Even (q j * s j) ↔ Even (|q j|) := fun j =>
    (even_mul_sign_iff (q j) (s j) (hs j)).trans (even_abs_iff (q j)).symm
  simp only [signedWeight, Fin.sum_univ_three]
  have e0 := hterm 0
  have e1 := hterm 1
  have e2 := hterm 2
  have hsum :
      Even (q 0 * s 0 + q 1 * s 1 + q 2 * s 2) ↔
        Even (|q 0| + |q 1| + |q 2|) := by
    simp [parity_simps, e0, e1, e2]
  have hqL : (|q 0| + |q 1| + |q 2| : ℤ) = (qL1 q : ℤ) := by
    simpa [Fin.sum_univ_three] using (qL1_eq_sum_abs q).symm
  rw [hsum, hqL, Int.even_natCast]

lemma signedWeight_odd_of_qL1_odd (q s : Fin 3 → ℤ)
    (hs : ∀ j, s j = 1 ∨ s j = -1) (hodd : Odd (qL1 q)) :
    Odd (signedWeight q s) := by
  have hNotEvenNat : ¬ Even (qL1 q) := Nat.not_even_iff_odd.mpr hodd
  have hNotEvenT : ¬ Even (signedWeight q s) := fun he =>
    hNotEvenNat ((signedWeight_even_iff_qL1_even q s hs).mp he)
  exact Int.not_even_iff_odd.mp hNotEvenT

/-! ## Main odd-L¹ ≤ 5 non-vanishing -/

lemma signedWeight_odd_abs_le_five_mem (q s : Fin 3 → ℤ)
    (hs : ∀ j, s j = 1 ∨ s j = -1)
    (hodd : Odd (qL1 q)) (hle : qL1 q ≤ 5) :
    signedWeight q s = 5 ∨ signedWeight q s = 3 ∨ signedWeight q s = 1 ∨
      signedWeight q s = -1 ∨ signedWeight q s = -3 ∨ signedWeight q s = -5 := by
  have htOdd := signedWeight_odd_of_qL1_odd q s hs hodd
  have habs : |signedWeight q s| ≤ (qL1 q : ℤ) := abs_signedWeight_le_qL1 q s hs
  have habs5 : |signedWeight q s| ≤ 5 :=
    le_trans habs (by exact_mod_cast hle)
  exact odd_abs_le_five_cases _ htOdd habs5

def resOdd (q : Fin 3 → ℤ) (s : Fin 3 → ℤ) : Fin 7 :=
  resOddT (signedWeight q s)

lemma resOdd_ne_zero (q s : Fin 3 → ℤ)
    (hs : ∀ j, s j = 1 ∨ s j = -1)
    (hodd : Odd (qL1 q)) (hle : qL1 q ≤ 5) :
    resOdd q s ≠ ⟨0, by omega⟩ :=
  resOddT_ne_zero_of_mem _ (signedWeight_odd_abs_le_five_mem q s hs hodd hle)

lemma exp_centroid_odd_eq_neg_zeta (n s q : Fin 3 → ℤ)
    (hs : ∀ j, s j = 1 ∨ s j = -1)
    (hodd : Odd (qL1 q)) (hle : qL1 q ≤ 5) :
    exp (2 * Real.pi * I * dot3 (qReal q) (centroidPoint n s)) =
      -(zeta7 ^ (resOdd q s).val) := by
  rw [exp_centroid_int_q]
  exact exp_neg_pi_odd_eq_neg_zeta _
    (signedWeight_odd_abs_le_five_mem q s hs hodd hle)

/-- `[P, Lean]` No nonempty finite equal-weight D-form box has `F = 0` at an
integer `q` with `‖q‖₁` odd and `≤ 5`. -/
theorem structureFactor_ne_zero_of_odd_qL1_le_five {N : ℕ} (hN : 1 ≤ N)
    (qZ : Fin 3 → ℤ) (hodd : Odd (qL1 qZ)) (hle : qL1 qZ ≤ 5)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    structureFactor (fun k => centroidPoint (n k) (s k)) (qReal qZ) ≠ 0 :=
  structureFactor_ne_zero_of_missing_residue_neg hN qZ n s hs
    (resOdd qZ)
    (fun k => exp_centroid_odd_eq_neg_zeta (n k) (s k) qZ (hs k) hodd hle)
    ⟨0, by omega⟩
    (fun s' hs' => resOdd_ne_zero qZ s' hs' hodd hle)

theorem normSq_structureFactor_ne_zero_of_odd_qL1_le_five {N : ℕ} (hN : 1 ≤ N)
    (qZ : Fin 3 → ℤ) (hodd : Odd (qL1 qZ)) (hle : qL1 qZ ≤ 5)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    ‖structureFactor (fun k => centroidPoint (n k) (s k)) (qReal qZ)‖ ^ 2 ≠ 0 := by
  intro hz
  have : structureFactor (fun k => centroidPoint (n k) (s k)) (qReal qZ) = 0 :=
    norm_eq_zero.mp (sq_eq_zero_iff.mp hz)
  exact structureFactor_ne_zero_of_odd_qL1_le_five hN qZ hodd hle n s hs this

theorem normSq_structureFactor_pos_of_odd_qL1_le_five {N : ℕ} (hN : 1 ≤ N)
    (qZ : Fin 3 → ℤ) (hodd : Odd (qL1 qZ)) (hle : qL1 qZ ≤ 5)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    0 < ‖structureFactor (fun k => centroidPoint (n k) (s k)) (qReal qZ)‖ ^ 2 :=
  lt_of_le_of_ne (sq_nonneg _)
    (normSq_structureFactor_ne_zero_of_odd_qL1_le_five hN qZ hodd hle n s hs).symm

/-! ### Named odd vectors as corollaries -/

def qZ221 : Fin 3 → ℤ
  | ⟨0, _⟩ => 2
  | ⟨1, _⟩ => 2
  | ⟨2, _⟩ => 1

def qZ311 : Fin 3 → ℤ
  | ⟨0, _⟩ => 3
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 1

def qZ320 : Fin 3 → ℤ
  | ⟨0, _⟩ => 3
  | ⟨1, _⟩ => 2
  | ⟨2, _⟩ => 0

def qZ410 : Fin 3 → ℤ
  | ⟨0, _⟩ => 4
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 0

lemma qL1_221 : qL1 qZ221 = 5 := by
  simp [qL1, qZ221, Fin.sum_univ_three]
lemma qL1_311 : qL1 qZ311 = 5 := by
  simp [qL1, qZ311, Fin.sum_univ_three]
lemma qL1_320 : qL1 qZ320 = 5 := by
  simp [qL1, qZ320, Fin.sum_univ_three]
lemma qL1_410 : qL1 qZ410 = 5 := by
  simp [qL1, qZ410, Fin.sum_univ_three]

lemma odd_qL1_221 : Odd (qL1 qZ221) := by simpa [qL1_221] using (by decide : Odd (5 : ℕ))
lemma odd_qL1_311 : Odd (qL1 qZ311) := by simpa [qL1_311] using (by decide : Odd (5 : ℕ))
lemma odd_qL1_320 : Odd (qL1 qZ320) := by simpa [qL1_320] using (by decide : Odd (5 : ℕ))
lemma odd_qL1_410 : Odd (qL1 qZ410) := by simpa [qL1_410] using (by decide : Odd (5 : ℕ))

lemma qL1_221_le : qL1 qZ221 ≤ 5 := by rw [qL1_221]
lemma qL1_311_le : qL1 qZ311 ≤ 5 := by rw [qL1_311]
lemma qL1_320_le : qL1 qZ320 ≤ 5 := by rw [qL1_320]
lemma qL1_410_le : qL1 qZ410 ≤ 5 := by rw [qL1_410]

theorem structureFactor_ne_zero_at_221 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    structureFactor (fun k => centroidPoint (n k) (s k)) (qReal qZ221) ≠ 0 :=
  structureFactor_ne_zero_of_odd_qL1_le_five hN qZ221 odd_qL1_221 qL1_221_le n s hs

theorem structureFactor_ne_zero_at_311 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    structureFactor (fun k => centroidPoint (n k) (s k)) (qReal qZ311) ≠ 0 :=
  structureFactor_ne_zero_of_odd_qL1_le_five hN qZ311 odd_qL1_311 qL1_311_le n s hs

theorem structureFactor_ne_zero_at_320 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    structureFactor (fun k => centroidPoint (n k) (s k)) (qReal qZ320) ≠ 0 :=
  structureFactor_ne_zero_of_odd_qL1_le_five hN qZ320 odd_qL1_320 qL1_320_le n s hs

theorem structureFactor_ne_zero_at_410 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    structureFactor (fun k => centroidPoint (n k) (s k)) (qReal qZ410) ≠ 0 :=
  structureFactor_ne_zero_of_odd_qL1_le_five hN qZ410 odd_qL1_410 qL1_410_le n s hs

theorem normSq_structureFactor_pos_at_221 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    0 < ‖structureFactor (fun k => centroidPoint (n k) (s k)) (qReal qZ221)‖ ^ 2 :=
  normSq_structureFactor_pos_of_odd_qL1_le_five hN qZ221 odd_qL1_221 qL1_221_le n s hs

theorem normSq_structureFactor_pos_at_311 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    0 < ‖structureFactor (fun k => centroidPoint (n k) (s k)) (qReal qZ311)‖ ^ 2 :=
  normSq_structureFactor_pos_of_odd_qL1_le_five hN qZ311 odd_qL1_311 qL1_311_le n s hs

theorem normSq_structureFactor_pos_at_320 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    0 < ‖structureFactor (fun k => centroidPoint (n k) (s k)) (qReal qZ320)‖ ^ 2 :=
  normSq_structureFactor_pos_of_odd_qL1_le_five hN qZ320 odd_qL1_320 qL1_320_le n s hs

theorem normSq_structureFactor_pos_at_410 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    0 < ‖structureFactor (fun k => centroidPoint (n k) (s k)) (qReal qZ410)‖ ^ 2 :=
  normSq_structureFactor_pos_of_odd_qL1_le_five hN qZ410 odd_qL1_410 qL1_410_le n s hs

/-! ## Part 2: orbit transfer -/

/-- Orbit action on an integer wavevector: `q' j = eps j · q (σ j)`. -/
def orbitQ (q : Fin 3 → ℤ) (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ) :
    Fin 3 → ℤ :=
  fun j => eps j * q (σ j)

/-- Pull a vector from the orbit frame back to the representative frame:
`(pull σ eps v) i = eps(σ⁻¹ i) · v(σ⁻¹ i)`. -/
def pullVec (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ) (v : Fin 3 → ℤ) :
    Fin 3 → ℤ :=
  fun i => eps (σ.symm i) * v (σ.symm i)

lemma pullVec_is_sign (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (s' : Fin 3 → ℤ) (hs' : ∀ j, s' j = 1 ∨ s' j = -1) :
    ∀ i, pullVec σ eps s' i = 1 ∨ pullVec σ eps s' i = -1 := by
  intro i
  simp only [pullVec]
  rcases heps (σ.symm i) with he | he <;> rcases hs' (σ.symm i) with hs | hs <;>
    simp [he, hs]

/-- Pointwise identity: `q · r = q' · r'` after the pull. -/
lemma dot3_orbit_pull (q : Fin 3 → ℤ) (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n' s' : Fin 3 → ℤ) :
    dot3 (qReal q) (centroidPoint (pullVec σ eps n') (pullVec σ eps s')) =
      dot3 (qReal (orbitQ q σ eps)) (centroidPoint n' s') := by
  simp only [dot3, centroidPoint, qReal, orbitQ, pullVec]
  set g : Fin 3 → ℝ := fun i =>
    (q i : ℝ) *
      ((eps (σ.symm i) : ℝ) * (n' (σ.symm i) : ℝ) -
        (eps (σ.symm i) : ℝ) * (s' (σ.symm i) : ℝ) / 14)
  have hLcast :
      (∑ i : Fin 3,
          (q i : ℝ) *
            ((↑(eps (σ.symm i) * n' (σ.symm i)) : ℝ) -
              (↑(eps (σ.symm i) * s' (σ.symm i)) : ℝ) / 14)) =
        ∑ i : Fin 3, g i := by
    refine sum_congr rfl fun i _ => ?_
    simp only [g]
    push_cast
    ring
  have hreindex : (∑ i : Fin 3, g i) =
      ∑ j : Fin 3,
        (q (σ j) : ℝ) *
          ((eps j : ℝ) * (n' j : ℝ) - (eps j : ℝ) * (s' j : ℝ) / 14) := by
    have hcomp := (Equiv.sum_comp σ g).symm
    -- ∑ i, g i = ∑ j, g (σ j)
    refine hcomp.trans ?_
    refine sum_congr rfl fun j _ => ?_
    simp only [g, Equiv.symm_apply_apply]
  have hterm : ∀ j,
      (q (σ j) : ℝ) *
          ((eps j : ℝ) * (n' j : ℝ) - (eps j : ℝ) * (s' j : ℝ) / 14) =
        ((eps j * q (σ j) : ℤ) : ℝ) *
          ((n' j : ℝ) - (s' j : ℝ) / 14) := by
    intro j
    rcases heps j with he | he
    · simp [he]
    · simp [he]; ring
  calc
    (∑ i : Fin 3,
        (q i : ℝ) *
          ((↑(eps (σ.symm i) * n' (σ.symm i)) : ℝ) -
            (↑(eps (σ.symm i) * s' (σ.symm i)) : ℝ) / 14)) =
        ∑ i : Fin 3, g i := hLcast
    _ = ∑ j : Fin 3,
          (q (σ j) : ℝ) *
            ((eps j : ℝ) * (n' j : ℝ) - (eps j : ℝ) * (s' j : ℝ) / 14) := hreindex
    _ = ∑ j : Fin 3,
          ((eps j * q (σ j) : ℤ) : ℝ) *
            ((n' j : ℝ) - (s' j : ℝ) / 14) := sum_congr rfl fun j _ => hterm j

lemma structureFactor_orbit_pull {N : ℕ}
    (q : Fin 3 → ℤ) (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n' : Fin N → Fin 3 → ℤ) (s' : Fin N → Fin 3 → ℤ) :
    structureFactor
        (fun k => centroidPoint (pullVec σ eps (n' k)) (pullVec σ eps (s' k)))
        (qReal q) =
      structureFactor (fun k => centroidPoint (n' k) (s' k))
        (qReal (orbitQ q σ eps)) := by
  unfold structureFactor
  congr 1
  refine sum_congr rfl fun k _ => ?_
  rw [dot3_orbit_pull q σ eps heps (n' k) (s' k)]

/-- `[P, Lean]` Non-vanishing transfers along the coordinate-permutation /
coordinate-sign orbit. -/
theorem structureFactor_ne_zero_orbit_transfer {N : ℕ} (hN : 1 ≤ N)
    (qZ : Fin 3 → ℤ)
    (hq : ∀ {N' : ℕ} (_hN' : 1 ≤ N') (n : Fin N' → Fin 3 → ℤ)
      (s : Fin N' → Fin 3 → ℤ), (∀ k j, s k j = 1 ∨ s k j = -1) →
      structureFactor (fun k => centroidPoint (n k) (s k)) (qReal qZ) ≠ 0)
    (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n' : Fin N → Fin 3 → ℤ) (s' : Fin N → Fin 3 → ℤ)
    (hs' : ∀ k j, s' k j = 1 ∨ s' k j = -1) :
    structureFactor (fun k => centroidPoint (n' k) (s' k))
      (qReal (orbitQ qZ σ eps)) ≠ 0 := by
  intro hF
  have hs_pull : ∀ k j,
      pullVec σ eps (s' k) j = 1 ∨ pullVec σ eps (s' k) j = -1 :=
    fun k => pullVec_is_sign σ eps heps (s' k) (hs' k)
  have hEq := structureFactor_orbit_pull qZ σ eps heps n' s'
  have hFpull :
      structureFactor
          (fun k => centroidPoint (pullVec σ eps (n' k)) (pullVec σ eps (s' k)))
          (qReal qZ) = 0 := by
    rw [hEq]; exact hF
  exact hq hN (fun k => pullVec σ eps (n' k)) (fun k => pullVec σ eps (s' k))
    hs_pull hFpull

/-! ### Orbit corollaries for named representatives -/

theorem structureFactor_ne_zero_orbit_220 {N : ℕ} (hN : 1 ≤ N)
    (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    structureFactor (fun k => centroidPoint (n k) (s k))
      (qReal (orbitQ qZ220 σ eps)) ≠ 0 :=
  structureFactor_ne_zero_orbit_transfer hN qZ220
    (fun {_N'} hN' n' s' hs' => structureFactor_ne_zero_at_220 hN' n' s' hs')
    σ eps heps n s hs

theorem structureFactor_ne_zero_orbit_310 {N : ℕ} (hN : 1 ≤ N)
    (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    structureFactor (fun k => centroidPoint (n k) (s k))
      (qReal (orbitQ qZ310 σ eps)) ≠ 0 :=
  structureFactor_ne_zero_orbit_transfer hN qZ310
    (fun {_N'} hN' n' s' hs' => structureFactor_ne_zero_at_310 hN' n' s' hs')
    σ eps heps n s hs

theorem structureFactor_ne_zero_orbit_211 {N : ℕ} (hN : 1 ≤ N)
    (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    structureFactor (fun k => centroidPoint (n k) (s k))
      (qReal (orbitQ qZ211 σ eps)) ≠ 0 :=
  structureFactor_ne_zero_orbit_transfer hN qZ211
    (fun {_N'} hN' n' s' hs' => structureFactor_ne_zero_at_211 hN' n' s' hs')
    σ eps heps n s hs

theorem structureFactor_ne_zero_orbit_odd_qL1_le_five {N : ℕ} (hN : 1 ≤ N)
    (qZ : Fin 3 → ℤ) (hodd : Odd (qL1 qZ)) (hle : qL1 qZ ≤ 5)
    (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    structureFactor (fun k => centroidPoint (n k) (s k))
      (qReal (orbitQ qZ σ eps)) ≠ 0 :=
  structureFactor_ne_zero_orbit_transfer hN qZ
    (fun {_N'} hN' n' s' hs' =>
      structureFactor_ne_zero_of_odd_qL1_le_five hN' qZ hodd hle n' s' hs')
    σ eps heps n s hs

theorem structureFactor_ne_zero_orbit_221 {N : ℕ} (hN : 1 ≤ N)
    (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    structureFactor (fun k => centroidPoint (n k) (s k))
      (qReal (orbitQ qZ221 σ eps)) ≠ 0 :=
  structureFactor_ne_zero_orbit_odd_qL1_le_five hN qZ221 odd_qL1_221
    qL1_221_le σ eps heps n s hs

theorem structureFactor_ne_zero_orbit_311 {N : ℕ} (hN : 1 ≤ N)
    (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    structureFactor (fun k => centroidPoint (n k) (s k))
      (qReal (orbitQ qZ311 σ eps)) ≠ 0 :=
  structureFactor_ne_zero_orbit_odd_qL1_le_five hN qZ311 odd_qL1_311
    qL1_311_le σ eps heps n s hs

theorem structureFactor_ne_zero_orbit_320 {N : ℕ} (hN : 1 ≤ N)
    (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    structureFactor (fun k => centroidPoint (n k) (s k))
      (qReal (orbitQ qZ320 σ eps)) ≠ 0 :=
  structureFactor_ne_zero_orbit_odd_qL1_le_five hN qZ320 odd_qL1_320
    qL1_320_le σ eps heps n s hs

theorem structureFactor_ne_zero_orbit_410 {N : ℕ} (hN : 1 ≤ N)
    (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    structureFactor (fun k => centroidPoint (n k) (s k))
      (qReal (orbitQ qZ410 σ eps)) ≠ 0 :=
  structureFactor_ne_zero_orbit_odd_qL1_le_five hN qZ410 odd_qL1_410
    qL1_410_le σ eps heps n s hs

#print axioms structureFactor_ne_zero_of_missing_residue_neg
#print axioms structureFactor_ne_zero_of_odd_qL1_le_five
#print axioms structureFactor_ne_zero_at_221
#print axioms structureFactor_ne_zero_at_311
#print axioms structureFactor_ne_zero_at_320
#print axioms structureFactor_ne_zero_at_410
#print axioms structureFactor_ne_zero_orbit_transfer
#print axioms structureFactor_ne_zero_orbit_220
#print axioms structureFactor_ne_zero_orbit_310
#print axioms structureFactor_ne_zero_orbit_211
#print axioms structureFactor_ne_zero_orbit_221
#print axioms structureFactor_ne_zero_orbit_311
#print axioms structureFactor_ne_zero_orbit_320
#print axioms structureFactor_ne_zero_orbit_410

end LeanLab.Scratch.LemmaDOrbitNoZero
