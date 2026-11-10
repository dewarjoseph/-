import LeanLab.Scratch.LemmaDNoZero220
import Mathlib.Algebra.Order.Floor.Ring

/-!
# q = (2,2,0): infimum of equal-weight intensity is zero, not attained (scratch)
[P, Lean] For every eps > 0 there is a nonempty equal-weight D-form box
(n = 0; a copies of (1,-1,1), b of (1,1,1), b of (-1,-1,1)) with
|F(2,2,0)|^2 < eps. Here N F = a + 2b cos(4pi/7), with a = floor(-2b cos(4pi/7)).
With `normSq_structureFactor_pos_at_220`: sInf of the box-intensity set is 0 and
no box attains 0. Scope: q = (2,2,0), D-form class, finite equal-weight boxes.
Scratch, not a Lake target, not peer reviewed. Licenses nothing about ETH
(false stays [X]), R2/R4/R5, ScaleLiftToRAM, PrimToRAM, CH-V-020, Theorem F.
-/
namespace LeanLab.Scratch.LemmaDInfZero220
open Complex Finset
open LeanLab.Scratch.LemmaD4 (dot3 structureFactor centroidPoint)
open LeanLab.Scratch.LemmaDIntVec (qReal signedWeight)
open LeanLab.Scratch.LemmaDNoZero220 (qZ220 q220 exp_centroid_at_t0 exp_centroid_at_t4
  exp_centroid_at_tneg4 normSq_structureFactor_pos_at_220)

def v0 : Fin 3 → ℤ := ![1, -1, 1]
def vp : Fin 3 → ℤ := ![1, 1, 1]
def vm : Fin 3 → ℤ := ![-1, -1, 1]

def boxSign (a b : ℕ) (i : ℕ) : Fin 3 → ℤ :=
  if i < a then v0 else if i < a + b then vp else vm

lemma boxSign_pm (a b i : ℕ) : ∀ j, boxSign a b i j = 1 ∨ boxSign a b i j = -1 := by
  intro j
  unfold boxSign
  split_ifs <;> fin_cases j <;> simp [v0, vp, vm]

noncomputable def cθ : ℝ := Real.cos (4 * Real.pi / 7)
noncomputable def sθ : ℝ := Real.sin (4 * Real.pi / 7)

noncomputable def g (a b : ℕ) (i : ℕ) : ℂ :=
  if i < a then 1 else if i < a + b then (cθ : ℂ) - I * sθ else (cθ : ℂ) + I * sθ

lemma summand_eq (a b i : ℕ) :
    exp (2 * Real.pi * I * dot3 q220 (centroidPoint (fun _ => 0) (boxSign a b i))) =
      g a b i := by
  unfold boxSign g
  split_ifs
  · exact exp_centroid_at_t0 _ _ (by simp [signedWeight, qZ220, v0, Fin.sum_univ_three])
  · exact exp_centroid_at_t4 _ _ (by simp [signedWeight, qZ220, vp, Fin.sum_univ_three])
  · exact exp_centroid_at_tneg4 _ _ (by simp [signedWeight, qZ220, vm, Fin.sum_univ_three])

lemma sum_g (a b : ℕ) :
    (∑ i ∈ range (a + b + b), g a b i) = ((a + 2 * b * cθ : ℝ) : ℂ) := by
  rw [sum_range_add, sum_range_add]
  have h1 : (∑ i ∈ range a, g a b i) = a := by
    rw [sum_congr rfl (g := fun _ => (1 : ℂ))]
    · simp
    · intro i hi; simp [g, mem_range.mp hi]
  have h2 : (∑ i ∈ range b, g a b (a + i)) = b * ((cθ : ℂ) - I * sθ) := by
    rw [sum_congr rfl (g := fun _ => (cθ : ℂ) - I * sθ)]
    · simp [mul_sub]
    · intro i hi; have := mem_range.mp hi; simp [g]; omega
  have h3 : (∑ i ∈ range b, g a b (a + b + i)) = b * ((cθ : ℂ) + I * sθ) := by
    rw [sum_congr rfl (g := fun _ => (cθ : ℂ) + I * sθ)]
    · simp [mul_add]
    · intro i hi; simp [g]; omega
  rw [h1, h2, h3]
  push_cast
  ring

/-- Explicit box with counts (a, b, b). -/
lemma F_box (a b : ℕ) :
    structureFactor (fun k : Fin (a + b + b) =>
      centroidPoint (fun _ => 0) (boxSign a b k.val)) q220 =
      (((a + b + b : ℕ) : ℂ))⁻¹ * ((a + 2 * b * cθ : ℝ) : ℂ) := by
  unfold structureFactor
  congr 1
  rw [← sum_g, ← Fin.sum_univ_eq_sum_range]
  exact sum_congr rfl fun k _ => summand_eq a b k.val

lemma cθ_neg : cθ < 0 := by
  unfold cθ
  apply Real.cos_neg_of_pi_div_two_lt_of_lt
  · linarith [Real.pi_pos]
  · linarith [Real.pi_pos]

/-- [P, Lean] Arbitrarily small intensity at q = (2,2,0). -/
theorem exists_box_normSq_lt (ε : ℝ) (hε : 0 < ε) :
    ∃ (N : ℕ) (_ : 1 ≤ N) (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
      (_ : ∀ k j, s k j = 1 ∨ s k j = -1),
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) q220‖ ^ 2 < ε := by
  obtain ⟨b, hb⟩ := exists_nat_gt (1 / ε)
  have hbpos : (0 : ℝ) < b := lt_trans (by positivity) hb
  have hb1 : 1 ≤ b := by exact_mod_cast hbpos
  have hltε : (1 : ℝ) / b < ε := (one_div_lt hε hbpos).mp hb
  set y : ℝ := -2 * b * cθ
  have hy : 0 ≤ y := by have := cθ_neg; dsimp [y]; nlinarith
  set a : ℕ := (⌊y⌋).toNat
  have ha : (a : ℝ) = ⌊y⌋ := by
    dsimp [a]; exact_mod_cast Int.toNat_of_nonneg (Int.floor_nonneg.mpr hy)
  set x : ℝ := a + 2 * b * cθ
  have hx : |x| < 1 := by
    have h1 := Int.floor_le y
    have h2 := Int.lt_floor_add_one y
    rw [abs_lt]; constructor <;> (dsimp [x, y] at *; linarith)
  set N := a + b + b
  have hN : (b : ℝ) ≤ N := by dsimp [N]; push_cast; linarith [(Nat.cast_nonneg a : (0:ℝ) ≤ a)]
  refine ⟨N, by omega, fun _ _ => 0, fun k => boxSign a b k.val,
    fun k => boxSign_pm a b k.val, ?_⟩
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le hbpos hN
  have hNge : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hF' :
      structureFactor (fun k : Fin (a + b + b) =>
        centroidPoint (fun _ => 0) (boxSign a b k.val)) q220 =
        ((N : ℂ)⁻¹ * (x : ℂ)) := by
    simpa [N, x] using F_box a b
  have hnorm :
      ‖structureFactor (fun k : Fin (a + b + b) =>
          centroidPoint (fun _ => 0) (boxSign a b k.val)) q220‖ =
        |x| / (N : ℝ) := by
    rw [hF', norm_mul, norm_inv, Complex.norm_natCast, Complex.norm_real,
      Real.norm_eq_abs]
    field_simp
  have hsq : |x| ^ 2 < 1 := by nlinarith [abs_nonneg x]
  have hpow :
      ‖structureFactor (fun k : Fin N =>
        centroidPoint (fun _ => 0) (boxSign a b k.val)) q220‖ ^ 2 =
        (|x| / (N : ℝ)) ^ 2 := by
    simpa [N] using congrArg (fun t : ℝ => t ^ 2) hnorm
  rw [hpow]
  have hNsq : (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith [hNge]
  calc (|x| / (N : ℝ)) ^ 2 = |x| ^ 2 / (N : ℝ) ^ 2 := by field_simp
    _ < 1 / (N : ℝ) ^ 2 := by gcongr
    _ ≤ 1 / (N : ℝ) := one_div_le_one_div_of_le hNpos hNsq
    _ ≤ 1 / b := one_div_le_one_div_of_le hbpos hN
    _ < ε := hltε

/-- Box-intensity set at q = (2,2,0). -/
noncomputable def boxNormSqSet220 : Set ℝ :=
  { r | ∃ (N : ℕ) (_ : 1 ≤ N) (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
      (_ : ∀ k j, s k j = 1 ∨ s k j = -1),
      r = ‖structureFactor (fun k => centroidPoint (n k) (s k)) q220‖ ^ 2 }

/-- [P, Lean] sInf of equal-weight intensities at q = (2,2,0) is 0. -/
theorem sInf_boxNormSqSet220 : sInf boxNormSqSet220 = 0 := by
  have hlb : ∀ r ∈ boxNormSqSet220, 0 ≤ r := by
    rintro r ⟨N, _, n, s, _, rfl⟩; positivity
  apply le_antisymm
  · by_contra h
    have hpos : 0 < sInf boxNormSqSet220 := lt_of_not_ge h
    obtain ⟨N, hN, n, s, hs, hlt⟩ := exists_box_normSq_lt _ hpos
    have hmem : ‖structureFactor (fun k => centroidPoint (n k) (s k)) q220‖ ^ 2
        ∈ boxNormSqSet220 := ⟨N, hN, n, s, hs, rfl⟩
    have := csInf_le ⟨0, hlb⟩ hmem
    linarith
  · exact Real.sInf_nonneg hlb

/-- [P, Lean] The infimum 0 is not attained. -/
theorem zero_not_mem_boxNormSqSet220 : (0 : ℝ) ∉ boxNormSqSet220 := by
  rintro ⟨N, hN, n, s, hs, h⟩
  have := normSq_structureFactor_pos_at_220 hN n s hs
  linarith

#print axioms exists_box_normSq_lt
#print axioms sInf_boxNormSqSet220
#print axioms zero_not_mem_boxNormSqSet220
end LeanLab.Scratch.LemmaDInfZero220
