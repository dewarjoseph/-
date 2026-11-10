import LeanLab.Scratch.LemmaAInt
import LeanLab.Scratch.LemmaD4
import LeanLab.Scratch.LemmaDLink

/-!
# Chair44 D-form bounds at general integer vectors q ∈ ℤ³
(public-screen)

Public-screen v2 copy of LeanLab.Scratch.LemmaDIntVec (official pin src
`281acaebdedf37d574f04e1f42da77b917280d597671dc1f5e3d5afa1e64997e`).
Header redacted; theorem bodies are unchanged. This copy is not a
replacement pin.

After LemmaDAxisMultiple, the D-form
`r = n − s/14` (n integer vector, s entries ±1) was bounded at axis-integer
multiples `q = m·e_a`. This file treats general **integer** wavevectors.

**(A) [P, Lean] scoped lower bound, named class `qL1 q ≤ 3`.**
For `q : Fin 3 → ℤ` with `L := ∑ |q i| ≤ 3`, and D-form points,
`exp(2πi q·r_k) = exp(−iπ t_k/7)` with integer `t_k := ∑ q_j s_{k,j}` and
`|t_k| ≤ L`. Each unit complex has real part `cos(π t_k/7) ≥ cos(Lπ/7) > 0`
(using `|t_k| ≤ L ≤ 3` and cos antitone on `[0, π]`), so
`Re F ≥ cos(Lπ/7)` and `cos(Lπ/7)² ≤ |F|² ≤ 1`. Same for equal-weight M-box
averages and (via LemmaDLink) integer origins. For axis vectors with `|m| ≤ 3`
the numerical bound coincides with LemmaDAxisMultiple; the new content is
non-axis integer `q` such as `(1,1,0)`, `(1,1,1)`, `(2,1,0)`. Says nothing for
`L ≥ 4` (a positive lower bound there is neither proved nor refuted here).

**(B) [F, Lean] integer non-axis counterexample `q = (1, 2, 4)`.**
Seven D-form points with `n ≡ 0` and the seven sign vectors
`(±1,±1,±1) \ {(−1,−1,−1)}` give phases `t ∈ {±1,±3,±5,7}` whose
`exp(−iπ t/7)` are exactly the negatives of all 7th roots of unity, hence
`F(q) = 0` and `|F|² = 0 < cos²(π/7)`. Same box repeated across an M-box
family yields average 0. This is a counterexample **inside** the D-form
hypothesis class at one integer vector; it shows no D3-style positive lower
bound holds for all of `ℤ³`.

Fidelity:
* D-form hypothesis class only (not the real 13/14 geometry).
* Finite statements; scratch; not a Lake target; not peer reviewed.

This file is source-only and is not a Lake package. It claims nothing
beyond the theorems stated below.

Dated 2026-11-10.
-/

namespace LeanLab.Scratch.LemmaDIntVec

open Complex Finset
open LeanLab.Scratch.LemmaD4 (dot3 structureFactor centroidPoint exp_two_pi_I_int
  avg_mem_Icc)
open LeanLab.Scratch.LemmaAInt (dForm intOrigin averagedIntensity averagedIntensity_lo
  averagedIntensity_lo_dForm_int boxStructureFactor norm_boxStructureFactor_le_one)
open LeanLab.Scratch.LemmaDLink (dForm_eq_centroidPoint_D4
  averagedIntensity_eq_avg_normSq_structureFactor boxStructureFactor_eq_structureFactor)

/-! ## Integer wavevector helpers -/

/-- Cast an integer wavevector to a real wavevector. -/
def qReal (q : Fin 3 → ℤ) : Fin 3 → ℝ := fun j => (q j : ℝ)

/-- ℓ¹ norm `L := ∑ |q i|`. -/
def qL1 (q : Fin 3 → ℤ) : ℕ := ∑ i : Fin 3, (q i).natAbs

/-- Integer signed weight `t := ∑ q_j s_j`. -/
def signedWeight (q s : Fin 3 → ℤ) : ℤ := ∑ j : Fin 3, q j * s j

lemma qL1_eq_sum_abs (q : Fin 3 → ℤ) :
    (qL1 q : ℤ) = ∑ i : Fin 3, |q i| := by
  simp [qL1]

lemma abs_signedWeight_le_qL1 (q s : Fin 3 → ℤ)
    (hs : ∀ j, s j = 1 ∨ s j = -1) :
    |signedWeight q s| ≤ (qL1 q : ℤ) := by
  have habs : ∀ j, |q j * s j| = |q j| := by
    intro j
    rcases hs j with h | h <;> simp [h]
  calc
    |signedWeight q s| = |∑ j : Fin 3, q j * s j| := rfl
    _ ≤ ∑ j : Fin 3, |q j * s j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j : Fin 3, |q j| := by simp [habs]
    _ = (qL1 q : ℤ) := (qL1_eq_sum_abs q).symm

/-! ## Single-summand phase at integer q -/

lemma dot3_qReal_centroid (n s : Fin 3 → ℤ) (q : Fin 3 → ℤ) :
    dot3 (qReal q) (centroidPoint n s) =
      ((∑ j : Fin 3, q j * n j : ℤ) : ℝ) - (signedWeight q s : ℝ) / 14 := by
  simp only [dot3, qReal, centroidPoint, signedWeight, Fin.sum_univ_three]
  push_cast
  ring

lemma exp_centroid_int_q (n s : Fin 3 → ℤ) (q : Fin 3 → ℤ) :
    exp (2 * Real.pi * I * dot3 (qReal q) (centroidPoint n s)) =
      exp (((-(Real.pi * (signedWeight q s : ℝ) / 7) : ℝ) : ℂ) * I) := by
  rw [dot3_qReal_centroid]
  have hexp :
      (2 * Real.pi * I *
          ((((∑ j : Fin 3, q j * n j : ℤ) : ℝ) - (signedWeight q s : ℝ) / 14) : ℝ) : ℂ) =
        (2 * Real.pi * I * ((∑ j : Fin 3, q j * n j : ℤ) : ℝ) : ℂ) +
          (((-(Real.pi * (signedWeight q s : ℝ) / 7) : ℝ) : ℂ) * I) := by
    push_cast
    ring
  rw [hexp, exp_add, exp_two_pi_I_int (∑ j : Fin 3, q j * n j), one_mul]

lemma re_exp_centroid_int_q (n s : Fin 3 → ℤ) (q : Fin 3 → ℤ) :
    (exp (2 * Real.pi * I * dot3 (qReal q) (centroidPoint n s))).re =
      Real.cos (Real.pi * (signedWeight q s : ℝ) / 7) := by
  rw [exp_centroid_int_q]
  have h := Complex.exp_ofReal_mul_I (-(Real.pi * (signedWeight q s : ℝ) / 7))
  rw [h]
  simp only [add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im, Real.cos_neg]
  ring

lemma cos_signedWeight_ge (t : ℤ) (L : ℕ) (hL : L ≤ 3) (ht : |t| ≤ (L : ℤ)) :
    Real.cos ((L : ℝ) * Real.pi / 7) ≤ Real.cos (Real.pi * (t : ℝ) / 7) := by
  have heven : Real.cos (Real.pi * (t : ℝ) / 7) =
      Real.cos (Real.pi * (|t| : ℝ) / 7) := by
    calc
      Real.cos (Real.pi * (t : ℝ) / 7)
          = Real.cos |Real.pi * (t : ℝ) / 7| := (Real.cos_abs _).symm
      _ = Real.cos (|Real.pi| * |(t : ℝ)| / |7|) := by rw [abs_div, abs_mul]
      _ = Real.cos (Real.pi * |(t : ℝ)| / 7) := by
            rw [abs_of_nonneg Real.pi_pos.le, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 7)]
      _ = Real.cos (Real.pi * (|t| : ℝ) / 7) := rfl
  rw [heven]
  have h0 : 0 ≤ Real.pi * (|t| : ℝ) / 7 :=
    div_nonneg (mul_nonneg Real.pi_pos.le (by exact_mod_cast abs_nonneg t)) (by norm_num)
  have hLπ : (L : ℝ) * Real.pi / 7 ≤ Real.pi := by
    have hL7 : (L : ℝ) ≤ 7 := by exact_mod_cast (le_trans hL (by norm_num : (3 : ℕ) ≤ 7))
    have hdiv : (L : ℝ) / 7 ≤ 1 := (div_le_one (by norm_num : (0 : ℝ) < 7)).mpr hL7
    calc
      (L : ℝ) * Real.pi / 7 = (L : ℝ) / 7 * Real.pi := by ring
      _ ≤ 1 * Real.pi := mul_le_mul_of_nonneg_right hdiv Real.pi_pos.le
      _ = Real.pi := one_mul _
  have hxy : Real.pi * (|t| : ℝ) / 7 ≤ (L : ℝ) * Real.pi / 7 := by
    have habs : (|t| : ℝ) ≤ (L : ℝ) := by exact_mod_cast ht
    calc
      Real.pi * (|t| : ℝ) / 7 = (|t| : ℝ) * Real.pi / 7 := by ring
      _ ≤ (L : ℝ) * Real.pi / 7 :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right habs Real.pi_pos.le) (by norm_num)
  exact Real.cos_le_cos_of_nonneg_of_le_pi h0 hLπ hxy

lemma cos_L_pi_div_seven_nonneg (L : ℕ) (hL : L ≤ 3) :
    0 ≤ Real.cos ((L : ℝ) * Real.pi / 7) := by
  apply Real.cos_nonneg_of_mem_Icc
  refine ⟨?_, ?_⟩
  · have hnn : 0 ≤ (L : ℝ) * Real.pi / 7 :=
      div_nonneg (mul_nonneg (Nat.cast_nonneg _) Real.pi_pos.le) (by norm_num)
    exact le_trans (neg_nonpos.mpr (div_nonneg Real.pi_pos.le (by norm_num))) hnn
  · have hL3 : (L : ℝ) ≤ 3 := by exact_mod_cast hL
    have h1 : (L : ℝ) * Real.pi / 7 ≤ 3 * Real.pi / 7 :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hL3 Real.pi_pos.le) (by norm_num)
    have h2 : 3 * Real.pi / 7 ≤ Real.pi / 2 := by
      rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 7) (by norm_num : (0 : ℝ) < 2)]
      nlinarith [Real.pi_pos]
    exact le_trans h1 h2

/-! ## (A) Single-box and average bounds -/

lemma re_mul_inv_sum {N : ℕ} (z : Fin N → ℂ) :
    (((N : ℂ)⁻¹ * ∑ k : Fin N, z k).re) =
      (N : ℝ)⁻¹ * ∑ k : Fin N, (z k).re := by
  have hInv : (N : ℂ)⁻¹ = ↑((N : ℝ)⁻¹) := by
    rw [← ofReal_natCast N, ← ofReal_inv]
  rw [hInv, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, Complex.re_sum]

lemma re_structureFactor_int_q_ge {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1)
    (q : Fin 3 → ℤ) (hL : qL1 q ≤ 3) :
    Real.cos ((qL1 q : ℝ) * Real.pi / 7) ≤
      (structureFactor (fun k => centroidPoint (n k) (s k)) (qReal q)).re := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hN)
  unfold structureFactor
  rw [re_mul_inv_sum]
  have hterm : ∀ k,
      Real.cos ((qL1 q : ℝ) * Real.pi / 7) ≤
        (exp (2 * Real.pi * I * dot3 (qReal q) (centroidPoint (n k) (s k)))).re := by
    intro k
    rw [re_exp_centroid_int_q]
    exact cos_signedWeight_ge (signedWeight q (s k)) (qL1 q) hL
      (abs_signedWeight_le_qL1 q (s k) (fun j => hs k j))
  have hsum :
      (N : ℝ) * Real.cos ((qL1 q : ℝ) * Real.pi / 7) ≤
        ∑ k : Fin N,
          (exp (2 * Real.pi * I * dot3 (qReal q) (centroidPoint (n k) (s k)))).re := by
    simpa [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] using
      (Finset.sum_le_sum fun (k : Fin N) (_ : k ∈ univ) => hterm k)
  exact (le_inv_mul_iff₀ hNpos).mpr hsum

theorem cos_sq_le_normSq_structureFactor_int_q_le_one {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1)
    (q : Fin 3 → ℤ) (hL : qL1 q ≤ 3) :
    Real.cos ((qL1 q : ℝ) * Real.pi / 7) ^ 2 ≤
        ‖structureFactor (fun k => centroidPoint (n k) (s k)) (qReal q)‖ ^ 2 ∧
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) (qReal q)‖ ^ 2 ≤ 1 := by
  set F := structureFactor (fun k => centroidPoint (n k) (s k)) (qReal q)
  set c := Real.cos ((qL1 q : ℝ) * Real.pi / 7)
  have hc0 : 0 ≤ c := cos_L_pi_div_seven_nonneg (qL1 q) hL
  have hre : c ≤ F.re := re_structureFactor_int_q_ge hN n s hs q hL
  have hcF : c ≤ ‖F‖ := le_trans hre (Complex.re_le_norm F)
  have hlo : c ^ 2 ≤ ‖F‖ ^ 2 := by nlinarith
  have hup : ‖F‖ ^ 2 ≤ 1 := by
    have hle : ‖F‖ ≤ 1 := by
      have heq : F = boxStructureFactor (fun k => centroidPoint (n k) (s k)) (qReal q) :=
        (boxStructureFactor_eq_structureFactor
          (fun k => centroidPoint (n k) (s k)) (qReal q)).symm
      simpa [F, heq] using
        norm_boxStructureFactor_le_one hN (fun k => centroidPoint (n k) (s k)) (qReal q)
    nlinarith [norm_nonneg F]
  exact ⟨hlo, hup⟩

theorem lemma_D_intVec_avg {M : ℕ} (hM : 1 ≤ M)
    (N : Fin M → ℕ) (hN : ∀ B, 1 ≤ N B)
    (n : (B : Fin M) → Fin (N B) → Fin 3 → ℤ)
    (s : (B : Fin M) → Fin (N B) → Fin 3 → ℤ)
    (hs : ∀ B k j, s B k j = 1 ∨ s B k j = -1)
    (q : Fin 3 → ℤ) (hL : qL1 q ≤ 3) :
    Real.cos ((qL1 q : ℝ) * Real.pi / 7) ^ 2 ≤
        (M : ℝ)⁻¹ * ∑ B : Fin M,
          ‖structureFactor (fun k => centroidPoint (n B k) (s B k)) (qReal q)‖ ^ 2 ∧
      (M : ℝ)⁻¹ * ∑ B : Fin M,
          ‖structureFactor (fun k => centroidPoint (n B k) (s B k)) (qReal q)‖ ^ 2 ≤ 1 := by
  set I : Fin M → ℝ := fun B =>
    ‖structureFactor (fun k => centroidPoint (n B k) (s B k)) (qReal q)‖ ^ 2
  set c2 := Real.cos ((qL1 q : ℝ) * Real.pi / 7) ^ 2
  have hx : ∀ B, c2 ≤ I B ∧ I B ≤ 1 := fun B =>
    cos_sq_le_normSq_structureFactor_int_q_le_one (hN B) (n B) (s B) (hs B) q hL
  simpa [I, c2] using avg_mem_Icc hM I c2 1 hx

theorem lemma_D_intVec_lo_int {M : ℕ} (hM : 1 ≤ M)
    (N : Fin M → ℕ) (hN : ∀ B, 1 ≤ N B)
    (n : (B : Fin M) → Fin (N B) → Fin 3 → ℤ)
    (s : (B : Fin M) → Fin (N B) → Fin 3 → ℤ)
    (hs : ∀ B k j, s B k j = 1 ∨ s B k j = -1)
    (lo : Fin M → Fin 3 → ℤ)
    (q : Fin 3 → ℤ) (hL : qL1 q ≤ 3) :
    Real.cos ((qL1 q : ℝ) * Real.pi / 7) ^ 2 ≤
        averagedIntensity_lo
          (fun B k => centroidPoint (n B k) (s B k)) (intOrigin lo) (qReal q) ∧
      averagedIntensity_lo
          (fun B k => centroidPoint (n B k) (s B k)) (intOrigin lo) (qReal q) ≤ 1 := by
  have hpts : (fun B k => centroidPoint (n B k) (s B k)) =
      (fun B k => dForm (n B k) (s B k)) := by
    funext B k; exact (dForm_eq_centroidPoint_D4 (n B k) (s B k)).symm
  rw [hpts, averagedIntensity_lo_dForm_int n s lo (qReal q)]
  rw [averagedIntensity_eq_avg_normSq_structureFactor]
  exact lemma_D_intVec_avg hM N hN (fun B k => n B k - lo B) s hs q hL

/-! ## (B) Counterexample at q = (1, 2, 4) -/

/-- Witness integer wavevector `q = (1, 2, 4)`. -/
def witness_qZ : Fin 3 → ℤ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 2
  | ⟨2, _⟩ => 4

noncomputable def witness_q : Fin 3 → ℝ := qReal witness_qZ

/-- The seven sign vectors `(±1,±1,±1)` except `(−1,−1,−1)`, indexed by `Fin 7`. -/
def witness_s7 : Fin 7 → Fin 3 → ℤ
  | ⟨0, _⟩ => fun
    | ⟨0, _⟩ => 1 | ⟨1, _⟩ => 1 | ⟨2, _⟩ => 1
  | ⟨1, _⟩ => fun
    | ⟨0, _⟩ => 1 | ⟨1, _⟩ => 1 | ⟨2, _⟩ => -1
  | ⟨2, _⟩ => fun
    | ⟨0, _⟩ => 1 | ⟨1, _⟩ => -1 | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => fun
    | ⟨0, _⟩ => 1 | ⟨1, _⟩ => -1 | ⟨2, _⟩ => -1
  | ⟨4, _⟩ => fun
    | ⟨0, _⟩ => -1 | ⟨1, _⟩ => 1 | ⟨2, _⟩ => 1
  | ⟨5, _⟩ => fun
    | ⟨0, _⟩ => -1 | ⟨1, _⟩ => 1 | ⟨2, _⟩ => -1
  | ⟨6, _⟩ => fun
    | ⟨0, _⟩ => -1 | ⟨1, _⟩ => -1 | ⟨2, _⟩ => 1

def witness_n7 : Fin 7 → Fin 3 → ℤ := fun _ _ => 0

lemma witness_s7_is_sign : ∀ k j, witness_s7 k j = 1 ∨ witness_s7 k j = -1 := by
  intro k j
  fin_cases k <;> fin_cases j <;> simp [witness_s7]

lemma signedWeight_witness :
    signedWeight witness_qZ (witness_s7 0) = 7 ∧
    signedWeight witness_qZ (witness_s7 1) = -1 ∧
    signedWeight witness_qZ (witness_s7 2) = 3 ∧
    signedWeight witness_qZ (witness_s7 3) = -5 ∧
    signedWeight witness_qZ (witness_s7 4) = 5 ∧
    signedWeight witness_qZ (witness_s7 5) = -3 ∧
    signedWeight witness_qZ (witness_s7 6) = 1 := by
  simp [signedWeight, witness_qZ, witness_s7, Fin.sum_univ_three]

/-- Primitive 7th root of unity `ζ = exp(2πi/7)`. -/
noncomputable def zeta7 : ℂ := exp (2 * Real.pi * I / 7)

lemma isPrimitiveRoot_zeta7 : IsPrimitiveRoot zeta7 7 :=
  Complex.isPrimitiveRoot_exp 7 (by decide)

lemma zeta7_pow (k : ℕ) :
    zeta7 ^ k = exp (2 * Real.pi * I * k / 7) := by
  rw [zeta7, ← exp_nat_mul]
  congr 1
  ring

lemma neg_zeta7_pow (k : ℕ) :
    -(zeta7 ^ k) =
      exp ((((↑(7 + 2 * k) * Real.pi / 7) : ℝ) : ℂ) * I) := by
  rw [zeta7_pow]
  have hπ : exp (↑Real.pi * I) = -1 := Complex.exp_pi_mul_I
  calc
    - exp (2 * Real.pi * I * k / 7)
        = exp (↑Real.pi * I) * exp (2 * Real.pi * I * k / 7) := by rw [hπ]; ring
    _ = exp (↑Real.pi * I + 2 * Real.pi * I * k / 7) := by rw [← exp_add]
    _ = exp ((((↑(7 + 2 * k) * Real.pi / 7) : ℝ) : ℂ) * I) := by
          congr 1
          push_cast
          ring

/-- If `t = 7 − 2k − 14m` then `exp(−(π t/7) I) = −ζ^k`. -/
lemma exp_neg_pi_t_eq_neg_zeta (t : ℤ) (k : ℕ) (m : ℤ)
    (h : t = (7 : ℤ) - 2 * (k : ℤ) - 14 * m) :
    exp (((-(Real.pi * (t : ℝ) / 7) : ℝ) : ℂ) * I) = -(zeta7 ^ k) := by
  rw [neg_zeta7_pow]
  have hθ : (-(Real.pi * (t : ℝ) / 7) : ℝ) =
      (↑(7 + 2 * k) * Real.pi / 7) + 2 * Real.pi * ((m - 1 : ℤ) : ℝ) := by
    have ht : (t : ℝ) = (7 : ℝ) - 2 * (k : ℝ) - 14 * (m : ℝ) := by exact_mod_cast h
    rw [ht]; push_cast; ring
  have hform :
      (((-(Real.pi * (t : ℝ) / 7) : ℝ) : ℂ) * I) =
        ((((↑(7 + 2 * k) * Real.pi / 7) : ℝ) : ℂ) * I) +
          ((((2 * Real.pi * ((m - 1 : ℤ) : ℝ)) : ℝ) : ℂ) * I) := by
    rw [hθ, ofReal_add, add_mul]
  rw [hform, exp_add]
  have hper : exp ((((2 * Real.pi * ((m - 1 : ℤ) : ℝ)) : ℝ) : ℂ) * I) = 1 := by
    convert exp_two_pi_I_int (m - 1) using 2
    push_cast; ring
  rw [hper, mul_one]

lemma witness_exp_eq_neg_zeta :
    (exp (2 * Real.pi * I * dot3 witness_q (centroidPoint (witness_n7 0) (witness_s7 0))) =
        -(zeta7 ^ 0)) ∧
    (exp (2 * Real.pi * I * dot3 witness_q (centroidPoint (witness_n7 1) (witness_s7 1))) =
        -(zeta7 ^ 4)) ∧
    (exp (2 * Real.pi * I * dot3 witness_q (centroidPoint (witness_n7 2) (witness_s7 2))) =
        -(zeta7 ^ 2)) ∧
    (exp (2 * Real.pi * I * dot3 witness_q (centroidPoint (witness_n7 3) (witness_s7 3))) =
        -(zeta7 ^ 6)) ∧
    (exp (2 * Real.pi * I * dot3 witness_q (centroidPoint (witness_n7 4) (witness_s7 4))) =
        -(zeta7 ^ 1)) ∧
    (exp (2 * Real.pi * I * dot3 witness_q (centroidPoint (witness_n7 5) (witness_s7 5))) =
        -(zeta7 ^ 5)) ∧
    (exp (2 * Real.pi * I * dot3 witness_q (centroidPoint (witness_n7 6) (witness_s7 6))) =
        -(zeta7 ^ 3)) := by
  have ht := signedWeight_witness
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show witness_q = qReal witness_qZ from rfl, exp_centroid_int_q,
      ht.1, exp_neg_pi_t_eq_neg_zeta 7 0 0 (by norm_num)]
  · rw [show witness_q = qReal witness_qZ from rfl, exp_centroid_int_q,
      ht.2.1, exp_neg_pi_t_eq_neg_zeta (-1) 4 0 (by norm_num)]
  · rw [show witness_q = qReal witness_qZ from rfl, exp_centroid_int_q,
      ht.2.2.1, exp_neg_pi_t_eq_neg_zeta 3 2 0 (by norm_num)]
  · rw [show witness_q = qReal witness_qZ from rfl, exp_centroid_int_q,
      ht.2.2.2.1, exp_neg_pi_t_eq_neg_zeta (-5) 6 0 (by norm_num)]
  · rw [show witness_q = qReal witness_qZ from rfl, exp_centroid_int_q,
      ht.2.2.2.2.1, exp_neg_pi_t_eq_neg_zeta 5 1 0 (by norm_num)]
  · rw [show witness_q = qReal witness_qZ from rfl, exp_centroid_int_q,
      ht.2.2.2.2.2.1, exp_neg_pi_t_eq_neg_zeta (-3) 5 0 (by norm_num)]
  · rw [show witness_q = qReal witness_qZ from rfl, exp_centroid_int_q,
      ht.2.2.2.2.2.2, exp_neg_pi_t_eq_neg_zeta 1 3 0 (by norm_num)]

lemma sum_neg_zeta7_eq_zero :
    -(zeta7 ^ 0) + -(zeta7 ^ 4) + -(zeta7 ^ 2) + -(zeta7 ^ 6) +
      -(zeta7 ^ 1) + -(zeta7 ^ 5) + -(zeta7 ^ 3) = 0 := by
  have hgeom : (∑ i ∈ range 7, zeta7 ^ i) = 0 :=
    IsPrimitiveRoot.geom_sum_eq_zero isPrimitiveRoot_zeta7 (by decide)
  have hlist : (∑ i ∈ range 7, zeta7 ^ i) =
      zeta7 ^ 0 + zeta7 ^ 1 + zeta7 ^ 2 + zeta7 ^ 3 +
        zeta7 ^ 4 + zeta7 ^ 5 + zeta7 ^ 6 := by
    rw [sum_range_succ, sum_range_succ, sum_range_succ, sum_range_succ,
      sum_range_succ, sum_range_succ, sum_range_succ, sum_range_zero]
    abel
  have hneg :
      -(zeta7 ^ 0) + -(zeta7 ^ 4) + -(zeta7 ^ 2) + -(zeta7 ^ 6) +
        -(zeta7 ^ 1) + -(zeta7 ^ 5) + -(zeta7 ^ 3) =
      - (zeta7 ^ 0 + zeta7 ^ 1 + zeta7 ^ 2 + zeta7 ^ 3 +
          zeta7 ^ 4 + zeta7 ^ 5 + zeta7 ^ 6) := by abel
  rw [hneg, ← hlist, hgeom, neg_zero]

lemma witness_exp_sum_eq_zero :
    (∑ k : Fin 7,
        exp (2 * Real.pi * I *
          dot3 witness_q (centroidPoint (witness_n7 k) (witness_s7 k)))) = 0 := by
  have h := witness_exp_eq_neg_zeta
  set f : Fin 7 → ℂ := fun k =>
    exp (2 * Real.pi * I * dot3 witness_q (centroidPoint (witness_n7 k) (witness_s7 k)))
  have hexp : ∑ k : Fin 7, f k = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 := by
    simp [Fin.sum_univ_succ, f]
    abel
  have hsum : ∑ k : Fin 7, f k =
      -(zeta7 ^ 0) + -(zeta7 ^ 4) + -(zeta7 ^ 2) + -(zeta7 ^ 6) +
        -(zeta7 ^ 1) + -(zeta7 ^ 5) + -(zeta7 ^ 3) := by
    rw [hexp, show f 0 = -(zeta7 ^ 0) from h.1, show f 1 = -(zeta7 ^ 4) from h.2.1,
      show f 2 = -(zeta7 ^ 2) from h.2.2.1, show f 3 = -(zeta7 ^ 6) from h.2.2.2.1,
      show f 4 = -(zeta7 ^ 1) from h.2.2.2.2.1, show f 5 = -(zeta7 ^ 5) from h.2.2.2.2.2.1,
      show f 6 = -(zeta7 ^ 3) from h.2.2.2.2.2.2]
  simpa [f] using (hsum.trans sum_neg_zeta7_eq_zero)

theorem witness_structureFactor_eq_zero :
    structureFactor (fun k : Fin 7 => centroidPoint (witness_n7 k) (witness_s7 k))
      witness_q = 0 := by
  unfold structureFactor
  rw [witness_exp_sum_eq_zero, mul_zero]

theorem witness_normSq_eq_zero :
    ‖structureFactor (fun k : Fin 7 => centroidPoint (witness_n7 k) (witness_s7 k))
      witness_q‖ ^ 2 = 0 := by
  rw [witness_structureFactor_eq_zero, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]

lemma cos_pi_div_seven_sq_pos : 0 < Real.cos (Real.pi / 7) ^ 2 := by
  have hpos : 0 < Real.cos (Real.pi / 7) := by
    have hlt : Real.pi / 7 < Real.pi / 2 := by
      apply (div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 7) (by norm_num : (0 : ℝ) < 2)).mpr
      linarith [Real.pi_pos]
    have hgt : 0 < Real.pi / 7 := div_pos Real.pi_pos (by norm_num)
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [hgt], hlt⟩
  exact sq_pos_of_pos hpos

/-- [F, Lean] No D3-style positive lower bound on all of `ℤ³` under the D-form:
at `q = (1,2,4)` there exist D-form points with `|F|² = 0`. -/
theorem no_D3_lower_bound_on_all_int_q :
    ∃ (N : ℕ) (_hN : 1 ≤ N) (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
      (_hs : ∀ k j, s k j = 1 ∨ s k j = -1) (q : Fin 3 → ℤ),
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) (qReal q)‖ ^ 2 = 0 ∧
        ‖structureFactor (fun k => centroidPoint (n k) (s k)) (qReal q)‖ ^ 2 <
          Real.cos (Real.pi / 7) ^ 2 := by
  refine ⟨7, by norm_num, witness_n7, witness_s7, witness_s7_is_sign, witness_qZ, ?_⟩
  have hz : ‖structureFactor (fun k : Fin 7 => centroidPoint (witness_n7 k) (witness_s7 k))
      (qReal witness_qZ)‖ ^ 2 = 0 := by
    simpa [witness_q] using witness_normSq_eq_zero
  exact ⟨hz, by rw [hz]; exact cos_pi_div_seven_sq_pos⟩

/-- Average version: the same vanishing box in every slot of an M-box family. -/
theorem no_D3_lower_bound_on_all_int_q_avg {M : ℕ} (_hM : 1 ≤ M) :
    ∃ (N : Fin M → ℕ) (_hN : ∀ B, 1 ≤ N B)
      (n : (B : Fin M) → Fin (N B) → Fin 3 → ℤ)
      (s : (B : Fin M) → Fin (N B) → Fin 3 → ℤ)
      (_hs : ∀ B k j, s B k j = 1 ∨ s B k j = -1) (q : Fin 3 → ℤ),
      (M : ℝ)⁻¹ * ∑ B : Fin M,
          ‖structureFactor (fun k => centroidPoint (n B k) (s B k)) (qReal q)‖ ^ 2 = 0 := by
  let N : Fin M → ℕ := fun _ => 7
  let n : (B : Fin M) → Fin (N B) → Fin 3 → ℤ := fun _ => witness_n7
  let s : (B : Fin M) → Fin (N B) → Fin 3 → ℤ := fun _ => witness_s7
  refine ⟨N, fun _ => by norm_num, n, s, fun _ => witness_s7_is_sign, witness_qZ, ?_⟩
  have hterm : ∀ B,
      ‖structureFactor (fun k => centroidPoint (n B k) (s B k)) (qReal witness_qZ)‖ ^ 2 = 0 := by
    intro B
    simpa [n, s, witness_q] using witness_normSq_eq_zero
  simp [hterm]

#print axioms qL1_eq_sum_abs
#print axioms abs_signedWeight_le_qL1
#print axioms exp_centroid_int_q
#print axioms re_exp_centroid_int_q
#print axioms cos_signedWeight_ge
#print axioms cos_L_pi_div_seven_nonneg
#print axioms re_structureFactor_int_q_ge
#print axioms cos_sq_le_normSq_structureFactor_int_q_le_one
#print axioms lemma_D_intVec_avg
#print axioms lemma_D_intVec_lo_int
#print axioms signedWeight_witness
#print axioms neg_zeta7_pow
#print axioms exp_neg_pi_t_eq_neg_zeta
#print axioms witness_exp_eq_neg_zeta
#print axioms witness_exp_sum_eq_zero
#print axioms witness_structureFactor_eq_zero
#print axioms witness_normSq_eq_zero
#print axioms no_D3_lower_bound_on_all_int_q
#print axioms no_D3_lower_bound_on_all_int_q_avg

end LeanLab.Scratch.LemmaDIntVec
