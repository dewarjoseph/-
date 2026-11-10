import LeanLab.Scratch.LemmaDLowerBound220
import LeanLab.Scratch.LemmaDL1Six
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Explicit polynomial lower bound at q = (3,3,0)
(public-screen)

Public-screen v2 copy of LeanLab.Scratch.LemmaDLowerBound330 (official pin src
`a919b91a65bd14b0060bf0f514f523ab96252245f09fa0bc7aee87fe426f69bc`).
Header redacted; theorem bodies are unchanged. This copy is not a
replacement pin.

**[P, Lean]** There is an explicit constant `c0 = 1/65 > 0` such that for
every nonempty finite equal-weight D-form box at `q = (3,3,0)`,
`‖F‖ ≥ c0 / N³` and therefore `|F|² ≥ c0² / N⁶`.

The exponent 3 is what this argument gives, not claimed sharp. The
infimum over all boxes at this `q` is not claimed here (stays `[X]`).

**Argument.** Counts `a,b,b'` of `t ∈ {0,6,−6}` (the two mixed-sign
patterns both give `t = 0`). With `θ = 6π/7`,
`N·F = (a+(b+b')c') + i(b'−b)s'` where `c' = cos θ = −cos(π/7)` and
`s' = sin θ = sin(π/7)`.

* If `b ≠ b'`, `|Im(N F)| ≥ sin θ ≥ 2/5`, so `‖F‖ ≥ (2/5)/N ≥ c0/N³`.
* If `b = b'` then `|N F| = |p + q c'|` with `p = a`, `q = 2b`.
  If `q = 0` then `|N F| = N ≥ 1`. The cosine `c'` is a root of the
  same cubic `g(x) = 8x³+4x²−4x−1` as in LemmaDLowerBound220
  (here from `ζ₇³+ζ₇⁴ = 2c'`). No rational root (reused). For
  integers `p,q` with `q ≠ 0`, `|p+q c'| ≥ 1/(|q|² |h|)`. When
  `|p+q c'| < 1` one has `|c'| < 91/100` and `|h| < 65`, so
  `|N F| ≥ 1/(65 N²)` and `‖F‖ ≥ c0/N³`.

The constant `H = 65` is recomputed for `c' = cos(6π/7)` (which is
near `−1`, unlike `cos(4π/7)`); the `H = 30` from the `(2,2,0)` file
does not apply.

**Not proved / out of scope:**
* Sharpness of the exponent 3, or any other `q`. Infimum at `(3,3,0)`
  stays `[X]` in this file.
* D-form class only. Scratch; not a Lake target; not peer reviewed.

This file is source-only and is not a Lake package. It claims nothing
beyond the theorems stated below.

Dated 2026-11-10.
-/

namespace LeanLab.Scratch.LemmaDLowerBound330

open Complex Finset
open LeanLab.Scratch.LemmaD4 (dot3 structureFactor centroidPoint exp_two_pi_I_int)
open LeanLab.Scratch.LemmaDIntVec
  (qReal signedWeight zeta7 zeta7_pow isPrimitiveRoot_zeta7 exp_centroid_int_q)
open LeanLab.Scratch.LemmaDL1Six
  (qZ330 q330 signedWeight_qZ330_mem)
open LeanLab.Scratch.LemmaDLowerBound220
  (gR hR gZ gQ gR_sub gZ_eq_q_pow gQ_ne_zero gZ_ne_zero abs_one_le_int
    zeta7_pow_seven zeta7_pow_add_seven sum_zeta7_explicit)

noncomputable def cθ' : ℝ := Real.cos (6 * Real.pi / 7)
noncomputable def sθ' : ℝ := Real.sin (6 * Real.pi / 7)

noncomputable def c0 : ℝ := 1 / 65

lemma c0_pos : 0 < c0 := by
  unfold c0
  norm_num

/-! ## Trigonometric bounds for θ = 6π/7 -/

lemma cθ'_eq_neg_cos_pi_div_seven : cθ' = -Real.cos (Real.pi / 7) := by
  unfold cθ'
  have : 6 * Real.pi / 7 = Real.pi - Real.pi / 7 := by ring
  rw [this, Real.cos_pi_sub]

lemma sθ'_eq_sin_pi_div_seven : sθ' = Real.sin (Real.pi / 7) := by
  unfold sθ'
  have : 6 * Real.pi / 7 = Real.pi - Real.pi / 7 := by ring
  rw [this, Real.sin_pi_sub]

lemma cos_pi_div_seven_pos : 0 < Real.cos (Real.pi / 7) := by
  refine Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩
  · linarith [Real.pi_pos]
  · have hmul : ((1 : ℝ) / 7) * Real.pi < ((1 : ℝ) / 2) * Real.pi :=
      mul_lt_mul_of_pos_right (by norm_num) Real.pi_pos
    convert hmul using 1 <;> ring

lemma cos_pi_div_seven_gt_cos_pi_div_six :
    Real.cos (Real.pi / 6) < Real.cos (Real.pi / 7) := by
  have hlt : Real.pi / 7 < Real.pi / 6 := by
    have hmul : ((1 : ℝ) / 7) * Real.pi < ((1 : ℝ) / 6) * Real.pi :=
      mul_lt_mul_of_pos_right (by norm_num) Real.pi_pos
    convert hmul using 1 <;> ring
  have hlo : 0 ≤ Real.pi / 7 := by positivity
  exact Real.cos_lt_cos_of_nonneg_of_le_pi hlo (by linarith [Real.pi_pos]) hlt

def pCos (x : ℝ) : ℝ := 8 * x ^ 3 - 4 * x ^ 2 - 4 * x + 1

lemma pCos_deriv_pos_of_ge_seven_tenths {x : ℝ} (hx : (7 / 10 : ℝ) ≤ x) :
    0 < 24 * x ^ 2 - 8 * x - 4 := by
  have hx2 : (49 / 100 : ℝ) ≤ x ^ 2 := by
    have hmul := mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 7 / 10) hx
    have hL : (7 / 10 : ℝ) * (7 / 10) = 49 / 100 := by norm_num
    have hR : x * x = x ^ 2 := by ring
    rwa [hL, hR] at hmul
  nlinarith

lemma pCos_eval_ninety_one_hundredths : (0 : ℝ) < pCos (91 / 100) := by
  unfold pCos
  norm_num

lemma zeta7_pow_three_add_four :
    zeta7 ^ 3 + zeta7 ^ 4 = 2 * (cθ' : ℂ) := by
  rw [zeta7_pow, zeta7_pow]
  have h3 : (2 * Real.pi * I * (3 : ℕ) / 7 : ℂ) =
      (↑(6 * Real.pi / 7) : ℂ) * I := by
    push_cast; ring
  have h4 : (2 * Real.pi * I * (4 : ℕ) / 7 : ℂ) =
      (↑(-(6 * Real.pi / 7)) : ℂ) * I + 2 * Real.pi * I := by
    push_cast; ring
  rw [h3, h4, exp_add]
  have h2π : exp (2 * Real.pi * I) = 1 := by
    have h := exp_two_pi_I_int (1 : ℤ)
    have heq : (2 * Real.pi * I : ℂ) = 2 * Real.pi * I * ((1 : ℤ) : ℝ) := by
      push_cast; ring
    rw [heq, h]
  rw [h2π, mul_one]
  rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
  rw [Real.cos_neg, Real.sin_neg]
  unfold cθ'
  push_cast
  ring

lemma eta'_cubic_zero :
    (zeta7 ^ 3 + zeta7 ^ 4) ^ 3 + (zeta7 ^ 3 + zeta7 ^ 4) ^ 2
      - 2 * (zeta7 ^ 3 + zeta7 ^ 4) - 1 = 0 := by
  set z := zeta7
  have hz7 : z ^ 7 = 1 := zeta7_pow_seven
  have h8 : z ^ 8 = z := by
    rw [show (8 : ℕ) = 1 + 7 from by decide, zeta7_pow_add_seven, pow_one]
  have h9 : z ^ 9 = z ^ 2 := by
    rw [show (9 : ℕ) = 2 + 7 from by decide, zeta7_pow_add_seven]
  have h10 : z ^ 10 = z ^ 3 := by
    rw [show (10 : ℕ) = 3 + 7 from by decide, zeta7_pow_add_seven]
  have hp36 : z ^ 3 * z ^ 6 = z ^ 9 := by rw [← pow_add]
  have hp33 : z ^ 3 * z = z ^ 4 := pow_succ z 3
  have hp46 : z ^ 4 * z ^ 6 = z ^ 10 := by rw [← pow_add]
  have hp41 : z ^ 4 * z = z ^ 5 := pow_succ z 4
  have hη2 : (z ^ 3 + z ^ 4) ^ 2 = z ^ 6 + 2 + z := by
    have hexp :
        (z ^ 3 + z ^ 4) ^ 2 =
          z ^ 3 * z ^ 3 + z ^ 3 * z ^ 4 + z ^ 4 * z ^ 3 + z ^ 4 * z ^ 4 := by ring
    have p33 : z ^ 3 * z ^ 3 = z ^ 6 := by rw [← pow_add]
    have p34 : z ^ 3 * z ^ 4 = z ^ 7 := by rw [← pow_add]
    have p43 : z ^ 4 * z ^ 3 = z ^ 7 := by rw [← pow_add]
    have p44 : z ^ 4 * z ^ 4 = z ^ 8 := by rw [← pow_add]
    rw [hexp, p33, p34, p43, p44, hz7, h8]
    ring
  have hη3 : (z ^ 3 + z ^ 4) ^ 3 = z ^ 2 + 3 * z ^ 3 + 3 * z ^ 4 + z ^ 5 := by
    have hmul : (z ^ 3 + z ^ 4) ^ 3 = (z ^ 3 + z ^ 4) * (z ^ 3 + z ^ 4) ^ 2 := by
      ring
    rw [hmul, hη2]
    have hexp :
        (z ^ 3 + z ^ 4) * (z ^ 6 + 2 + z) =
          z ^ 3 * z ^ 6 + z ^ 3 * 2 + z ^ 3 * z +
            z ^ 4 * z ^ 6 + z ^ 4 * 2 + z ^ 4 * z := by ring
    rw [hexp, hp36, hp46]
    have hp3z : z ^ 3 * z = z ^ 4 := pow_succ z 3
    have hp4z : z ^ 4 * z = z ^ 5 := pow_succ z 4
    rw [hp3z, hp4z, h9, h10]
    ring
  rw [hη3, hη2]
  have hsum := sum_zeta7_explicit
  convert hsum using 1
  ring

lemma gR_cθ'_eq_zero : gR cθ' = 0 := by
  have hη := eta'_cubic_zero
  rw [zeta7_pow_three_add_four] at hη
  have hC : ((gR cθ' : ℝ) : ℂ) = 0 := by
    unfold gR
    convert hη using 1
    push_cast
    ring
  exact_mod_cast (ofReal_eq_zero.mp hC)

lemma pCos_eq_neg_gR (x : ℝ) : pCos x = -gR (-x) := by
  unfold pCos gR
  ring

lemma pCos_cos_pi_div_seven : pCos (Real.cos (Real.pi / 7)) = 0 := by
  rw [pCos_eq_neg_gR, ← cθ'_eq_neg_cos_pi_div_seven, gR_cθ'_eq_zero, neg_zero]

lemma abs_cθ'_lt_ninety_one_hundredths' : |cθ'| < 91 / 100 := by
  rw [cθ'_eq_neg_cos_pi_div_seven, abs_neg, abs_of_pos cos_pi_div_seven_pos]
  set u := Real.cos (Real.pi / 7)
  have hu0 : pCos u = 0 := pCos_cos_pi_div_seven
  have hge : (7 / 10 : ℝ) ≤ u := by
    have hcos6 : Real.cos (Real.pi / 6) = Real.sqrt 3 / 2 := Real.cos_pi_div_six
    have hsqrt : (7 / 10 : ℝ) ≤ Real.sqrt 3 / 2 := by
      have hsq : (7 / 5 : ℝ) ≤ Real.sqrt 3 :=
        (Real.le_sqrt (by norm_num) (by positivity)).mpr (by norm_num)
      linarith
    have hcu : Real.sqrt 3 / 2 < u := by
      rw [← hcos6]
      exact cos_pi_div_seven_gt_cos_pi_div_six
    exact le_trans hsqrt (le_of_lt hcu)
  have hmono : ∀ {x y : ℝ}, (7 / 10 : ℝ) ≤ x → x ≤ y → pCos x ≤ pCos y := by
    intro x y hx hxy
    have hdiff : pCos y - pCos x =
        (y - x) * (8 * (y ^ 2 + y * x + x ^ 2) - 4 * (y + x) - 4) := by
      unfold pCos; ring
    have hq : 0 ≤ 8 * (y ^ 2 + y * x + x ^ 2) - 4 * (y + x) - 4 := by
      have hx2 : (49 / 100 : ℝ) ≤ x ^ 2 := by
        have hmul := mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 7 / 10) hx
        have hL : (7 / 10 : ℝ) * (7 / 10) = 49 / 100 := by norm_num
        have hR : x * x = x ^ 2 := by ring
        rwa [hL, hR] at hmul
      have hy : (7 / 10 : ℝ) ≤ y := le_trans hx hxy
      have hy2 : (49 / 100 : ℝ) ≤ y ^ 2 := by
        have hmul := mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 7 / 10) hy
        have hL : (7 / 10 : ℝ) * (7 / 10) = 49 / 100 := by norm_num
        have hR : y * y = y ^ 2 := by ring
        rwa [hL, hR] at hmul
      have hxyterm : (49 / 100 : ℝ) ≤ y * x := by
        have hmul : (7 / 10 : ℝ) * (7 / 10) ≤ y * x :=
          mul_le_mul hy hx (by norm_num) (by linarith)
        have hL : (7 / 10 : ℝ) * (7 / 10) = 49 / 100 := by norm_num
        rwa [hL] at hmul
      nlinarith
    rw [← sub_nonneg, hdiff]
    exact mul_nonneg (sub_nonneg.mpr hxy) hq
  have h91 : (7 / 10 : ℝ) ≤ 91 / 100 := by norm_num
  by_contra h
  have : (91 / 100 : ℝ) ≤ u := le_of_not_gt h
  have : pCos (91 / 100) ≤ pCos u := hmono h91 this
  rw [hu0] at this
  linarith [pCos_eval_ninety_one_hundredths]

lemma sθ'_ge_two_div_five : (2 / 5 : ℝ) ≤ sθ' := by
  rw [sθ'_eq_sin_pi_div_seven]
  have hsinpos : 0 < Real.sin (Real.pi / 7) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity)
      (by linarith [Real.pi_pos])
  have habs : |cθ'| = Real.cos (Real.pi / 7) := by
    rw [cθ'_eq_neg_cos_pi_div_seven, abs_neg, abs_of_pos cos_pi_div_seven_pos]
  have hsq : Real.sin (Real.pi / 7) ^ 2 = 1 - Real.cos (Real.pi / 7) ^ 2 := by
    rw [← Real.sin_sq_add_cos_sq (Real.pi / 7)]; ring
  have hc2 : Real.cos (Real.pi / 7) ^ 2 < (91 / 100 : ℝ) ^ 2 := by
    have hc := abs_cθ'_lt_ninety_one_hundredths'
    rw [habs] at hc
    have hmul := mul_self_lt_mul_self (le_of_lt cos_pi_div_seven_pos) hc
    have hL : Real.cos (Real.pi / 7) * Real.cos (Real.pi / 7) =
        Real.cos (Real.pi / 7) ^ 2 := by ring
    have hR : (91 / 100 : ℝ) * (91 / 100) = (91 / 100) ^ 2 := by ring
    rwa [hL, hR] at hmul
  have : (2 / 5 : ℝ) ^ 2 ≤ Real.sin (Real.pi / 7) ^ 2 := by
    have : 1 - (91 / 100 : ℝ) ^ 2 = 1719 / 10000 := by norm_num
    have : (2 / 5 : ℝ) ^ 2 = 4 / 25 := by norm_num
    have : 4 / 25 ≤ 1719 / 10000 := by norm_num
    have h1 : 1 - Real.cos (Real.pi / 7) ^ 2 > 1 - (91 / 100 : ℝ) ^ 2 := by
      linarith
    rw [← hsq] at h1
    linarith
  exact (sq_le_sq₀ (by norm_num) (le_of_lt hsinpos)).mp this

/-! ## |h| bound when |x − c'| < 1 -/

lemma abs_hR_lt_sixtyfive (x : ℝ) (hx : |x - cθ'| < 1) :
    |hR x cθ'| < 65 := by
  have hc := abs_cθ'_lt_ninety_one_hundredths'
  have hxab : |x| < 191 / 100 := by
    have : |x| = |(x - cθ') + cθ'| := by ring_nf
    rw [this]
    exact lt_of_le_of_lt (abs_add_le _ _) (by linarith)
  have hx2 : x ^ 2 < (191 / 100 : ℝ) ^ 2 := by
    have hmul := mul_self_lt_mul_self (abs_nonneg x) hxab
    have habs : |x| * |x| = x ^ 2 := by rw [← sq_abs, sq]
    have hR : (191 / 100 : ℝ) * (191 / 100) = (191 / 100) ^ 2 := by ring
    rwa [habs, hR] at hmul
  have hxc : |x * cθ'| < (191 / 100 : ℝ) * (91 / 100) := by
    rw [abs_mul]
    exact mul_lt_mul'' hxab hc (abs_nonneg _) (abs_nonneg _)
  have hc2 : cθ' ^ 2 < (91 / 100 : ℝ) ^ 2 := by
    have hmul := mul_self_lt_mul_self (abs_nonneg cθ') hc
    have habs : |cθ'| * |cθ'| = cθ' ^ 2 := by rw [← sq_abs, sq]
    have hR : (91 / 100 : ℝ) * (91 / 100) = (91 / 100) ^ 2 := by ring
    rwa [habs, hR] at hmul
  have htri :
      |hR x cθ'| ≤
        8 * (x ^ 2 + |x * cθ'| + cθ' ^ 2) + 4 * (|x| + |cθ'|) + 4 := by
    unfold hR
    have hA :
        |8 * (x ^ 2 + x * cθ' + cθ' ^ 2) + 4 * (x + cθ') + (-4)| ≤
          |8 * (x ^ 2 + x * cθ' + cθ' ^ 2)| + |4 * (x + cθ')| + |(-4 : ℝ)| := by
      set A := 8 * (x ^ 2 + x * cθ' + cθ' ^ 2)
      set B := 4 * (x + cθ')
      set C := (-4 : ℝ)
      have h1 := abs_add_le (A + B) C
      have h2 := abs_add_le A B
      linarith
    have h8 :
        |8 * (x ^ 2 + x * cθ' + cθ' ^ 2)| = 8 * |x ^ 2 + x * cθ' + cθ' ^ 2| := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 8)]
    have h4 : |4 * (x + cθ')| = 4 * |x + cθ'| := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    have h4c : |(-4 : ℝ)| = 4 := by norm_num
    have hx2nn : |x ^ 2| = x ^ 2 := abs_of_nonneg (sq_nonneg x)
    have hc2nn : |cθ' ^ 2| = cθ' ^ 2 := abs_of_nonneg (sq_nonneg cθ')
    have hquad :
        |x ^ 2 + x * cθ' + cθ' ^ 2| ≤ x ^ 2 + |x * cθ'| + cθ' ^ 2 := by
      have h1 := abs_add_le (x ^ 2 + x * cθ') (cθ' ^ 2)
      have h2 := abs_add_le (x ^ 2) (x * cθ')
      linarith [hx2nn, hc2nn]
    have hsum : |x + cθ'| ≤ |x| + |cθ'| := abs_add_le _ _
    have hid :
        8 * (x ^ 2 + x * cθ' + cθ' ^ 2) + 4 * (x + cθ') - 4 =
          8 * (x ^ 2 + x * cθ' + cθ' ^ 2) + 4 * (x + cθ') + (-4) := by ring
    rw [hid]
    linarith [hA, h8, h4, h4c, hquad, hsum]
  have hnum :
      8 * (x ^ 2 + |x * cθ'| + cθ' ^ 2) + 4 * (|x| + |cθ'|) + 4 < 65 := by
    have : 8 * ((191 / 100 : ℝ) ^ 2 + (191 / 100) * (91 / 100) +
        (91 / 100) ^ 2) + 4 * (191 / 100 + 91 / 100) + 4 = 649944 / 10000 := by
      norm_num
    have hbound :
        8 * ((191 / 100 : ℝ) ^ 2 + (191 / 100) * (91 / 100) +
          (91 / 100) ^ 2) + 4 * (191 / 100 + 91 / 100) + 4 < 65 := by
      norm_num
    nlinarith [hx2, hxc, hc2, hxab, hc, hbound]
  exact lt_of_le_of_lt htri hnum

lemma abs_linform_ge_of_small (p q : ℤ) (hq : q ≠ 0)
    (hsmall : |((p : ℝ) + (q : ℝ) * cθ')| < 1) :
    1 / (65 * (q : ℝ) ^ 2) ≤ |((p : ℝ) + (q : ℝ) * cθ')| := by
  have hqR : (q : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hq
  set x0 : ℝ := -((p : ℝ) / q)
  have hdiff : x0 - cθ' = -((p : ℝ) + (q : ℝ) * cθ') / q := by
    unfold x0
    field_simp [hqR]
    ring
  have hdiffabs : |x0 - cθ'| = |((p : ℝ) + (q : ℝ) * cθ')| / |(q : ℝ)| := by
    rw [hdiff, abs_div, abs_neg]
  have hqabs : (1 : ℝ) ≤ |(q : ℝ)| := abs_one_le_int hq
  have hxlt : |x0 - cθ'| < 1 := by
    rw [hdiffabs]
    exact (div_lt_one (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hqabs)).2
      (lt_of_lt_of_le hsmall hqabs)
  have hfact : gR x0 = (x0 - cθ') * hR x0 cθ' := by
    have : gR x0 = gR x0 - gR cθ' := by rw [gR_cθ'_eq_zero, sub_zero]
    rw [this, gR_sub]
  have hgZ : (gZ p q : ℝ) = (q : ℝ) ^ 3 * gR x0 := by
    rw [gZ_eq_q_pow p q hq]
    congr 2
    unfold x0
    field_simp [hqR]
  have hgz0 : gZ p q ≠ 0 := gZ_ne_zero p q hq
  have habsZ : (1 : ℝ) ≤ |(gZ p q : ℝ)| := abs_one_le_int hgz0
  have hh : |hR x0 cθ'| < 65 := abs_hR_lt_sixtyfive x0 hxlt
  have hh0 : hR x0 cθ' ≠ 0 := by
    intro hz
    have hg0 : gR x0 = 0 := by rw [hfact, hz, mul_zero]
    have hxQ : (gQ ((-p : ℚ) / q) : ℝ) = gR x0 := by
      unfold gQ gR x0; push_cast; field_simp [hqR]
    have : gQ ((-p : ℚ) / q) = 0 := by
      have hcast : ((gQ ((-p : ℚ) / q) : ℚ) : ℝ) = 0 := by
        rw [hxQ, hg0]
      exact_mod_cast hcast
    exact gQ_ne_zero _ this
  have hprod : |gR x0| = |x0 - cθ'| * |hR x0 cθ'| := by
    rw [hfact, abs_mul]
  have hgRabs : |(q : ℝ) ^ 3| * |gR x0| = |(gZ p q : ℝ)| := by
    have habs := congrArg abs hgZ
    rw [abs_mul] at habs
    exact habs.symm
  have hq3 : |(q : ℝ) ^ 3| = |(q : ℝ)| ^ 3 := abs_pow _ _
  have hfinal :
      |((p : ℝ) + (q : ℝ) * cθ')| =
        |(gZ p q : ℝ)| / (|(q : ℝ)| ^ 2 * |hR x0 cθ'|) := by
    have hxeq : |((p : ℝ) + (q : ℝ) * cθ')| = |(q : ℝ)| * |x0 - cθ'| := by
      have hne : |(q : ℝ)| ≠ 0 := abs_ne_zero.mpr hqR
      rw [hdiffabs, mul_div_cancel₀ _ hne]
    have hge : |x0 - cθ'| = |gR x0| / |hR x0 cθ'| := by
      have hne : |hR x0 cθ'| ≠ 0 := abs_ne_zero.mpr hh0
      rw [hprod]
      field_simp [hne]
    have hgR' : |gR x0| = |(gZ p q : ℝ)| / |(q : ℝ) ^ 3| := by
      have hne : |(q : ℝ) ^ 3| ≠ 0 := by simp [hqR]
      exact eq_div_of_mul_eq hne (by rw [mul_comm]; exact hgRabs)
    rw [hxeq, hge, hgR', hq3]
    have hne1 : |hR x0 cθ'| ≠ 0 := abs_ne_zero.mpr hh0
    have hne2 : |(q : ℝ)| ≠ 0 := abs_ne_zero.mpr hqR
    field_simp [hne1, hne2]
  rw [hfinal]
  have hdenpos : 0 < |(q : ℝ)| ^ 2 * |hR x0 cθ'| := by
    have : 0 < |hR x0 cθ'| := abs_pos.mpr hh0
    positivity
  have hcmp : |(q : ℝ)| ^ 2 * |hR x0 cθ'| ≤ 65 * (q : ℝ) ^ 2 := by
    have hsq : (q : ℝ) ^ 2 = |(q : ℝ)| ^ 2 := (sq_abs (q : ℝ)).symm
    rw [hsq]
    nlinarith [le_of_lt hh, sq_nonneg |(q : ℝ)|]
  have hnumpos : 0 < 65 * (q : ℝ) ^ 2 := by
    have : (q : ℝ) ≠ 0 := hqR
    positivity
  refine (div_le_div_iff₀ hnumpos hdenpos).mpr ?_
  nlinarith [habsZ, hcmp, sq_nonneg |(q : ℝ)|]

/-! ## Counts and the phase sum at q = (3,3,0) -/

noncomputable def countT {N : ℕ} (s : Fin N → Fin 3 → ℤ) (t : ℤ) : ℕ :=
  #{k : Fin N | signedWeight qZ330 (s k) = t}

lemma countT_add_eq_card {N : ℕ} (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    countT s 0 + countT s 6 + countT s (-6) = N := by
  classical
  set S0 : Finset (Fin N) := {k | signedWeight qZ330 (s k) = 0}
  set S6 : Finset (Fin N) := {k | signedWeight qZ330 (s k) = 6}
  set Sm : Finset (Fin N) := {k | signedWeight qZ330 (s k) = -6}
  have hdisj01 : Disjoint S0 S6 := by
    refine disjoint_left.mpr ?_
    intro x hx0 hx6
    simp only [S0, S6, mem_filter, mem_univ, true_and] at hx0 hx6
    exact absurd hx6 (by omega)
  have hdisj02 : Disjoint S0 Sm := by
    refine disjoint_left.mpr ?_
    intro x hx0 hxm
    simp only [S0, Sm, mem_filter, mem_univ, true_and] at hx0 hxm
    exact absurd hxm (by omega)
  have hdisj12 : Disjoint S6 Sm := by
    refine disjoint_left.mpr ?_
    intro x hx6 hxm
    simp only [S6, Sm, mem_filter, mem_univ, true_and] at hx6 hxm
    exact absurd hxm (by omega)
  have hcover : S0 ∪ S6 ∪ Sm = univ := by
    ext k
    constructor
    · intro; exact mem_univ _
    · intro _
      simp only [S0, S6, Sm, mem_union, mem_filter, mem_univ, true_and]
      rcases signedWeight_qZ330_mem (s k) (hs k) with h | h | h <;> simp [h]
  have hcard : (S0 ∪ S6 ∪ Sm).card = N := by
    rw [hcover, card_univ, Fintype.card_fin]
  have hdisj_left : Disjoint (S0 ∪ S6) Sm :=
    Disjoint.sup_left hdisj02 hdisj12
  rw [card_union_of_disjoint hdisj_left, card_union_of_disjoint hdisj01] at hcard
  simpa [countT, S0, S6, Sm] using hcard

lemma exp_centroid_at_t0 (n s : Fin 3 → ℤ)
    (ht : signedWeight qZ330 s = 0) :
    exp (2 * Real.pi * I * dot3 q330 (centroidPoint n s)) = 1 := by
  rw [q330, exp_centroid_int_q, ht]
  simp [exp_zero]

lemma exp_centroid_at_t6 (n s : Fin 3 → ℤ)
    (ht : signedWeight qZ330 s = 6) :
    exp (2 * Real.pi * I * dot3 q330 (centroidPoint n s)) =
      (cθ' : ℂ) - I * sθ' := by
  rw [q330, exp_centroid_int_q, ht]
  have hθ : (-(Real.pi * ((6 : ℤ) : ℝ) / 7) : ℝ) = -(Real.pi * (6 : ℝ) / 7) := by
    norm_cast
  rw [hθ, Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
  unfold cθ' sθ'
  push_cast
  ring_nf

lemma exp_centroid_at_tneg6 (n s : Fin 3 → ℤ)
    (ht : signedWeight qZ330 s = -6) :
    exp (2 * Real.pi * I * dot3 q330 (centroidPoint n s)) =
      (cθ' : ℂ) + I * sθ' := by
  rw [q330, exp_centroid_int_q, ht]
  have hθ : (-(Real.pi * ((-6 : ℤ) : ℝ) / 7) : ℝ) = 6 * Real.pi / 7 := by
    push_cast; ring
  rw [hθ, Complex.exp_ofReal_mul_I]
  unfold cθ' sθ'
  push_cast
  ring

lemma sum_exp_eq_counts {N : ℕ}
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (∑ k : Fin N,
        exp (2 * Real.pi * I * dot3 q330 (centroidPoint (n k) (s k)))) =
      (countT s 0 : ℂ) +
        (countT s 6 : ℂ) * ((cθ' : ℂ) - I * sθ') +
        (countT s (-6) : ℂ) * ((cθ' : ℂ) + I * sθ') := by
  classical
  set S0 : Finset (Fin N) := {k | signedWeight qZ330 (s k) = 0}
  set S6 : Finset (Fin N) := {k | signedWeight qZ330 (s k) = 6}
  set Sm : Finset (Fin N) := {k | signedWeight qZ330 (s k) = -6}
  have hdisj01 : Disjoint S0 S6 := by
    refine disjoint_left.mpr ?_
    intro x hx0 hx6
    simp only [S0, S6, mem_filter, mem_univ, true_and] at hx0 hx6
    exact absurd hx6 (by omega)
  have hdisj02 : Disjoint S0 Sm := by
    refine disjoint_left.mpr ?_
    intro x hx0 hxm
    simp only [S0, Sm, mem_filter, mem_univ, true_and] at hx0 hxm
    exact absurd hxm (by omega)
  have hdisj12 : Disjoint S6 Sm := by
    refine disjoint_left.mpr ?_
    intro x hx6 hxm
    simp only [S6, Sm, mem_filter, mem_univ, true_and] at hx6 hxm
    exact absurd hxm (by omega)
  have hcover : S0 ∪ S6 ∪ Sm = univ := by
    ext k
    constructor
    · intro; exact mem_univ _
    · intro _
      simp only [S0, S6, Sm, mem_union, mem_filter, mem_univ, true_and]
      rcases signedWeight_qZ330_mem (s k) (hs k) with h | h | h <;> simp [h]
  have hdisj_left : Disjoint (S0 ∪ S6) Sm :=
    Disjoint.sup_left hdisj02 hdisj12
  have hsum :
      (∑ k : Fin N,
          exp (2 * Real.pi * I * dot3 q330 (centroidPoint (n k) (s k)))) =
        (∑ k ∈ S0,
            exp (2 * Real.pi * I * dot3 q330 (centroidPoint (n k) (s k)))) +
          (∑ k ∈ S6,
              exp (2 * Real.pi * I * dot3 q330 (centroidPoint (n k) (s k)))) +
            (∑ k ∈ Sm,
                exp (2 * Real.pi * I * dot3 q330 (centroidPoint (n k) (s k)))) := by
    calc
      (∑ k : Fin N,
            exp (2 * Real.pi * I * dot3 q330 (centroidPoint (n k) (s k))))
          = ∑ k ∈ univ,
              exp (2 * Real.pi * I * dot3 q330 (centroidPoint (n k) (s k))) := rfl
      _ = ∑ k ∈ S0 ∪ S6 ∪ Sm,
              exp (2 * Real.pi * I * dot3 q330 (centroidPoint (n k) (s k))) := by
                rw [hcover]
      _ = ∑ k ∈ S0 ∪ S6,
              exp (2 * Real.pi * I * dot3 q330 (centroidPoint (n k) (s k))) +
            ∑ k ∈ Sm,
              exp (2 * Real.pi * I * dot3 q330 (centroidPoint (n k) (s k))) :=
            sum_union hdisj_left
      _ = (∑ k ∈ S0,
              exp (2 * Real.pi * I * dot3 q330 (centroidPoint (n k) (s k))) +
            ∑ k ∈ S6,
              exp (2 * Real.pi * I * dot3 q330 (centroidPoint (n k) (s k)))) +
            ∑ k ∈ Sm,
              exp (2 * Real.pi * I * dot3 q330 (centroidPoint (n k) (s k))) := by
            rw [sum_union hdisj01]
      _ = _ := by abel
  have h0 : ∀ k ∈ S0,
      exp (2 * Real.pi * I * dot3 q330 (centroidPoint (n k) (s k))) = 1 := by
    intro k hk; simp only [S0, mem_filter, mem_univ, true_and] at hk
    exact exp_centroid_at_t0 (n k) (s k) hk
  have h6 : ∀ k ∈ S6,
      exp (2 * Real.pi * I * dot3 q330 (centroidPoint (n k) (s k))) =
        (cθ' : ℂ) - I * sθ' := by
    intro k hk; simp only [S6, mem_filter, mem_univ, true_and] at hk
    exact exp_centroid_at_t6 (n k) (s k) hk
  have hm : ∀ k ∈ Sm,
      exp (2 * Real.pi * I * dot3 q330 (centroidPoint (n k) (s k))) =
        (cθ' : ℂ) + I * sθ' := by
    intro k hk; simp only [Sm, mem_filter, mem_univ, true_and] at hk
    exact exp_centroid_at_tneg6 (n k) (s k) hk
  rw [hsum, sum_congr rfl h0, sum_congr rfl h6, sum_congr rfl hm]
  simp only [sum_const, nsmul_eq_mul, mul_one]
  simp only [countT, S0, S6, Sm]

lemma re_sum_eq {N : ℕ}
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (∑ k : Fin N,
        exp (2 * Real.pi * I * dot3 q330 (centroidPoint (n k) (s k)))).re =
      (countT s 0 : ℝ) +
        ((countT s 6 : ℝ) + (countT s (-6) : ℝ)) * cθ' := by
  rw [sum_exp_eq_counts n s hs]
  simp [sub_re, add_re, mul_re, I_re, I_im, ofReal_re, ofReal_im]
  ring

lemma im_sum_eq {N : ℕ}
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (∑ k : Fin N,
        exp (2 * Real.pi * I * dot3 q330 (centroidPoint (n k) (s k)))).im =
      ((countT s (-6) : ℝ) - (countT s 6 : ℝ)) * sθ' := by
  rw [sum_exp_eq_counts n s hs]
  simp [sub_im, add_im, mul_im, I_re, I_im, ofReal_re, ofReal_im]
  ring

lemma norm_structureFactor_eq {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ) :
    ‖structureFactor (fun k => centroidPoint (n k) (s k)) q330‖ =
      ‖(∑ k : Fin N,
          exp (2 * Real.pi * I * dot3 q330 (centroidPoint (n k) (s k))))‖ /
        (N : ℝ) := by
  unfold structureFactor
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  field_simp

lemma c0_div_N3_le_two_fifths_div_N {N : ℕ} (hN : 1 ≤ N) :
    c0 / (N : ℝ) ^ 3 ≤ (2 / 5 : ℝ) / N := by
  unfold c0
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hN2 : (1 : ℝ) ≤ (N : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  have hpos1 : (0 : ℝ) < 65 * N ^ 3 := by positivity
  have heqL : (1 / 65 : ℝ) / N ^ 3 = 1 / (65 * N ^ 3) := by field_simp
  have heqR : (2 / 5 : ℝ) / N = 2 / (5 * N) := by field_simp
  rw [heqL, heqR]
  rw [div_le_div_iff₀ hpos1 (by positivity)]
  nlinarith [hN2, hNpos]

lemma c0_div_N3_le_one_div_N {N : ℕ} (hN : 1 ≤ N) :
    c0 / (N : ℝ) ^ 3 ≤ (1 : ℝ) / N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have h := c0_div_N3_le_two_fifths_div_N hN
  have : (2 / 5 : ℝ) / N ≤ 1 / N := by
    exact div_le_div_of_nonneg_right (by norm_num) hNpos.le
  exact le_trans h this

lemma c0_div_N3_le_one {N : ℕ} (hN : 1 ≤ N) :
    c0 / (N : ℝ) ^ 3 ≤ 1 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  exact le_trans (c0_div_N3_le_one_div_N hN) (div_le_one_of_le₀
    (by exact_mod_cast hN : (1 : ℝ) ≤ N) hNpos.le)

/-! ## Main lower bound -/

/-- `[P, Lean]` Explicit bound `‖F(q₃₃₀)‖ ≥ (1/65) / N³`. -/
theorem norm_structureFactor_ge_c0_div_N_pow_three {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    c0 / (N : ℝ) ^ 3 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) q330‖ := by
  set a := countT s 0
  set b := countT s 6
  set b' := countT s (-6)
  have hcard : a + b + b' = N := countT_add_eq_card s hs
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  set S := (∑ k : Fin N,
      exp (2 * Real.pi * I * dot3 q330 (centroidPoint (n k) (s k))))
  have hnormF := norm_structureFactor_eq hN n s
  have hre : S.re = (a : ℝ) + ((b : ℝ) + (b' : ℝ)) * cθ' := by
    change (∑ k : Fin N,
        exp (2 * Real.pi * I * dot3 q330 (centroidPoint (n k) (s k)))).re = _
    exact re_sum_eq n s hs
  have him : S.im = ((b' : ℝ) - (b : ℝ)) * sθ' := by
    change (∑ k : Fin N,
        exp (2 * Real.pi * I * dot3 q330 (centroidPoint (n k) (s k)))).im = _
    exact im_sum_eq n s hs
  by_cases hbb : b = b'
  · have him0 : S.im = 0 := by
      rw [him, hbb, sub_self, zero_mul]
    have hre' : S.re = (a : ℝ) + (2 * (b : ℝ)) * cθ' := by
      rw [hre, hbb]; ring
    have hS : S = ↑((a : ℝ) + (2 * (b : ℝ)) * cθ') := by
      apply Complex.ext
      · simp [hre']
      · simp [him0]
    have hNF : ‖S‖ = |((a : ℝ) + (2 * (b : ℝ)) * cθ')| := by
      rw [hS, Complex.norm_real, Real.norm_eq_abs]
    rw [hnormF, hNF]
    set p : ℤ := (a : ℤ)
    set q : ℤ := 2 * (b : ℤ)
    have hpq : ((a : ℝ) + (2 * (b : ℝ)) * cθ') = ((p : ℝ) + (q : ℝ) * cθ') := by
      unfold p q; push_cast; ring
    have hqN : |(q : ℝ)| ≤ (N : ℝ) := by
      have hqnn : 0 ≤ (q : ℝ) := by
        unfold q; exact_mod_cast (Int.natCast_nonneg (2 * b))
      have h2b : (q : ℝ) = 2 * (b : ℝ) := by unfold q; push_cast; rfl
      have hsum : (a + 2 * b : ℕ) = N := by
        have : a + b + b' = N := hcard
        rw [hbb] at this
        omega
      have : (2 * (b : ℝ)) ≤ N := by
        have hs' : (a : ℝ) + 2 * (b : ℝ) = (N : ℝ) := by exact_mod_cast hsum
        have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg _
        linarith
      rw [abs_of_nonneg hqnn, h2b]
      exact this
    by_cases hb0 : b = 0
    · have haN : a = N := by omega
      have : |((a : ℝ) + (2 * (b : ℝ)) * cθ')| = (N : ℝ) := by
        simp [hb0, haN]
      rw [this, div_self (ne_of_gt hNpos)]
      exact c0_div_N3_le_one hN
    · have hqne : q ≠ 0 := by
        unfold q
        have : (b : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hb0
        omega
      rw [hpq]
      by_cases hge1 : 1 ≤ |((p : ℝ) + (q : ℝ) * cθ')|
      · have : 1 / (N : ℝ) ≤ |((p : ℝ) + (q : ℝ) * cθ')| / N :=
          div_le_div_of_nonneg_right hge1 hNpos.le
        exact le_trans (c0_div_N3_le_one_div_N hN) this
      · have hsmall : |((p : ℝ) + (q : ℝ) * cθ')| < 1 := lt_of_not_ge hge1
        have hlb := abs_linform_ge_of_small p q hqne hsmall
        have hstep :
            1 / (65 * (q : ℝ) ^ 2) / N ≤ |((p : ℝ) + (q : ℝ) * cθ')| / N :=
          div_le_div_of_nonneg_right hlb hNpos.le
        have hq2 : (q : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := by
          have h1 : (q : ℝ) ^ 2 = |(q : ℝ)| ^ 2 := (sq_abs (q : ℝ)).symm
          rw [h1]
          exact pow_le_pow_left₀ (abs_nonneg (q : ℝ)) hqN 2
        have hcmp : c0 / (N : ℝ) ^ 3 ≤ 1 / (65 * (q : ℝ) ^ 2) / N := by
          unfold c0
          have hL : (1 / 65 : ℝ) / N ^ 3 = 1 / (65 * N ^ 3) := by field_simp
          have hR : (1 : ℝ) / (65 * (q : ℝ) ^ 2) / N =
              1 / (65 * (q : ℝ) ^ 2 * N) := by field_simp
          rw [hL, hR]
          have hpos1 : (0 : ℝ) < 65 * N ^ 3 := by positivity
          have hpos2 : (0 : ℝ) < 65 * (q : ℝ) ^ 2 * N := by
            have : (q : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hqne
            positivity
          rw [one_div_le_one_div hpos1 hpos2]
          nlinarith [hq2, hNpos]
        exact le_trans hcmp hstep
  · have hdiff : (1 : ℝ) ≤ |((b' : ℝ) - (b : ℝ))| := by
      have hne : (b : ℤ) ≠ (b' : ℤ) := Nat.cast_injective.ne hbb
      have hz : ((b' : ℤ) - (b : ℤ)) ≠ 0 := sub_ne_zero.mpr (hne.symm)
      have hle' : (1 : ℝ) ≤ |(((b' : ℤ) - (b : ℤ) : ℤ) : ℝ)| :=
        abs_one_le_int hz
      have hcast : |(((b' : ℤ) - (b : ℤ) : ℤ) : ℝ)| =
          |((b' : ℝ) - (b : ℝ))| := by
        push_cast; rfl
      exact (hcast ▸ hle')
    have himabs : (2 / 5 : ℝ) ≤ |S.im| := by
      rw [him, abs_mul, abs_of_pos (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2 / 5)
        sθ'_ge_two_div_five)]
      nlinarith [sθ'_ge_two_div_five, hdiff]
    have hSbound : (2 / 5 : ℝ) ≤ ‖S‖ :=
      le_trans himabs (Complex.abs_im_le_norm S)
    have hle : (2 / 5 : ℝ) / N ≤ ‖S‖ / N :=
      div_le_div_of_nonneg_right hSbound hNpos.le
    have hgoal : c0 / (N : ℝ) ^ 3 ≤ ‖S‖ / N :=
      le_trans (c0_div_N3_le_two_fifths_div_N hN) hle
    rw [hnormF]
    change c0 / (N : ℝ) ^ 3 ≤ ‖S‖ / N
    exact hgoal

/-- `|F|² ≥ c0² / N⁶`. -/
theorem normSq_structureFactor_ge_c0_sq_div_N_pow_six {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    c0 ^ 2 / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) q330‖ ^ 2 := by
  have h := norm_structureFactor_ge_c0_div_N_pow_three hN n s hs
  have hc0 : 0 ≤ c0 / (N : ℝ) ^ 3 := div_nonneg c0_pos.le (by positivity)
  have := pow_le_pow_left₀ hc0 h (n := 2)
  convert this using 1
  ring

#print axioms gR_cθ'_eq_zero
#print axioms abs_cθ'_lt_ninety_one_hundredths'
#print axioms sθ'_ge_two_div_five
#print axioms abs_linform_ge_of_small
#print axioms norm_structureFactor_ge_c0_div_N_pow_three
#print axioms normSq_structureFactor_ge_c0_sq_div_N_pow_six

end LeanLab.Scratch.LemmaDLowerBound330
