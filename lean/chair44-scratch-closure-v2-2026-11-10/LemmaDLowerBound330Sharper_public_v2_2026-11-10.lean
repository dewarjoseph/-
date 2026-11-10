import LeanLab.Scratch.LemmaDLowerBound330
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Sharper explicit constant at q = (3,3,0)
(public-screen)

Public-screen v2 copy of LeanLab.Scratch.LemmaDLowerBound330Sharper (official pin src
`6e0751833d278eda9ee84ad5d55e130d31e7d05f95031b136ec5e26d421d41ea`).
Header redacted; theorem bodies are unchanged. This copy is not a
replacement pin.

**[P, Lean]** A uniform bound `|h(x, c')| < 34` holds for every real
`x` with `|x − c'| < 1`, where `c' = cos(6π/7)` and `h` is the cubic
cofactor of LemmaDLowerBound220/330. Consequently, for every nonempty
finite equal-weight D-form box at `q = (3,3,0)`,

  `‖F‖ ≥ c0' / N³`    with    `c0' = 1/34`.

This improves the triangle-inequality constant `H = 65` of
LemmaDLowerBound330 (which gave `c0 = 1/65`) without changing the
exponent. The argument uses that `h(·, c')` is strictly decreasing on
the closed unit interval about `c'` (the vertex of the quadratic lies
to the right of `c' + 1`, since `c' < −5/6`), so `|h|` on the open
interval is strictly less than the larger endpoint value
`h(c' − 1, c') = 24 c'² − 16 c'`. Combined with the tighter bound
`|c'| < 901/1000` (the same `pCos`-monotonicity argument as in
LemmaDLowerBound330, evaluated at `901/1000` rather than `91/100`),
this endpoint is strictly less than 34. (A numeric check puts the
true supremum near 33.90 as `x → (c' − 1)⁺`; this file does not claim
that the constant 34 is sharp.)

The exponent 3 is what this argument gives, not claimed sharp. The
infimum over all boxes at `(3,3,0)` is not claimed here (stays `[X]`).

D-form class only. Scratch; not a Lake target; not peer reviewed.

This file is source-only and is not a Lake package. It claims nothing
beyond the theorems stated below.

Dated 2026-11-10.
-/

namespace LeanLab.Scratch.LemmaDLowerBound330Sharper

open Complex
open LeanLab.Scratch.LemmaD4 (structureFactor centroidPoint)
open LeanLab.Scratch.LemmaDL1Six (q330)
open LeanLab.Scratch.LemmaDLowerBound220
  (hR gR gZ gQ gR_sub gZ_eq_q_pow gQ_ne_zero gZ_ne_zero abs_one_le_int)
open LeanLab.Scratch.LemmaDLowerBound330
  (cθ' sθ' pCos pCos_cos_pi_div_seven cos_pi_div_seven_pos
    cos_pi_div_seven_gt_cos_pi_div_six cθ'_eq_neg_cos_pi_div_seven
    sθ'_ge_two_div_five countT countT_add_eq_card re_sum_eq im_sum_eq
    norm_structureFactor_eq gR_cθ'_eq_zero)

/-! ## The improved constant -/

noncomputable def c0' : ℝ := 1 / 34

lemma c0'_pos : 0 < c0' := by
  unfold c0'
  norm_num

/-! ## Tighter bound |c'| < 901/1000 -/

lemma cθ'_lt_neg_five_six : cθ' < -5 / 6 := by
  rw [cθ'_eq_neg_cos_pi_div_seven]
  have hlt : Real.cos (Real.pi / 6) < Real.cos (Real.pi / 7) :=
    cos_pi_div_seven_gt_cos_pi_div_six
  have h6 : Real.cos (Real.pi / 6) = Real.sqrt 3 / 2 := Real.cos_pi_div_six
  have hsq : (5 / 3 : ℝ) ≤ Real.sqrt 3 :=
    (Real.le_sqrt (by norm_num) (by positivity)).mpr (by norm_num)
  have : (5 / 6 : ℝ) ≤ Real.sqrt 3 / 2 := by linarith
  linarith

lemma pCos_eval_nine_hundred_one_thousandths :
    (0 : ℝ) < pCos (901 / 1000) := by
  unfold pCos
  norm_num

lemma pCos_mono_of_ge_seven_tenths {x y : ℝ}
    (hx : (7 / 10 : ℝ) ≤ x) (hxy : x ≤ y) :
    pCos x ≤ pCos y := by
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

lemma cos_pi_div_seven_ge_seven_tenths :
    (7 / 10 : ℝ) ≤ Real.cos (Real.pi / 7) := by
  have hcos6 : Real.cos (Real.pi / 6) = Real.sqrt 3 / 2 := Real.cos_pi_div_six
  have hsqrt : (7 / 10 : ℝ) ≤ Real.sqrt 3 / 2 := by
    have hsq : (7 / 5 : ℝ) ≤ Real.sqrt 3 :=
      (Real.le_sqrt (by norm_num) (by positivity)).mpr (by norm_num)
    linarith
  have hcu : Real.sqrt 3 / 2 < Real.cos (Real.pi / 7) := by
    rw [← hcos6]
    exact cos_pi_div_seven_gt_cos_pi_div_six
  exact le_trans hsqrt (le_of_lt hcu)

lemma abs_cθ'_lt_nine_hundred_one_thousandths : |cθ'| < 901 / 1000 := by
  rw [cθ'_eq_neg_cos_pi_div_seven, abs_neg, abs_of_pos cos_pi_div_seven_pos]
  set u := Real.cos (Real.pi / 7)
  have hu0 : pCos u = 0 := pCos_cos_pi_div_seven
  have hge : (7 / 10 : ℝ) ≤ u := cos_pi_div_seven_ge_seven_tenths
  have h901 : (7 / 10 : ℝ) ≤ 901 / 1000 := by norm_num
  by_contra h
  have : (901 / 1000 : ℝ) ≤ u := le_of_not_gt h
  have : pCos (901 / 1000) ≤ pCos u := pCos_mono_of_ge_seven_tenths h901 this
  rw [hu0] at this
  linarith [pCos_eval_nine_hundred_one_thousandths]

/-! ## |h| bound on |x − c'| < 1 -/

lemma hR_sub_same (x y c : ℝ) :
    hR x c - hR y c = (x - y) * (8 * (x + y) + 8 * c + 4) := by
  unfold hR
  ring

lemma hR_anti_on_left_of_right {x y : ℝ}
    (hxy : x < y) (hy : y ≤ cθ' + 1) :
    hR y cθ' < hR x cθ' := by
  have hdiff : hR x cθ' - hR y cθ' =
      (x - y) * (8 * (x + y) + 8 * cθ' + 4) := hR_sub_same x y cθ'
  have hxyneg : x - y < 0 := sub_neg.mpr hxy
  have hsum : x + y < 2 * (cθ' + 1) := by linarith
  have hfac : 8 * (x + y) + 8 * cθ' + 4 < 0 := by
    have hlt : 8 * (x + y) + 8 * cθ' + 4 <
        8 * (2 * (cθ' + 1)) + 8 * cθ' + 4 := by linarith
    have hsimp : 8 * (2 * (cθ' + 1)) + 8 * cθ' + 4 = 24 * cθ' + 20 := by ring
    have hneg : 24 * cθ' + 20 < 0 := by
      linarith [cθ'_lt_neg_five_six]
    linarith
  have : 0 < hR x cθ' - hR y cθ' := by
    rw [hdiff]
    exact mul_pos_of_neg_of_neg hxyneg hfac
  linarith

lemma hR_eval_left : hR (cθ' - 1) cθ' = 24 * cθ' ^ 2 - 16 * cθ' := by
  unfold hR
  ring

lemma hR_eval_right : hR (cθ' + 1) cθ' = 24 * cθ' ^ 2 + 32 * cθ' + 8 := by
  unfold hR
  ring

lemma hR_left_lt_thirtyfour : hR (cθ' - 1) cθ' < 34 := by
  rw [hR_eval_left]
  have hc := abs_cθ'_lt_nine_hundred_one_thousandths
  have hneg : cθ' < 0 := by linarith [cθ'_lt_neg_five_six]
  have habs : |cθ'| = -cθ' := abs_of_neg hneg
  have heq : 24 * cθ' ^ 2 - 16 * cθ' = 24 * |cθ'| ^ 2 + 16 * |cθ'| := by
    have hsq : cθ' ^ 2 = |cθ'| ^ 2 := (sq_abs cθ').symm
    rw [hsq, habs]
    ring
  rw [heq]
  have h1 : 24 * |cθ'| ^ 2 < 24 * (901 / 1000 : ℝ) ^ 2 := by
    have hmul := mul_self_lt_mul_self (abs_nonneg cθ') hc
    have habs2 : |cθ'| * |cθ'| = |cθ'| ^ 2 := by ring
    have hR2 : (901 / 1000 : ℝ) * (901 / 1000) = (901 / 1000) ^ 2 := by ring
    have : |cθ'| ^ 2 < (901 / 1000 : ℝ) ^ 2 := by rwa [habs2, hR2] at hmul
    nlinarith
  have h2 : 16 * |cθ'| < 16 * (901 / 1000 : ℝ) := by nlinarith [hc]
  have hnum : 24 * (901 / 1000 : ℝ) ^ 2 + 16 * (901 / 1000) < 34 := by
    norm_num
  linarith

lemma hR_right_gt_neg_thirtyfour : -34 < hR (cθ' + 1) cθ' := by
  rw [hR_eval_right]
  have hc := abs_cθ'_lt_nine_hundred_one_thousandths
  have hlo : -(901 / 1000 : ℝ) < cθ' := (abs_lt.mp hc).1
  have hsq : (0 : ℝ) ≤ 24 * cθ' ^ 2 := by positivity
  have hnum : (8 : ℝ) + 32 * (-(901 / 1000)) > -34 := by norm_num
  linarith

lemma abs_hR_lt_thirtyfour (x : ℝ) (hx : |x - cθ'| < 1) :
    |hR x cθ'| < 34 := by
  have hxabs := abs_lt.mp hx
  have hxI : cθ' - 1 < x ∧ x < cθ' + 1 :=
    ⟨by linarith [hxabs.1], by linarith [hxabs.2]⟩
  have hltR : hR (cθ' + 1) cθ' < hR x cθ' :=
    hR_anti_on_left_of_right hxI.2 le_rfl
  have hltL : hR x cθ' < hR (cθ' - 1) cθ' :=
    hR_anti_on_left_of_right hxI.1 (by linarith [hxI.2])
  have hlo : -34 < hR x cθ' := lt_trans hR_right_gt_neg_thirtyfour hltR
  have hhi : hR x cθ' < 34 := lt_trans hltL hR_left_lt_thirtyfour
  exact abs_lt.mpr ⟨hlo, hhi⟩

/-! ## Linear form bound with H = 34 -/

lemma abs_linform_ge_of_small (p q : ℤ) (hq : q ≠ 0)
    (hsmall : |((p : ℝ) + (q : ℝ) * cθ')| < 1) :
    1 / (34 * (q : ℝ) ^ 2) ≤ |((p : ℝ) + (q : ℝ) * cθ')| := by
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
  have hh : |hR x0 cθ'| < 34 := abs_hR_lt_thirtyfour x0 hxlt
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
  have hcmp : |(q : ℝ)| ^ 2 * |hR x0 cθ'| ≤ 34 * (q : ℝ) ^ 2 := by
    have hsq : (q : ℝ) ^ 2 = |(q : ℝ)| ^ 2 := (sq_abs (q : ℝ)).symm
    rw [hsq]
    nlinarith [le_of_lt hh, sq_nonneg |(q : ℝ)|]
  have hnumpos : 0 < 34 * (q : ℝ) ^ 2 := by
    have : (q : ℝ) ≠ 0 := hqR
    positivity
  refine (div_le_div_iff₀ hnumpos hdenpos).mpr ?_
  nlinarith [habsZ, hcmp, sq_nonneg |(q : ℝ)|]

/-! ## Comparison lemmas for c0' / N³ -/

lemma c0'_div_N3_le_two_fifths_div_N {N : ℕ} (hN : 1 ≤ N) :
    c0' / (N : ℝ) ^ 3 ≤ (2 / 5 : ℝ) / N := by
  unfold c0'
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hN2 : (1 : ℝ) ≤ (N : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  have hpos1 : (0 : ℝ) < 34 * N ^ 3 := by positivity
  have heqL : (1 / 34 : ℝ) / N ^ 3 = 1 / (34 * N ^ 3) := by field_simp
  have heqR : (2 / 5 : ℝ) / N = 2 / (5 * N) := by field_simp
  rw [heqL, heqR]
  rw [div_le_div_iff₀ hpos1 (by positivity)]
  nlinarith [hN2, hNpos]

lemma c0'_div_N3_le_one_div_N {N : ℕ} (hN : 1 ≤ N) :
    c0' / (N : ℝ) ^ 3 ≤ (1 : ℝ) / N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have h := c0'_div_N3_le_two_fifths_div_N hN
  have : (2 / 5 : ℝ) / N ≤ 1 / N :=
    div_le_div_of_nonneg_right (by norm_num) hNpos.le
  exact le_trans h this

lemma c0'_div_N3_le_one {N : ℕ} (hN : 1 ≤ N) :
    c0' / (N : ℝ) ^ 3 ≤ 1 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  exact le_trans (c0'_div_N3_le_one_div_N hN)
    (div_le_one_of_le₀ (by exact_mod_cast hN : (1 : ℝ) ≤ N) hNpos.le)

/-! ## Main lower bound with c0' = 1/34 -/

/-- `[P, Lean]` Explicit bound `‖F(q₃₃₀)‖ ≥ (1/34) / N³`. -/
theorem norm_structureFactor_ge_c0'_div_N_pow_three {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    c0' / (N : ℝ) ^ 3 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) q330‖ := by
  set a := countT s 0
  set b := countT s 6
  set b' := countT s (-6)
  have hcard : a + b + b' = N := countT_add_eq_card s hs
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  set S := (∑ k : Fin N,
      exp (2 * Real.pi * I * LeanLab.Scratch.LemmaD4.dot3 q330
        (centroidPoint (n k) (s k))))
  have hnormF := norm_structureFactor_eq hN n s
  have hre : S.re = (a : ℝ) + ((b : ℝ) + (b' : ℝ)) * cθ' := by
    change (∑ k : Fin N,
        exp (2 * Real.pi * I * LeanLab.Scratch.LemmaD4.dot3 q330
          (centroidPoint (n k) (s k)))).re = _
    exact re_sum_eq n s hs
  have him : S.im = ((b' : ℝ) - (b : ℝ)) * sθ' := by
    change (∑ k : Fin N,
        exp (2 * Real.pi * I * LeanLab.Scratch.LemmaD4.dot3 q330
          (centroidPoint (n k) (s k)))).im = _
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
    have hpq : ((a : ℝ) + (2 * (b : ℝ)) * cθ') =
        ((p : ℝ) + (q : ℝ) * cθ') := by
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
      exact c0'_div_N3_le_one hN
    · have hqne : q ≠ 0 := by
        unfold q
        have : (b : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hb0
        omega
      rw [hpq]
      by_cases hge1 : 1 ≤ |((p : ℝ) + (q : ℝ) * cθ')|
      · have : 1 / (N : ℝ) ≤ |((p : ℝ) + (q : ℝ) * cθ')| / N :=
          div_le_div_of_nonneg_right hge1 hNpos.le
        exact le_trans (c0'_div_N3_le_one_div_N hN) this
      · have hsmall : |((p : ℝ) + (q : ℝ) * cθ')| < 1 := lt_of_not_ge hge1
        have hlb := abs_linform_ge_of_small p q hqne hsmall
        have hstep :
            1 / (34 * (q : ℝ) ^ 2) / N ≤ |((p : ℝ) + (q : ℝ) * cθ')| / N :=
          div_le_div_of_nonneg_right hlb hNpos.le
        have hq2 : (q : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := by
          have h1 : (q : ℝ) ^ 2 = |(q : ℝ)| ^ 2 := (sq_abs (q : ℝ)).symm
          rw [h1]
          exact pow_le_pow_left₀ (abs_nonneg (q : ℝ)) hqN 2
        have hcmp : c0' / (N : ℝ) ^ 3 ≤ 1 / (34 * (q : ℝ) ^ 2) / N := by
          unfold c0'
          have hL : (1 / 34 : ℝ) / N ^ 3 = 1 / (34 * N ^ 3) := by field_simp
          have hR : (1 : ℝ) / (34 * (q : ℝ) ^ 2) / N =
              1 / (34 * (q : ℝ) ^ 2 * N) := by field_simp
          rw [hL, hR]
          have hpos1 : (0 : ℝ) < 34 * N ^ 3 := by positivity
          have hpos2 : (0 : ℝ) < 34 * (q : ℝ) ^ 2 * N := by
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
    have hgoal : c0' / (N : ℝ) ^ 3 ≤ ‖S‖ / N :=
      le_trans (c0'_div_N3_le_two_fifths_div_N hN) hle
    rw [hnormF]
    change c0' / (N : ℝ) ^ 3 ≤ ‖S‖ / N
    exact hgoal

/-- `|F|² ≥ c0'² / N⁶`. -/
theorem normSq_structureFactor_ge_c0'_sq_div_N_pow_six {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    c0' ^ 2 / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) q330‖ ^ 2 := by
  have h := norm_structureFactor_ge_c0'_div_N_pow_three hN n s hs
  have hnn : 0 ≤ c0' / (N : ℝ) ^ 3 := div_nonneg c0'_pos.le (by positivity)
  have hF : 0 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) q330‖ :=
    norm_nonneg _
  have hsq := mul_le_mul h h hnn hF
  have hL : (c0' / (N : ℝ) ^ 3) * (c0' / (N : ℝ) ^ 3) =
      c0' ^ 2 / (N : ℝ) ^ 6 := by
    field_simp
  have hR : ‖structureFactor (fun k => centroidPoint (n k) (s k)) q330‖ *
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) q330‖ =
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) q330‖ ^ 2 := by
    ring
  rwa [hL, hR] at hsq

#print axioms abs_hR_lt_thirtyfour
#print axioms abs_linform_ge_of_small
#print axioms c0'_pos
#print axioms norm_structureFactor_ge_c0'_div_N_pow_three
#print axioms normSq_structureFactor_ge_c0'_sq_div_N_pow_six

end LeanLab.Scratch.LemmaDLowerBound330Sharper
