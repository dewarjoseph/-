import LeanLab.Scratch.LemmaDNoZero220
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Algebra.Ring.Rat
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.IntervalCases

/-!
# Explicit polynomial lower bound at q = (2,2,0)
(public-screen)

Public-screen v2 copy of LeanLab.Scratch.LemmaDLowerBound220 (official pin src
`0e05234ecae80955f385e4cc11c07b0e6af7f043031d05407e0e25a7426af2bb`).
Header redacted; theorem bodies are unchanged. This copy is not a
replacement pin.

**[P, Lean]** There is an explicit constant `c0 = 1/30 > 0` such that for
every nonempty finite equal-weight D-form box at `q = (2,2,0)`,
`‖F‖ ≥ c0 / N³` and therefore `|F|² ≥ c0² / N⁶`.

This complements `LemmaDInfZero220` (`sInf = 0` over all boxes): the
intensity can be arbitrarily small, but for each fixed `N` it is at least
order `N⁻³`. The exponent 3 is what this argument gives, not claimed
sharp.

**Argument.** With counts `a,b,b'` of `t ∈ {0,4,−4}` and `θ = 4π/7`,
`N·F = (a+(b+b')cos θ) + i(b'−b)sin θ` (LemmaDNoZero220).

* If `b ≠ b'`, `|Im(N F)| ≥ sin θ ≥ 1/2`, so `‖F‖ ≥ (1/2)/N ≥ c0/N³`.
* If `b = b'` then `|N F| = |p + q c|` with `c = cos θ`, `p = a`, `q = 2b`.
  If `q = 0` then `|N F| = N ≥ 1`. The cosine `c` is a root of
  `g(x) = 8x³+4x²−4x−1` (from `ζ₇²+ζ₇⁵ = 2c` and `ζ₇⁷=1`). The
  polynomial `g` has no rational root (rational-root check: any rational
  root has numerator `±1` and denominator dividing 8, and none works).
  Thus for integers `p,q` with `q ≠ 0`, `q³ g(−p/q)` is a nonzero
  integer, and `g(x₀)−g(c) = (x₀−c) h(x₀,c)` yields
  `|p+q c| ≥ 1/(|q|² |h|)`. When `|p+q c| < 1` one has `|c| < 1/4` and
  `|h| < 30`, so `|N F| ≥ 1/(30 N²)` and `‖F‖ ≥ c0/N³`.

**Not proved / out of scope:**
* Sharpness of the exponent 3, or any other `q`.
* D-form class only. Scratch; not a Lake target; not peer reviewed.

This file is source-only and is not a Lake package. It claims nothing
beyond the theorems stated below.

Dated 2026-11-10.
-/

namespace LeanLab.Scratch.LemmaDLowerBound220

open Complex Finset
open LeanLab.Scratch.LemmaD4 (dot3 structureFactor centroidPoint exp_two_pi_I_int)
open LeanLab.Scratch.LemmaDIntVec
  (qReal signedWeight zeta7 zeta7_pow isPrimitiveRoot_zeta7)
open LeanLab.Scratch.LemmaDNoZero220
  (qZ220 q220 countT countT_add_eq_card re_sum_eq im_sum_eq
    sin_four_pi_div_seven_pos)

noncomputable def cθ : ℝ := Real.cos (4 * Real.pi / 7)
noncomputable def sθ : ℝ := Real.sin (4 * Real.pi / 7)

def gR (x : ℝ) : ℝ := 8 * x ^ 3 + 4 * x ^ 2 - 4 * x - 1
def hR (x y : ℝ) : ℝ := 8 * (x ^ 2 + x * y + y ^ 2) + 4 * (x + y) - 4
def gZ (p q : ℤ) : ℤ := -8 * p ^ 3 + 4 * p ^ 2 * q + 4 * p * q ^ 2 - q ^ 3
def gQ (x : ℚ) : ℚ := 8 * x ^ 3 + 4 * x ^ 2 - 4 * x - 1

noncomputable def c0 : ℝ := 1 / 30

lemma c0_pos : 0 < c0 := by
  unfold c0
  norm_num

/-! ## Trigonometric bounds -/

lemma sθ_eq_sin_three : sθ = Real.sin (3 * Real.pi / 7) := by
  unfold sθ
  have hangle : Real.pi - 4 * Real.pi / 7 = 3 * Real.pi / 7 := by ring
  rw [← hangle, Real.sin_pi_sub]

lemma sin_four_pi_div_seven_ge_half : (1 / 2 : ℝ) ≤ sθ := by
  have hlt : Real.pi / 6 < 3 * Real.pi / 7 := by
    have hmul :
        ((1 : ℝ) / 6) * Real.pi < ((3 : ℝ) / 7) * Real.pi :=
      mul_lt_mul_of_pos_right (by norm_num) Real.pi_pos
    convert hmul using 1 <;> ring
  have hle : 3 * Real.pi / 7 ≤ Real.pi / 2 := by
    have hmul :
        ((3 : ℝ) / 7) * Real.pi ≤ ((1 : ℝ) / 2) * Real.pi :=
      mul_le_mul_of_nonneg_right (by norm_num) Real.pi_pos.le
    convert hmul using 1 <;> ring
  have hlo : -(Real.pi / 2) ≤ Real.pi / 6 := by linarith [Real.pi_pos]
  have hsin :=
    Real.sin_lt_sin_of_lt_of_le_pi_div_two hlo hle hlt
  rw [sθ_eq_sin_three, ← Real.sin_pi_div_six]
  exact le_of_lt hsin

lemma cos_eq_neg_sin_pi_div_fourteen : cθ = -Real.sin (Real.pi / 14) := by
  unfold cθ
  have hadd : 4 * Real.pi / 7 = Real.pi / 14 + Real.pi / 2 := by ring
  rw [hadd, Real.cos_add_pi_div_two]

lemma abs_cθ_lt_one_div_four : |cθ| < 1 / 4 := by
  rw [cos_eq_neg_sin_pi_div_fourteen, abs_neg]
  have hpos : 0 < Real.pi / 14 := by positivity
  have hsin : Real.sin (Real.pi / 14) < Real.pi / 14 := Real.sin_lt hpos
  have hpi : Real.pi / 14 < 1 / 4 := by
    have hπ : Real.pi < (7 / 2 : ℝ) :=
      lt_trans Real.pi_lt_d2 (by norm_num)
    have hdiv := div_lt_div_of_pos_right hπ (by norm_num : (0 : ℝ) < 14)
    have : (7 / 2 : ℝ) / 14 = 1 / 4 := by norm_num
    rwa [this] at hdiv
  have hsinpos : 0 < Real.sin (Real.pi / 14) :=
    Real.sin_pos_of_pos_of_lt_pi hpos (by linarith [Real.pi_pos])
  rw [abs_of_pos hsinpos]
  exact lt_trans hsin hpi

/-! ## The cubic identity g(c) = 0 via ζ₇ -/

lemma zeta7_pow_seven : zeta7 ^ 7 = 1 :=
  isPrimitiveRoot_zeta7.pow_eq_one

lemma zeta7_pow_add_seven (n : ℕ) : zeta7 ^ (n + 7) = zeta7 ^ n := by
  rw [pow_add, zeta7_pow_seven, mul_one]

lemma sum_zeta7_pow : (∑ i ∈ range 7, zeta7 ^ i) = 0 :=
  IsPrimitiveRoot.geom_sum_eq_zero isPrimitiveRoot_zeta7 (by decide)

lemma sum_zeta7_explicit :
    (1 : ℂ) + zeta7 + zeta7 ^ 2 + zeta7 ^ 3 + zeta7 ^ 4 +
      zeta7 ^ 5 + zeta7 ^ 6 = 0 := by
  have hlist :
      (∑ i ∈ range 7, zeta7 ^ i) =
        zeta7 ^ 0 + zeta7 ^ 1 + zeta7 ^ 2 + zeta7 ^ 3 +
          zeta7 ^ 4 + zeta7 ^ 5 + zeta7 ^ 6 := by
    rw [sum_range_succ, sum_range_succ, sum_range_succ, sum_range_succ,
      sum_range_succ, sum_range_succ, sum_range_succ, sum_range_zero]
    abel
  simpa [pow_zero, pow_one, sum_zeta7_pow] using hlist.symm

lemma zeta7_sq_add_pow_five :
    zeta7 ^ 2 + zeta7 ^ 5 = 2 * (cθ : ℂ) := by
  rw [zeta7_pow, zeta7_pow]
  have h2 : (2 * Real.pi * I * (2 : ℕ) / 7 : ℂ) =
      (↑(4 * Real.pi / 7) : ℂ) * I := by
    push_cast; ring
  have h5 : (2 * Real.pi * I * (5 : ℕ) / 7 : ℂ) =
      (↑(-(4 * Real.pi / 7)) : ℂ) * I + 2 * Real.pi * I := by
    push_cast; ring
  rw [h2, h5, exp_add]
  have h2π : exp (2 * Real.pi * I) = 1 := by
    have h := exp_two_pi_I_int (1 : ℤ)
    have heq : (2 * Real.pi * I : ℂ) = 2 * Real.pi * I * ((1 : ℤ) : ℝ) := by
      push_cast; ring
    rw [heq, h]
  rw [h2π, mul_one]
  rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
  rw [Real.cos_neg, Real.sin_neg]
  unfold cθ
  push_cast
  ring

lemma eta_cubic_zero :
    (zeta7 ^ 2 + zeta7 ^ 5) ^ 3 + (zeta7 ^ 2 + zeta7 ^ 5) ^ 2
      - 2 * (zeta7 ^ 2 + zeta7 ^ 5) - 1 = 0 := by
  set z := zeta7
  have hz7 : z ^ 7 = 1 := zeta7_pow_seven
  have h8 : z ^ 8 = z := by
    rw [show (8 : ℕ) = 1 + 7 from by decide, zeta7_pow_add_seven, pow_one]
  have h9 : z ^ 9 = z ^ 2 := by
    rw [show (9 : ℕ) = 2 + 7 from by decide, zeta7_pow_add_seven]
  have h10 : z ^ 10 = z ^ 3 := by
    rw [show (10 : ℕ) = 3 + 7 from by decide, zeta7_pow_add_seven]
  have hp22 : z ^ 2 * z ^ 2 = z ^ 4 := by rw [← pow_add]
  have hp25 : z ^ 2 * z ^ 5 = z ^ 7 := by rw [← pow_add]
  have hp52 : z ^ 5 * z ^ 2 = z ^ 7 := by rw [← pow_add]
  have hp55 : z ^ 5 * z ^ 5 = z ^ 10 := by rw [← pow_add]
  have hη2 : (z ^ 2 + z ^ 5) ^ 2 = z ^ 4 + 2 + z ^ 3 := by
    calc
      (z ^ 2 + z ^ 5) ^ 2
          = z ^ 2 * z ^ 2 + z ^ 2 * z ^ 5 + z ^ 5 * z ^ 2 + z ^ 5 * z ^ 5 := by
            ring
      _ = z ^ 4 + z ^ 7 + z ^ 7 + z ^ 10 := by
            rw [hp22, hp25, hp52, hp55]
      _ = z ^ 4 + 2 + z ^ 3 := by
            rw [hz7, h10]; ring
  have hp24 : z ^ 2 * z ^ 4 = z ^ 6 := by rw [← pow_add]
  have hp23 : z ^ 2 * z ^ 3 = z ^ 5 := by rw [← pow_add]
  have hp54 : z ^ 5 * z ^ 4 = z ^ 9 := by rw [← pow_add]
  have hp53 : z ^ 5 * z ^ 3 = z ^ 8 := by rw [← pow_add]
  have hη3 : (z ^ 2 + z ^ 5) ^ 3 = z + 3 * z ^ 2 + 3 * z ^ 5 + z ^ 6 := by
    have hmul : (z ^ 2 + z ^ 5) ^ 3 = (z ^ 2 + z ^ 5) * (z ^ 2 + z ^ 5) ^ 2 := by
      ring
    rw [hmul, hη2]
    calc
      (z ^ 2 + z ^ 5) * (z ^ 4 + 2 + z ^ 3)
          = z ^ 2 * z ^ 4 + z ^ 2 * 2 + z ^ 2 * z ^ 3 +
              z ^ 5 * z ^ 4 + z ^ 5 * 2 + z ^ 5 * z ^ 3 := by
            ring
      _ = z ^ 6 + 2 * z ^ 2 + z ^ 5 + z ^ 9 + 2 * z ^ 5 + z ^ 8 := by
            rw [hp24, hp23, hp54, hp53]; ring
      _ = z + 3 * z ^ 2 + 3 * z ^ 5 + z ^ 6 := by
            rw [h9, h8]; ring
  rw [hη3, hη2]
  have hsum := sum_zeta7_explicit
  -- (z+3z²+3z⁵+z⁶)+(z⁴+2+z³)-2(z²+z⁵)-1 = 1+z+…+z⁶
  convert hsum using 1
  ring

lemma gR_cθ_eq_zero : gR cθ = 0 := by
  have hη := eta_cubic_zero
  rw [zeta7_sq_add_pow_five] at hη
  have hC : ((gR cθ : ℝ) : ℂ) = 0 := by
    unfold gR
    convert hη using 1
    push_cast
    ring
  exact_mod_cast (ofReal_eq_zero.mp hC)

lemma gR_sub (x y : ℝ) : gR x - gR y = (x - y) * hR x y := by
  unfold gR hR
  ring

lemma gZ_eq_q_pow (p q : ℤ) (hq : q ≠ 0) :
    (gZ p q : ℝ) = (q : ℝ) ^ 3 * gR (-(p : ℝ) / (q : ℝ)) := by
  unfold gZ gR
  have hqR : (q : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hq
  field_simp [hqR]
  push_cast
  ring

/-! ## No rational roots of g -/

lemma eq_one_of_coprime_dvd {a b : ℕ} (hc : Nat.Coprime a b) (hd : a ∣ b) :
    a = 1 := by
  have hgcd : Nat.gcd a b = a := Nat.gcd_eq_left hd
  have h1 : Nat.gcd a b = 1 := Nat.coprime_iff_gcd_eq_one.mp hc
  omega

lemma gQ_eval_candidates :
    gQ 1 ≠ 0 ∧ gQ (-1) ≠ 0 ∧
      gQ (1 / 2) ≠ 0 ∧ gQ (-(1 / 2)) ≠ 0 ∧
      gQ (1 / 4) ≠ 0 ∧ gQ (-(1 / 4)) ≠ 0 ∧
      gQ (1 / 8) ≠ 0 ∧ gQ (-(1 / 8)) ≠ 0 := by
  unfold gQ
  norm_num

lemma gQ_clear (n d : ℤ) (hd : (d : ℚ) ≠ 0) :
    gQ ((n : ℚ) / d) * (d : ℚ) ^ 3 =
      (8 * n ^ 3 + 4 * n ^ 2 * d - 4 * n * d ^ 2 - d ^ 3 : ℚ) := by
  unfold gQ
  field_simp [hd]

lemma gQ_ne_zero (x : ℚ) : gQ x ≠ 0 := by
  intro h0
  set n := x.num
  set d : ℤ := (x.den : ℤ)
  have hdpos : (0 : ℤ) < d := Nat.cast_pos.mpr x.den_pos
  have hdne : (d : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hdpos)
  have hx : x = (n : ℚ) / (d : ℚ) := by
    simpa [n, d] using (Rat.num_div_den x).symm
  have hint : (8 * n ^ 3 + 4 * n ^ 2 * d - 4 * n * d ^ 2 - d ^ 3 : ℤ) = 0 := by
    have hclear := gQ_clear n d hdne
    rw [← hx, h0, zero_mul] at hclear
    exact_mod_cast hclear.symm
  have hndvd : n ∣ d ^ 3 := by
    refine ⟨8 * n ^ 2 + 4 * n * d - 4 * d ^ 2, ?_⟩
    linarith [hint]
  have hcop : Nat.Coprime n.natAbs x.den := x.reduced
  have hcop3 : Nat.Coprime n.natAbs (x.den ^ 3) :=
    (Nat.coprime_pow_right_iff (by decide : 0 < 3) n.natAbs x.den).mpr hcop
  have habs : n.natAbs ∣ x.den ^ 3 := by
    have := Int.natAbs_dvd_natAbs.mpr hndvd
    simpa [d, Int.natAbs_pow, Int.natAbs_natCast] using this
  have hn1 : n.natAbs = 1 := eq_one_of_coprime_dvd hcop3 habs
  have hddvd : (x.den : ℤ) ∣ 8 * n ^ 3 := by
    refine ⟨d ^ 2 + 4 * n * d - 4 * n ^ 2, ?_⟩
    -- 8n³ = d(d² + 4 n d - 4 n²) from hint
    linarith [hint]
  have hcop8 : Nat.Coprime x.den (n.natAbs ^ 3) :=
    (Nat.coprime_pow_right_iff (by decide : 0 < 3) x.den n.natAbs).mpr hcop.symm
  have hden_mul : x.den ∣ 8 * n.natAbs ^ 3 := by
    have h1 : x.den ∣ (8 * n ^ 3).natAbs := by
      have := Int.natAbs_dvd_natAbs.mpr hddvd
      simpa [Int.natAbs_natCast] using this
    have habs8 : (8 * n ^ 3).natAbs = 8 * n.natAbs ^ 3 := by
      rw [Int.natAbs_mul, Int.natAbs_pow]
      norm_num
    rwa [habs8] at h1
  have hden8 : x.den ∣ 8 :=
    (hcop8.dvd_mul_left).mp (by simpa [mul_comm] using hden_mul)
  have hd8 : x.den = 1 ∨ x.den = 2 ∨ x.den = 4 ∨ x.den = 8 := by
    have hle : x.den ≤ 8 := Nat.le_of_dvd (by decide) hden8
    have hpos : 0 < x.den := x.den_pos
    interval_cases x.den
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact absurd hden8 (by decide)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact absurd hden8 (by decide)
    · exact absurd hden8 (by decide)
    · exact absurd hden8 (by decide)
    · exact Or.inr (Or.inr (Or.inr rfl))
  have hnpm : n = 1 ∨ n = -1 := Int.natAbs_eq_iff.mp hn1
  have heval := gQ_eval_candidates
  rcases hnpm with hn | hn <;> rcases hd8 with hd | hd | hd | hd
  · have : x = 1 := by rw [hx, hn, show d = 1 by simp [d, hd]]; norm_num
    rw [this] at h0; exact heval.1 h0
  · have : x = (1 / 2 : ℚ) := by
      rw [hx, hn, show d = 2 by simp [d, hd]]; norm_num
    rw [this] at h0; exact heval.2.2.1 h0
  · have : x = (1 / 4 : ℚ) := by
      rw [hx, hn, show d = 4 by simp [d, hd]]; norm_num
    rw [this] at h0; exact heval.2.2.2.2.1 h0
  · have : x = (1 / 8 : ℚ) := by
      rw [hx, hn, show d = 8 by simp [d, hd]]; norm_num
    rw [this] at h0; exact heval.2.2.2.2.2.2.1 h0
  · have : x = (-1 : ℚ) := by
      rw [hx, hn, show d = 1 by simp [d, hd]]; norm_num
    rw [this] at h0; exact heval.2.1 h0
  · have : x = (-(1 / 2) : ℚ) := by
      rw [hx, hn, show d = 2 by simp [d, hd]]; norm_num
    rw [this] at h0; exact heval.2.2.2.1 h0
  · have : x = (-(1 / 4) : ℚ) := by
      rw [hx, hn, show d = 4 by simp [d, hd]]; norm_num
    rw [this] at h0; exact heval.2.2.2.2.2.1 h0
  · have : x = (-(1 / 8) : ℚ) := by
      rw [hx, hn, show d = 8 by simp [d, hd]]; norm_num
    rw [this] at h0; exact heval.2.2.2.2.2.2.2 h0

lemma gZ_ne_zero (p q : ℤ) (hq : q ≠ 0) : gZ p q ≠ 0 := by
  intro h
  have hqR : (q : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hq
  have hgR : gR (-(p : ℝ) / q) = 0 := by
    have hR : (q : ℝ) ^ 3 * gR (-(p : ℝ) / q) = 0 := by
      rw [← gZ_eq_q_pow p q hq, h, Int.cast_zero]
    exact (mul_eq_zero.mp hR).resolve_left (pow_ne_zero 3 hqR)
  have hx : (gQ ((-p : ℚ) / q) : ℝ) = gR (-(p : ℝ) / q) := by
    unfold gQ gR; push_cast; rfl
  have : gQ ((-p : ℚ) / q) = 0 := by
    have hcast : ((gQ ((-p : ℚ) / q) : ℚ) : ℝ) = 0 := by
      rw [hx, hgR]
    exact_mod_cast hcast
  exact gQ_ne_zero _ this

/-! ## |h| bound when |x − c| < 1 -/

lemma abs_hR_lt_thirty (x : ℝ) (hx : |x - cθ| < 1) :
    |hR x cθ| < 30 := by
  have hc := abs_cθ_lt_one_div_four
  have hxab : |x| < 5 / 4 := by
    have : |x| = |(x - cθ) + cθ| := by ring_nf
    rw [this]
    exact lt_of_le_of_lt (abs_add_le _ _) (by linarith)
  have hx2 : x ^ 2 < (25 / 16 : ℝ) := by
    have hmul :=
      mul_self_lt_mul_self (abs_nonneg x) (show |x| < 5 / 4 from hxab)
    have habs : |x| * |x| = x ^ 2 := by rw [← sq_abs, sq]
    have : (5 / 4 : ℝ) * (5 / 4) = 25 / 16 := by norm_num
    rw [habs, this] at hmul
    exact hmul
  have hxc : |x * cθ| < (5 / 16 : ℝ) := by
    rw [abs_mul]
    have hmul := mul_lt_mul'' hxab hc (abs_nonneg _) (abs_nonneg _)
    have hprod : (5 / 4 : ℝ) * (1 / 4) = 5 / 16 := by norm_num
    rwa [hprod] at hmul
  have hc2 : cθ ^ 2 < (1 / 16 : ℝ) := by
    have hmul := mul_self_lt_mul_self (abs_nonneg cθ) hc
    have habs : |cθ| * |cθ| = cθ ^ 2 := by rw [← sq_abs, sq]
    have : (1 / 4 : ℝ) * (1 / 4) = 1 / 16 := by norm_num
    rw [habs, this] at hmul
    exact hmul
  have htri :
      |hR x cθ| ≤
        8 * (x ^ 2 + |x * cθ| + cθ ^ 2) + 4 * (|x| + |cθ|) + 4 := by
    unfold hR
    have hA :
        |8 * (x ^ 2 + x * cθ + cθ ^ 2) + 4 * (x + cθ) + (-4)| ≤
          |8 * (x ^ 2 + x * cθ + cθ ^ 2)| + |4 * (x + cθ)| + |(-4 : ℝ)| := by
      set A := 8 * (x ^ 2 + x * cθ + cθ ^ 2)
      set B := 4 * (x + cθ)
      set C := (-4 : ℝ)
      have h1 := abs_add_le (A + B) C
      have h2 := abs_add_le A B
      linarith
    have h8 :
        |8 * (x ^ 2 + x * cθ + cθ ^ 2)| = 8 * |x ^ 2 + x * cθ + cθ ^ 2| := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 8)]
    have h4 : |4 * (x + cθ)| = 4 * |x + cθ| := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    have h4c : |(-4 : ℝ)| = 4 := by norm_num
    have hx2nn : |x ^ 2| = x ^ 2 := abs_of_nonneg (sq_nonneg x)
    have hc2nn : |cθ ^ 2| = cθ ^ 2 := abs_of_nonneg (sq_nonneg cθ)
    have hquad :
        |x ^ 2 + x * cθ + cθ ^ 2| ≤ x ^ 2 + |x * cθ| + cθ ^ 2 := by
      have h1 := abs_add_le (x ^ 2 + x * cθ) (cθ ^ 2)
      have h2 := abs_add_le (x ^ 2) (x * cθ)
      linarith [hx2nn, hc2nn]
    have hsum : |x + cθ| ≤ |x| + |cθ| := abs_add_le _ _
    have hid :
        8 * (x ^ 2 + x * cθ + cθ ^ 2) + 4 * (x + cθ) - 4 =
          8 * (x ^ 2 + x * cθ + cθ ^ 2) + 4 * (x + cθ) + (-4) := by ring
    rw [hid]
    linarith [hA, h8, h4, h4c, hquad, hsum]
  have hnum :
      8 * (x ^ 2 + |x * cθ| + cθ ^ 2) + 4 * (|x| + |cθ|) + 4 < 30 := by
    have hxlo : |x| < 5 / 4 := hxab
    have hylo : |cθ| < 1 / 4 := hc
    linarith [hx2, hxc, hc2, hxlo, hylo]
  exact lt_of_le_of_lt htri hnum

lemma abs_one_le_int {z : ℤ} (hz : z ≠ 0) : (1 : ℝ) ≤ |(z : ℝ)| := by
  have : (1 : ℤ) ≤ |z| := Int.one_le_abs hz
  have hcast : ((|z| : ℤ) : ℝ) = |(z : ℝ)| := by rw [Int.cast_abs]
  have : (1 : ℝ) ≤ ((|z| : ℤ) : ℝ) := by exact_mod_cast this
  rwa [hcast] at this

lemma abs_linform_ge_of_small (p q : ℤ) (hq : q ≠ 0)
    (hsmall : |((p : ℝ) + (q : ℝ) * cθ)| < 1) :
    1 / (30 * (q : ℝ) ^ 2) ≤ |((p : ℝ) + (q : ℝ) * cθ)| := by
  have hqR : (q : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hq
  set x0 : ℝ := -((p : ℝ) / q)
  have hdiff : x0 - cθ = -((p : ℝ) + (q : ℝ) * cθ) / q := by
    unfold x0
    field_simp [hqR]
    ring
  have hdiffabs : |x0 - cθ| = |((p : ℝ) + (q : ℝ) * cθ)| / |(q : ℝ)| := by
    rw [hdiff, abs_div, abs_neg]
  have hqabs : (1 : ℝ) ≤ |(q : ℝ)| := abs_one_le_int hq
  have hxlt : |x0 - cθ| < 1 := by
    rw [hdiffabs]
    exact (div_lt_one (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hqabs)).2
      (lt_of_lt_of_le hsmall hqabs)
  have hfact : gR x0 = (x0 - cθ) * hR x0 cθ := by
    have : gR x0 = gR x0 - gR cθ := by rw [gR_cθ_eq_zero, sub_zero]
    rw [this, gR_sub]
  have hx0form : x0 = -((p : ℝ) / q) := rfl
  have hgZ : (gZ p q : ℝ) = (q : ℝ) ^ 3 * gR x0 := by
    rw [gZ_eq_q_pow p q hq]
    congr 2
    unfold x0
    field_simp [hqR]
  have hgz0 : gZ p q ≠ 0 := gZ_ne_zero p q hq
  have habsZ : (1 : ℝ) ≤ |(gZ p q : ℝ)| := abs_one_le_int hgz0
  have hh : |hR x0 cθ| < 30 := abs_hR_lt_thirty x0 hxlt
  have hh0 : hR x0 cθ ≠ 0 := by
    intro hz
    have hg0 : gR x0 = 0 := by rw [hfact, hz, mul_zero]
    have hxQ : (gQ ((-p : ℚ) / q) : ℝ) = gR x0 := by
      unfold gQ gR x0; push_cast; field_simp [hqR]
    have : gQ ((-p : ℚ) / q) = 0 := by
      have hcast : ((gQ ((-p : ℚ) / q) : ℚ) : ℝ) = 0 := by
        rw [hxQ, hg0]
      exact_mod_cast hcast
    exact gQ_ne_zero _ this
  have hprod : |gR x0| = |x0 - cθ| * |hR x0 cθ| := by
    rw [hfact, abs_mul]
  have hgRabs : |(q : ℝ) ^ 3| * |gR x0| = |(gZ p q : ℝ)| := by
    have habs := congrArg abs hgZ
    rw [abs_mul] at habs
    exact habs.symm
  have hq3 : |(q : ℝ) ^ 3| = |(q : ℝ)| ^ 3 := abs_pow _ _
  have hfinal :
      |((p : ℝ) + (q : ℝ) * cθ)| =
        |(gZ p q : ℝ)| / (|(q : ℝ)| ^ 2 * |hR x0 cθ|) := by
    have hxeq : |((p : ℝ) + (q : ℝ) * cθ)| = |(q : ℝ)| * |x0 - cθ| := by
      have hne : |(q : ℝ)| ≠ 0 := abs_ne_zero.mpr hqR
      rw [hdiffabs, mul_div_cancel₀ _ hne]
    have hge : |x0 - cθ| = |gR x0| / |hR x0 cθ| := by
      have hne : |hR x0 cθ| ≠ 0 := abs_ne_zero.mpr hh0
      rw [hprod]
      field_simp [hne]
    have hgR' : |gR x0| = |(gZ p q : ℝ)| / |(q : ℝ) ^ 3| := by
      have hne : |(q : ℝ) ^ 3| ≠ 0 := by simp [hqR]
      exact eq_div_of_mul_eq hne (by rw [mul_comm]; exact hgRabs)
    rw [hxeq, hge, hgR', hq3]
    have hne1 : |hR x0 cθ| ≠ 0 := abs_ne_zero.mpr hh0
    have hne2 : |(q : ℝ)| ≠ 0 := abs_ne_zero.mpr hqR
    field_simp [hne1, hne2]
  rw [hfinal]
  have hdenpos : 0 < |(q : ℝ)| ^ 2 * |hR x0 cθ| := by
    have : 0 < |hR x0 cθ| := abs_pos.mpr hh0
    positivity
  have hcmp : |(q : ℝ)| ^ 2 * |hR x0 cθ| ≤ 30 * (q : ℝ) ^ 2 := by
    have hsq : (q : ℝ) ^ 2 = |(q : ℝ)| ^ 2 := (sq_abs (q : ℝ)).symm
    rw [hsq]
    nlinarith [le_of_lt hh, sq_nonneg |(q : ℝ)|]
  have hnumpos : 0 < 30 * (q : ℝ) ^ 2 := by
    have : (q : ℝ) ≠ 0 := hqR
    positivity
  refine (div_le_div_iff₀ hnumpos hdenpos).mpr ?_
  nlinarith [habsZ, hcmp, sq_nonneg |(q : ℝ)|]

/-! ## Structure-factor norm vs the phase sum -/

lemma norm_structureFactor_eq {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ) :
    ‖structureFactor (fun k => centroidPoint (n k) (s k)) q220‖ =
      ‖(∑ k : Fin N,
          exp (2 * Real.pi * I * dot3 q220 (centroidPoint (n k) (s k))))‖ /
        (N : ℝ) := by
  unfold structureFactor
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  field_simp

lemma c0_div_N3_le_half_div_N {N : ℕ} (hN : 1 ≤ N) :
    c0 / (N : ℝ) ^ 3 ≤ (1 : ℝ) / (2 * N) := by
  unfold c0
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hN2 : (1 : ℝ) ≤ (N : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  have hpos1 : (0 : ℝ) < 30 * N ^ 3 := by positivity
  have hpos2 : (0 : ℝ) < 2 * N := by positivity
  have heq : (1 / 30 : ℝ) / N ^ 3 = 1 / (30 * N ^ 3) := by field_simp
  rw [heq]
  exact (one_div_le_one_div hpos1 hpos2).mpr (by nlinarith [hN2, hNpos])

lemma c0_div_N3_le_one_div_N {N : ℕ} (hN : 1 ≤ N) :
    c0 / (N : ℝ) ^ 3 ≤ (1 : ℝ) / N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hhalf := c0_div_N3_le_half_div_N hN
  have : (1 : ℝ) / (2 * N) ≤ 1 / N := by
    rw [one_div_le_one_div (by positivity) hNpos]
    linarith [hNpos]
  exact le_trans hhalf this

lemma c0_div_N3_le_one {N : ℕ} (hN : 1 ≤ N) :
    c0 / (N : ℝ) ^ 3 ≤ 1 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  exact le_trans (c0_div_N3_le_one_div_N hN) (div_le_one_of_le₀
    (by exact_mod_cast hN : (1 : ℝ) ≤ N) hNpos.le)

/-! ## Main lower bound -/

/-- `[P, Lean]` Explicit bound `‖F(q₂₂₀)‖ ≥ (1/30) / N³`. -/
theorem norm_structureFactor_ge_c0_div_N_pow_three {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    c0 / (N : ℝ) ^ 3 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) q220‖ := by
  set a := countT s 0
  set b := countT s 4
  set b' := countT s (-4)
  have hcard : a + b + b' = N := countT_add_eq_card s hs
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  set S := (∑ k : Fin N,
      exp (2 * Real.pi * I * dot3 q220 (centroidPoint (n k) (s k))))
  have hnormF := norm_structureFactor_eq hN n s
  have hre : S.re = (a : ℝ) + ((b : ℝ) + (b' : ℝ)) * cθ := by
    change (∑ k : Fin N,
        exp (2 * Real.pi * I * dot3 q220 (centroidPoint (n k) (s k)))).re = _
    rw [re_sum_eq n s hs]
    unfold cθ a b b'
    rfl
  have him : S.im = ((b' : ℝ) - (b : ℝ)) * sθ := by
    change (∑ k : Fin N,
        exp (2 * Real.pi * I * dot3 q220 (centroidPoint (n k) (s k)))).im = _
    rw [im_sum_eq n s hs]
    unfold sθ b b'
    rfl
  by_cases hbb : b = b'
  · have him0 : S.im = 0 := by
      rw [him, hbb, sub_self, zero_mul]
    have hre' : S.re = (a : ℝ) + (2 * (b : ℝ)) * cθ := by
      rw [hre, hbb]; ring
    have hS : S = ↑((a : ℝ) + (2 * (b : ℝ)) * cθ) := by
      apply Complex.ext
      · simp [hre']
      · simp [him0]
    have hNF : ‖S‖ = |((a : ℝ) + (2 * (b : ℝ)) * cθ)| := by
      rw [hS, Complex.norm_real, Real.norm_eq_abs]
    rw [hnormF, hNF]
    set p : ℤ := (a : ℤ)
    set q : ℤ := 2 * (b : ℤ)
    have hpq : ((a : ℝ) + (2 * (b : ℝ)) * cθ) = ((p : ℝ) + (q : ℝ) * cθ) := by
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
    · have haN : a = N := by
        omega
      have : |((a : ℝ) + (2 * (b : ℝ)) * cθ)| = (N : ℝ) := by
        simp [hb0, haN]
      rw [this, div_self (ne_of_gt hNpos)]
      exact c0_div_N3_le_one hN
    · have hqne : q ≠ 0 := by
        unfold q
        have : (b : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hb0
        omega
      rw [hpq]
      by_cases hge1 : 1 ≤ |((p : ℝ) + (q : ℝ) * cθ)|
      · have : 1 / (N : ℝ) ≤ |((p : ℝ) + (q : ℝ) * cθ)| / N :=
          div_le_div_of_nonneg_right hge1 hNpos.le
        exact le_trans (c0_div_N3_le_one_div_N hN) this
      · have hsmall : |((p : ℝ) + (q : ℝ) * cθ)| < 1 := lt_of_not_ge hge1
        have hlb := abs_linform_ge_of_small p q hqne hsmall
        have hstep :
            1 / (30 * (q : ℝ) ^ 2) / N ≤ |((p : ℝ) + (q : ℝ) * cθ)| / N :=
          div_le_div_of_nonneg_right hlb hNpos.le
        have hq2 : (q : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := by
          have h1 : (q : ℝ) ^ 2 = |(q : ℝ)| ^ 2 := (sq_abs (q : ℝ)).symm
          rw [h1]
          exact pow_le_pow_left₀ (abs_nonneg (q : ℝ)) hqN 2
        have hcmp : c0 / (N : ℝ) ^ 3 ≤ 1 / (30 * (q : ℝ) ^ 2) / N := by
          unfold c0
          have hL : (1 / 30 : ℝ) / N ^ 3 = 1 / (30 * N ^ 3) := by field_simp
          have hR : (1 : ℝ) / (30 * (q : ℝ) ^ 2) / N =
              1 / (30 * (q : ℝ) ^ 2 * N) := by field_simp
          rw [hL, hR]
          have hpos1 : (0 : ℝ) < 30 * N ^ 3 := by positivity
          have hpos2 : (0 : ℝ) < 30 * (q : ℝ) ^ 2 * N := by
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
    have himabs : (1 / 2 : ℝ) ≤ |S.im| := by
      rw [him, abs_mul, abs_of_pos (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2)
        sin_four_pi_div_seven_ge_half)]
      have hspos : 0 < sθ := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2)
        sin_four_pi_div_seven_ge_half
      nlinarith [sin_four_pi_div_seven_ge_half, hdiff]
    have hSbound : (1 / 2 : ℝ) ≤ ‖S‖ :=
      le_trans himabs (Complex.abs_im_le_norm S)
    have hle : (1 : ℝ) / (2 * N) ≤ ‖S‖ / N := by
      have hhalf : (1 / 2 : ℝ) / N = 1 / (2 * N) := by field_simp
      rw [← hhalf]
      exact div_le_div_of_nonneg_right hSbound hNpos.le
    have hgoal : c0 / (N : ℝ) ^ 3 ≤ ‖S‖ / N :=
      le_trans (c0_div_N3_le_half_div_N hN) hle
    rw [hnormF]
    change c0 / (N : ℝ) ^ 3 ≤ ‖S‖ / N
    exact hgoal

/-- `|F|² ≥ c0² / N⁶`. -/
theorem normSq_structureFactor_ge_c0_sq_div_N_pow_six {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    c0 ^ 2 / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) q220‖ ^ 2 := by
  have h := norm_structureFactor_ge_c0_div_N_pow_three hN n s hs
  have hc0 : 0 ≤ c0 / (N : ℝ) ^ 3 := div_nonneg c0_pos.le (by positivity)
  have := pow_le_pow_left₀ hc0 h (n := 2)
  convert this using 1
  ring

#print axioms sin_four_pi_div_seven_ge_half
#print axioms gR_cθ_eq_zero
#print axioms gQ_ne_zero
#print axioms gZ_ne_zero
#print axioms abs_linform_ge_of_small
#print axioms norm_structureFactor_ge_c0_div_N_pow_three
#print axioms normSq_structureFactor_ge_c0_sq_div_N_pow_six

end LeanLab.Scratch.LemmaDLowerBound220
