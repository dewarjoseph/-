import LeanLab.Scratch.LemmaAInt
import LeanLab.Scratch.LemmaD4
import LeanLab.Scratch.LemmaDLink
import LeanLab.Scratch.LemmaDIntVec
import Mathlib.NumberTheory.Niven

/-!
# Chair44 D-form: no equal-weight zero at q = (2,2,0)
(public-screen)

Public-screen v2 copy of LeanLab.Scratch.LemmaDNoZero220 (official pin src
`d95476a191c502b8193bab35af9a00616169eedf85f410a4eb0528be4f579e2c`).
Header redacted; theorem bodies are unchanged. This copy is not a
replacement pin.

At the integer wavevector `q = (2,2,0)`, every
finite nonempty equal-weight D-form box has structure factor `F(q) ≠ 0`.

**Setup.** Points `r_k = n_k − s_k/14` with `n_k ∈ ℤ³`, `s_k ∈ {±1}³`, equal
weights. At integer `q` the lattice part drops and
`exp(2πi q·r_k) = exp(−iπ t_k/7)` with `t_k = q·s_k`. For `q = (2,2,0)` one has
`t_k = 2(s₀+s₁) ∈ {4,0,−4}`, so each summand is one of
`1`, `cos θ − i sin θ`, `cos θ + i sin θ` where `θ = 4π/7`.

**Argument [P, Lean].** Write `a,b,c'` for the counts of `t ∈ {0,4,−4}`
(`a+b+c' = N ≥ 1`). Then
`N·F = (a + (b+c') cos θ) + i (c'−b) sin θ`.
`sin θ > 0`, so `F = 0` forces `b = c'` and then `a + 2 b cos θ = 0`.
* If `b = 0` then `a = N ≥ 1`, so the real part is nonzero.
* If `b ≥ 1` then `cos θ = −a/(2b) ∈ ℚ`, contradicting Niven
  (`irrational_cos_rat_mul_pi` at `r = 4/7`, denominator `7 > 3`).

Also the equal-weight M-box average of intensities is strictly positive
(each term is).

**Not proved / out of scope:**
* No uniform positive lower bound on `|F|²`: rational approximations
  `a/(2b) ≈ −cos θ` make `|F|` arbitrarily small, so
  `inf {|F|² : nonempty equal-weight D-form boxes} = 0` is expected but
  **not** formalized here (`[X]/[E]` remark only).
* Nothing off-axis; nothing for other `‖q‖₁ = 4` vectors.
* D-form hypothesis class only (not the real 13/14 geometry).
* Scratch; not a Lake target; not peer reviewed.

This file is source-only and is not a Lake package. It claims nothing
beyond the theorems stated below.

Dated 2026-11-10.
-/

namespace LeanLab.Scratch.LemmaDNoZero220

open Complex Finset
open LeanLab.Scratch.LemmaD4 (dot3 structureFactor centroidPoint)
open LeanLab.Scratch.LemmaDIntVec (qReal signedWeight exp_centroid_int_q)

/-! ## The wavevector q = (2, 2, 0) -/

def qZ220 : Fin 3 → ℤ
  | ⟨0, _⟩ => 2
  | ⟨1, _⟩ => 2
  | ⟨2, _⟩ => 0

noncomputable def q220 : Fin 3 → ℝ := qReal qZ220

/-! ## Signed weights land in {4, 0, −4} -/

lemma signedWeight_qZ220_mem (s : Fin 3 → ℤ) (hs : ∀ j, s j = 1 ∨ s j = -1) :
    signedWeight qZ220 s = 4 ∨ signedWeight qZ220 s = 0 ∨
      signedWeight qZ220 s = -4 := by
  have h0 := hs 0
  have h1 := hs 1
  simp only [signedWeight, qZ220, Fin.sum_univ_three, mul_zero, add_zero]
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> simp [h0, h1]

/-! ## Phase closed forms -/

lemma exp_centroid_at_t4 (n s : Fin 3 → ℤ)
    (ht : signedWeight qZ220 s = 4) :
    exp (2 * Real.pi * I * dot3 q220 (centroidPoint n s)) =
      (↑(Real.cos (4 * Real.pi / 7)) : ℂ) -
        I * ↑(Real.sin (4 * Real.pi / 7)) := by
  rw [show q220 = qReal qZ220 from rfl, exp_centroid_int_q, ht]
  have hθ : (-(Real.pi * ((4 : ℤ) : ℝ) / 7) : ℝ) = -(4 * Real.pi / 7) := by
    push_cast; ring
  rw [hθ, Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
  push_cast
  ring

lemma exp_centroid_at_t0 (n s : Fin 3 → ℤ)
    (ht : signedWeight qZ220 s = 0) :
    exp (2 * Real.pi * I * dot3 q220 (centroidPoint n s)) = 1 := by
  rw [show q220 = qReal qZ220 from rfl, exp_centroid_int_q, ht]
  simp

lemma exp_centroid_at_tneg4 (n s : Fin 3 → ℤ)
    (ht : signedWeight qZ220 s = -4) :
    exp (2 * Real.pi * I * dot3 q220 (centroidPoint n s)) =
      (↑(Real.cos (4 * Real.pi / 7)) : ℂ) +
        I * ↑(Real.sin (4 * Real.pi / 7)) := by
  rw [show q220 = qReal qZ220 from rfl, exp_centroid_int_q, ht]
  have hθ : (-(Real.pi * ((-4 : ℤ) : ℝ) / 7) : ℝ) = 4 * Real.pi / 7 := by
    push_cast; ring
  rw [hθ, Complex.exp_ofReal_mul_I]
  push_cast
  ring

/-! ## Trigonometric facts at θ = 4π/7 -/

lemma sin_four_pi_div_seven_pos : 0 < Real.sin (4 * Real.pi / 7) := by
  have hgt : 0 < 4 * Real.pi / 7 := by positivity
  have hlt : 4 * Real.pi / 7 < Real.pi := by
    have : (4 : ℝ) / 7 < 1 := by norm_num
    calc
      4 * Real.pi / 7 = ((4 : ℝ) / 7) * Real.pi := by ring
      _ < 1 * Real.pi := mul_lt_mul_of_pos_right this Real.pi_pos
      _ = Real.pi := one_mul _
  exact Real.sin_pos_of_mem_Ioo ⟨hgt, hlt⟩

lemma sin_four_pi_div_seven_ne_zero : Real.sin (4 * Real.pi / 7) ≠ 0 :=
  ne_of_gt sin_four_pi_div_seven_pos

/-- `[P, Lean]` standalone: `cos(4π/7)` is irrational (Niven, den 7 > 3). -/
theorem cos_four_pi_div_seven_irrational :
    Irrational (Real.cos (4 * Real.pi / 7)) := by
  have h : Real.cos (4 * Real.pi / 7) =
      Real.cos (((4 : ℚ) / 7 : ℝ) * Real.pi) := by
    push_cast; ring
  rw [h]
  have hr : (3 : ℕ) < ((4 : ℚ) / 7).den := by
    have : ((4 : ℚ) / 7).den = 7 := by norm_num
    rw [this]; norm_num
  simpa using irrational_cos_rat_mul_pi (r := (4 : ℚ) / 7) hr

/-! ## Counts of the three phase classes -/

noncomputable def countT {N : ℕ} (s : Fin N → Fin 3 → ℤ) (t : ℤ) : ℕ :=
  #{k : Fin N | signedWeight qZ220 (s k) = t}

lemma countT_add_eq_card {N : ℕ} (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    countT s 0 + countT s 4 + countT s (-4) = N := by
  classical
  set S0 : Finset (Fin N) := {k | signedWeight qZ220 (s k) = 0}
  set S4 : Finset (Fin N) := {k | signedWeight qZ220 (s k) = 4}
  set Sm : Finset (Fin N) := {k | signedWeight qZ220 (s k) = -4}
  have hdisj01 : Disjoint S0 S4 := by
    refine disjoint_left.mpr ?_
    intro x hx0 hx4
    simp only [S0, S4, mem_filter, mem_univ, true_and] at hx0 hx4
    exact absurd hx4 (by omega)
  have hdisj02 : Disjoint S0 Sm := by
    refine disjoint_left.mpr ?_
    intro x hx0 hxm
    simp only [S0, Sm, mem_filter, mem_univ, true_and] at hx0 hxm
    exact absurd hxm (by omega)
  have hdisj12 : Disjoint S4 Sm := by
    refine disjoint_left.mpr ?_
    intro x hx4 hxm
    simp only [S4, Sm, mem_filter, mem_univ, true_and] at hx4 hxm
    exact absurd hxm (by omega)
  have hcover : S0 ∪ S4 ∪ Sm = univ := by
    ext k
    constructor
    · intro; exact mem_univ _
    · intro _
      simp only [S0, S4, Sm, mem_union, mem_filter, mem_univ, true_and]
      rcases signedWeight_qZ220_mem (s k) (hs k) with h | h | h <;> simp [h]
  have hcard : (S0 ∪ S4 ∪ Sm).card = N := by
    rw [hcover, card_univ, Fintype.card_fin]
  have hdisj_left : Disjoint (S0 ∪ S4) Sm :=
    Disjoint.sup_left hdisj02 hdisj12
  rw [card_union_of_disjoint hdisj_left, card_union_of_disjoint hdisj01] at hcard
  simpa [countT, S0, S4, Sm] using hcard

/-! ## Sum of phases via counts -/

lemma sum_exp_eq_counts {N : ℕ}
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (∑ k : Fin N,
        exp (2 * Real.pi * I * dot3 q220 (centroidPoint (n k) (s k)))) =
      (countT s 0 : ℂ) +
        (countT s 4 : ℂ) *
          ((↑(Real.cos (4 * Real.pi / 7)) : ℂ) -
            I * ↑(Real.sin (4 * Real.pi / 7))) +
        (countT s (-4) : ℂ) *
          ((↑(Real.cos (4 * Real.pi / 7)) : ℂ) +
            I * ↑(Real.sin (4 * Real.pi / 7))) := by
  classical
  set S0 : Finset (Fin N) := {k | signedWeight qZ220 (s k) = 0}
  set S4 : Finset (Fin N) := {k | signedWeight qZ220 (s k) = 4}
  set Sm : Finset (Fin N) := {k | signedWeight qZ220 (s k) = -4}
  have hdisj01 : Disjoint S0 S4 := by
    refine disjoint_left.mpr ?_
    intro x hx0 hx4
    simp only [S0, S4, mem_filter, mem_univ, true_and] at hx0 hx4
    exact absurd hx4 (by omega)
  have hdisj02 : Disjoint S0 Sm := by
    refine disjoint_left.mpr ?_
    intro x hx0 hxm
    simp only [S0, Sm, mem_filter, mem_univ, true_and] at hx0 hxm
    exact absurd hxm (by omega)
  have hdisj12 : Disjoint S4 Sm := by
    refine disjoint_left.mpr ?_
    intro x hx4 hxm
    simp only [S4, Sm, mem_filter, mem_univ, true_and] at hx4 hxm
    exact absurd hxm (by omega)
  have hcover : S0 ∪ S4 ∪ Sm = univ := by
    ext k
    constructor
    · intro; exact mem_univ _
    · intro _
      simp only [S0, S4, Sm, mem_union, mem_filter, mem_univ, true_and]
      rcases signedWeight_qZ220_mem (s k) (hs k) with h | h | h <;> simp [h]
  have hdisj_left : Disjoint (S0 ∪ S4) Sm :=
    Disjoint.sup_left hdisj02 hdisj12
  have hsum :
      (∑ k : Fin N,
          exp (2 * Real.pi * I * dot3 q220 (centroidPoint (n k) (s k)))) =
        (∑ k ∈ S0,
            exp (2 * Real.pi * I * dot3 q220 (centroidPoint (n k) (s k)))) +
          (∑ k ∈ S4,
              exp (2 * Real.pi * I * dot3 q220 (centroidPoint (n k) (s k)))) +
            (∑ k ∈ Sm,
                exp (2 * Real.pi * I * dot3 q220 (centroidPoint (n k) (s k)))) := by
    calc
      (∑ k : Fin N,
            exp (2 * Real.pi * I * dot3 q220 (centroidPoint (n k) (s k))))
          = ∑ k ∈ univ,
              exp (2 * Real.pi * I * dot3 q220 (centroidPoint (n k) (s k))) := rfl
      _ = ∑ k ∈ S0 ∪ S4 ∪ Sm,
              exp (2 * Real.pi * I * dot3 q220 (centroidPoint (n k) (s k))) := by
                rw [hcover]
      _ = ∑ k ∈ S0 ∪ S4,
              exp (2 * Real.pi * I * dot3 q220 (centroidPoint (n k) (s k))) +
            ∑ k ∈ Sm,
              exp (2 * Real.pi * I * dot3 q220 (centroidPoint (n k) (s k))) :=
            sum_union hdisj_left
      _ = (∑ k ∈ S0,
              exp (2 * Real.pi * I * dot3 q220 (centroidPoint (n k) (s k))) +
            ∑ k ∈ S4,
              exp (2 * Real.pi * I * dot3 q220 (centroidPoint (n k) (s k)))) +
            ∑ k ∈ Sm,
              exp (2 * Real.pi * I * dot3 q220 (centroidPoint (n k) (s k))) := by
            rw [sum_union hdisj01]
      _ = _ := by abel
  have h0 : ∀ k ∈ S0,
      exp (2 * Real.pi * I * dot3 q220 (centroidPoint (n k) (s k))) = 1 := by
    intro k hk; simp only [S0, mem_filter, mem_univ, true_and] at hk
    exact exp_centroid_at_t0 (n k) (s k) hk
  have h4 : ∀ k ∈ S4,
      exp (2 * Real.pi * I * dot3 q220 (centroidPoint (n k) (s k))) =
        (↑(Real.cos (4 * Real.pi / 7)) : ℂ) -
          I * ↑(Real.sin (4 * Real.pi / 7)) := by
    intro k hk; simp only [S4, mem_filter, mem_univ, true_and] at hk
    exact exp_centroid_at_t4 (n k) (s k) hk
  have hm : ∀ k ∈ Sm,
      exp (2 * Real.pi * I * dot3 q220 (centroidPoint (n k) (s k))) =
        (↑(Real.cos (4 * Real.pi / 7)) : ℂ) +
          I * ↑(Real.sin (4 * Real.pi / 7)) := by
    intro k hk; simp only [Sm, mem_filter, mem_univ, true_and] at hk
    exact exp_centroid_at_tneg4 (n k) (s k) hk
  rw [hsum, sum_congr rfl h0, sum_congr rfl h4, sum_congr rfl hm]
  simp only [sum_const, nsmul_eq_mul, mul_one]
  simp only [countT, S0, S4, Sm]

lemma re_of_cos_sub_I_sin (c σ : ℝ) :
    (((c : ℂ) - I * (σ : ℂ))).re = c := by
  rw [sub_re, mul_re, I_re, I_im]
  simp [ofReal_re, ofReal_im]

lemma im_of_cos_sub_I_sin (c σ : ℝ) :
    (((c : ℂ) - I * (σ : ℂ))).im = -σ := by
  rw [sub_im, mul_im, I_re, I_im]
  simp [ofReal_re, ofReal_im]

lemma re_of_cos_add_I_sin (c σ : ℝ) :
    (((c : ℂ) + I * (σ : ℂ))).re = c := by
  rw [add_re, mul_re, I_re, I_im]
  simp [ofReal_re, ofReal_im]

lemma im_of_cos_add_I_sin (c σ : ℝ) :
    (((c : ℂ) + I * (σ : ℂ))).im = σ := by
  rw [add_im, mul_im, I_re, I_im]
  simp [ofReal_re, ofReal_im]

lemma re_sum_eq {N : ℕ}
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (∑ k : Fin N,
        exp (2 * Real.pi * I * dot3 q220 (centroidPoint (n k) (s k)))).re =
      (countT s 0 : ℝ) +
        ((countT s 4 : ℝ) + (countT s (-4) : ℝ)) *
          Real.cos (4 * Real.pi / 7) := by
  rw [sum_exp_eq_counts n s hs]
  set c := Real.cos (4 * Real.pi / 7)
  set σ := Real.sin (4 * Real.pi / 7)
  have hpos := re_of_cos_sub_I_sin c σ
  have hneg := re_of_cos_add_I_sin c σ
  have hipos := im_of_cos_sub_I_sin c σ
  have hineg := im_of_cos_add_I_sin c σ
  -- Expand (a + b * zpos + cp * zneg).re with a,b,cp nat casts
  rw [add_re, add_re, mul_re, mul_re]
  simp only [ofReal_re, ofReal_im, natCast_re, natCast_im, hpos, hneg, hipos, hineg]
  ring

lemma im_sum_eq {N : ℕ}
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (∑ k : Fin N,
        exp (2 * Real.pi * I * dot3 q220 (centroidPoint (n k) (s k)))).im =
      ((countT s (-4) : ℝ) - (countT s 4 : ℝ)) *
        Real.sin (4 * Real.pi / 7) := by
  rw [sum_exp_eq_counts n s hs]
  set c := Real.cos (4 * Real.pi / 7)
  set σ := Real.sin (4 * Real.pi / 7)
  have hpos := re_of_cos_sub_I_sin c σ
  have hneg := re_of_cos_add_I_sin c σ
  have hipos := im_of_cos_sub_I_sin c σ
  have hineg := im_of_cos_add_I_sin c σ
  rw [add_im, add_im, mul_im, mul_im]
  simp only [ofReal_re, ofReal_im, natCast_re, natCast_im, hpos, hneg, hipos, hineg]
  ring

/-! ## Main non-vanishing -/

lemma sum_eq_zero_of_structureFactor_eq_zero {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hF : structureFactor (fun k => centroidPoint (n k) (s k)) q220 = 0) :
    (∑ k : Fin N,
        exp (2 * Real.pi * I * dot3 q220 (centroidPoint (n k) (s k)))) = 0 := by
  unfold structureFactor at hF
  have hNne : (N : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (Nat.zero_lt_of_lt hN))
  have h := congr_arg (fun z : ℂ => (N : ℂ) * z) hF
  simp only [mul_zero] at h
  rwa [mul_inv_cancel_left₀ hNne] at h

lemma counts_eq_of_sum_eq_zero {N : ℕ}
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1)
    (hsum : (∑ k : Fin N,
        exp (2 * Real.pi * I * dot3 q220 (centroidPoint (n k) (s k)))) = 0) :
    countT s 4 = countT s (-4) ∧
      (countT s 0 : ℝ) +
          (2 * (countT s 4 : ℝ)) * Real.cos (4 * Real.pi / 7) = 0 := by
  have him := congr_arg Complex.im hsum
  have hre := congr_arg Complex.re hsum
  rw [im_sum_eq n s hs, zero_im] at him
  rw [re_sum_eq n s hs, zero_re] at hre
  have hdiff :
      (countT s (-4) : ℝ) - (countT s 4 : ℝ) = 0 :=
    (mul_eq_zero.mp him).resolve_right sin_four_pi_div_seven_ne_zero
  have hbc : countT s 4 = countT s (-4) := by
    have : (countT s 4 : ℝ) = (countT s (-4) : ℝ) := by linarith [hdiff]
    exact_mod_cast this
  refine ⟨hbc, ?_⟩
  calc
    (countT s 0 : ℝ) + (2 * (countT s 4 : ℝ)) * Real.cos (4 * Real.pi / 7)
        = (countT s 0 : ℝ) +
            ((countT s 4 : ℝ) + (countT s (-4) : ℝ)) *
              Real.cos (4 * Real.pi / 7) := by
              rw [hbc]; ring
    _ = 0 := hre

/-- `[P, Lean]` No finite nonempty equal-weight D-form box has `F = 0` at
`q = (2,2,0)`. -/
theorem structureFactor_ne_zero_at_220 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    structureFactor (fun k => centroidPoint (n k) (s k)) q220 ≠ 0 := by
  intro hF
  have hsum := sum_eq_zero_of_structureFactor_eq_zero hN n s hF
  obtain ⟨hbc, hre⟩ := counts_eq_of_sum_eq_zero n s hs hsum
  have hcard := countT_add_eq_card s hs
  have habN : countT s 0 + 2 * countT s 4 = N := by omega
  have hb_cases : countT s 4 = 0 ∨ 1 ≤ countT s 4 := by omega
  rcases hb_cases with hb0 | hbpos
  · have ha : countT s 0 = N := by omega
    have ha_pos : (0 : ℝ) < (countT s 0 : ℝ) := by
      exact_mod_cast (Nat.zero_lt_of_lt (ha ▸ hN))
    rw [hb0, Nat.cast_zero, mul_zero, zero_mul, add_zero] at hre
    exact absurd hre (ne_of_gt ha_pos)
  · have hbne : (countT s 4 : ℝ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (Nat.zero_lt_of_lt hbpos))
    have h2b : (2 : ℝ) * (countT s 4 : ℝ) ≠ 0 :=
      mul_ne_zero (by norm_num) hbne
    have hcos :
        Real.cos (4 * Real.pi / 7) =
          - (countT s 0 : ℝ) / (2 * (countT s 4 : ℝ)) := by
      have := hre
      field_simp [h2b] at this ⊢
      linarith
    have hrational :
        Real.cos (4 * Real.pi / 7) ∈ Set.range ((↑) : ℚ → ℝ) := by
      refine ⟨(-(countT s 0 : ℚ) / (2 * (countT s 4 : ℚ))), ?_⟩
      rw [hcos]
      push_cast
      rfl
    exact cos_four_pi_div_seven_irrational hrational

/-- Same statement with the integer vector written as `qZ220`. -/
theorem structureFactor_ne_zero_at_qZ220 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    structureFactor (fun k => centroidPoint (n k) (s k)) (qReal qZ220) ≠ 0 :=
  structureFactor_ne_zero_at_220 hN n s hs

/-- Intensity form: `|F|² ≠ 0` at `q = (2,2,0)`. -/
theorem normSq_structureFactor_ne_zero_at_220 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    ‖structureFactor (fun k => centroidPoint (n k) (s k)) q220‖ ^ 2 ≠ 0 := by
  intro hz
  have : structureFactor (fun k => centroidPoint (n k) (s k)) q220 = 0 :=
    norm_eq_zero.mp (sq_eq_zero_iff.mp hz)
  exact structureFactor_ne_zero_at_220 hN n s hs this

/-- Intensity is strictly positive. -/
theorem normSq_structureFactor_pos_at_220 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    0 < ‖structureFactor (fun k => centroidPoint (n k) (s k)) q220‖ ^ 2 :=
  lt_of_le_of_ne (sq_nonneg _)
    (normSq_structureFactor_ne_zero_at_220 hN n s hs).symm

/-- `[P, Lean]` Equal-weight average of intensities over M≥1 boxes is > 0
at `q = (2,2,0)`. -/
theorem avg_normSq_pos_at_220 {M : ℕ} (hM : 1 ≤ M)
    (N : Fin M → ℕ) (hN : ∀ B, 1 ≤ N B)
    (n : (B : Fin M) → Fin (N B) → Fin 3 → ℤ)
    (s : (B : Fin M) → Fin (N B) → Fin 3 → ℤ)
    (hs : ∀ B k j, s B k j = 1 ∨ s B k j = -1) :
    0 <
      (M : ℝ)⁻¹ * ∑ B : Fin M,
        ‖structureFactor (fun k => centroidPoint (n B k) (s B k)) q220‖ ^ 2 := by
  have hterm : ∀ B,
      0 < ‖structureFactor (fun k => centroidPoint (n B k) (s B k)) q220‖ ^ 2 :=
    fun B => normSq_structureFactor_pos_at_220 (hN B) (n B) (s B) (hs B)
  have hsum :
      0 < ∑ B : Fin M,
        ‖structureFactor (fun k => centroidPoint (n B k) (s B k)) q220‖ ^ 2 :=
    sum_pos (fun B _ => hterm B) (univ_nonempty_iff.mpr ⟨⟨0, Nat.zero_lt_of_lt hM⟩⟩)
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hM)
  exact mul_pos (inv_pos.mpr hMpos) hsum

#print axioms cos_four_pi_div_seven_irrational
#print axioms structureFactor_ne_zero_at_220
#print axioms structureFactor_ne_zero_at_qZ220
#print axioms normSq_structureFactor_ne_zero_at_220
#print axioms normSq_structureFactor_pos_at_220
#print axioms avg_normSq_pos_at_220

end LeanLab.Scratch.LemmaDNoZero220
