import LeanLab.Scratch.LemmaDLowerBound220
import LeanLab.Scratch.LemmaDLowerBound330
import LeanLab.Scratch.LemmaDLowerBound330Sharper
import LeanLab.Scratch.LemmaDL1SevenClassification
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Cubic N⁻³ lower bounds at (1,1,0), (6,1,0), (5,2,0), (4,3,0)
(public-screen)

Public-screen v2 copy of LeanLab.Scratch.LemmaDLowerBoundL1SevenCubic (official pin src
`290a95355a66d676ca23aab4a0ef7fcda567362a97c6a85bb97c4bd3a494c6fd`).
Header redacted; theorem bodies are unchanged. This copy is not a
replacement pin.

**[P, Lean]** For each of the four remaining one-conjugate-pair
representatives with `‖q‖₁ ≤ 7`, every nonempty finite equal-weight
D-form box satisfies `‖F‖ ≥ c0 / N³` with an explicit rational `c0`:

* `(1,1,0)`: phases `1`, `cis(±2π/7)`; cosine `cos(2π/7)` (a root of
  `g(x) = 8x³+4x²−4x−1`); `|h| < 38` on `|x − c| < 1`; `c0 = 1/38`.
* `(6,1,0)`: phases `−1`, `cis(±5π/7)`; reduces to the same cosine
  `cos(2π/7)` (since `cos(5π/7) = −cos(2π/7)`); same `H = 38`,
  `c0 = 1/38`.
* `(5,2,0)`: phases `−1`, `cis(±3π/7)`; reduces to `cos(4π/7)`
  (LemmaDLowerBound220); `H = 30`, `c0 = 1/30`.
* `(4,3,0)`: phases `−1`, `cis(±π/7)`; reduces to `cos(6π/7)`
  (LemmaDLowerBound330 / 330Sharper); `H = 34`, `c0 = 1/34`.

The argument is the same cubic route as at `(2,2,0)` and `(3,3,0)`:
signed-weight counts, `N·F = p + q c` when the two conjugate counts
agree, and `|p+q c| ≥ 1/(|q|² H)` from `g(x)−g(c)=(x−c)h(x,c)` and
a nonzero integer value of `q³ g(−p/q)`. Full-orbit transfer is not
formalized here (optional; the representatives are proved). The
exponent 3 is what the method gives, not claimed sharp. Infima stay
`[X]`.

D-form class only. Scratch; not a Lake target; not peer reviewed.

Dated 2026-11-09. No obstacles: all four orbits go through.

This file is source-only and is not a Lake package. It claims nothing
beyond the theorems stated below.

Dated 2026-11-10.
-/

namespace LeanLab.Scratch.LemmaDLowerBoundL1SevenCubic

open Complex Finset
open LeanLab.Scratch.LemmaD4 (dot3 structureFactor centroidPoint exp_two_pi_I_int)
open LeanLab.Scratch.LemmaDIntVec
  (qReal signedWeight zeta7 zeta7_pow isPrimitiveRoot_zeta7 exp_centroid_int_q)
open LeanLab.Scratch.LemmaDL1SevenClassification (qOf)
open LeanLab.Scratch.LemmaDLowerBound220
  (gR hR gZ gQ gR_sub gZ_eq_q_pow gQ_ne_zero gZ_ne_zero abs_one_le_int
    zeta7_pow_seven zeta7_pow_add_seven sum_zeta7_explicit
    cθ sθ abs_hR_lt_thirty
    sin_four_pi_div_seven_ge_half)

-- Disambiguate the two `abs_linform_ge_of_small` (220 vs Sharper).
open LeanLab.Scratch.LemmaDLowerBound220 (abs_linform_ge_of_small)
open LeanLab.Scratch.LemmaDLowerBound330 (cθ' sθ' cθ'_eq_neg_cos_pi_div_seven
  sθ'_eq_sin_pi_div_seven sθ'_ge_two_div_five)
/-! ## Shared count helper -/

noncomputable def countT (q : Fin 3 → ℤ) {N : ℕ}
    (s : Fin N → Fin 3 → ℤ) (t : ℤ) : ℕ :=
  #{k : Fin N | signedWeight q (s k) = t}

lemma countT_partition3 (q : Fin 3 → ℤ) {N : ℕ}
    (s : Fin N → Fin 3 → ℤ)
    {t0 t1 t2 : ℤ}
    (hne01 : t0 ≠ t1) (hne02 : t0 ≠ t2) (hne12 : t1 ≠ t2)
    (hmem : ∀ k, signedWeight q (s k) = t0 ∨
      signedWeight q (s k) = t1 ∨ signedWeight q (s k) = t2) :
    countT q s t0 + countT q s t1 + countT q s t2 = N := by
  classical
  set S0 : Finset (Fin N) := {k | signedWeight q (s k) = t0}
  set S1 : Finset (Fin N) := {k | signedWeight q (s k) = t1}
  set S2 : Finset (Fin N) := {k | signedWeight q (s k) = t2}
  have hdisj01 : Disjoint S0 S1 := by
    refine disjoint_left.mpr ?_
    intro x hx0 hx1
    simp only [S0, S1, mem_filter, mem_univ, true_and] at hx0 hx1
    omega
  have hdisj02 : Disjoint S0 S2 := by
    refine disjoint_left.mpr ?_
    intro x hx0 hx2
    simp only [S0, S2, mem_filter, mem_univ, true_and] at hx0 hx2
    omega
  have hdisj12 : Disjoint S1 S2 := by
    refine disjoint_left.mpr ?_
    intro x hx1 hx2
    simp only [S1, S2, mem_filter, mem_univ, true_and] at hx1 hx2
    omega
  have hcover : S0 ∪ S1 ∪ S2 = univ := by
    ext k
    constructor
    · intro; exact mem_univ _
    · intro _
      simp only [S0, S1, S2, mem_union, mem_filter, mem_univ, true_and]
      simpa [or_assoc] using hmem k
  have hcard : (S0 ∪ S1 ∪ S2).card = N := by
    rw [hcover, card_univ, Fintype.card_fin]
  have hdisj_left : Disjoint (S0 ∪ S1) S2 :=
    Disjoint.sup_left hdisj02 hdisj12
  rw [card_union_of_disjoint hdisj_left, card_union_of_disjoint hdisj01] at hcard
  simpa [countT, S0, S1, S2] using hcard

lemma countT_partition4 (q : Fin 3 → ℤ) {N : ℕ}
    (s : Fin N → Fin 3 → ℤ)
    {t0 t1 t2 t3 : ℤ}
    (hne01 : t0 ≠ t1) (hne02 : t0 ≠ t2) (hne03 : t0 ≠ t3)
    (hne12 : t1 ≠ t2) (hne13 : t1 ≠ t3) (hne23 : t2 ≠ t3)
    (hmem : ∀ k, signedWeight q (s k) = t0 ∨ signedWeight q (s k) = t1 ∨
      signedWeight q (s k) = t2 ∨ signedWeight q (s k) = t3) :
    countT q s t0 + countT q s t1 + countT q s t2 + countT q s t3 = N := by
  classical
  set S0 : Finset (Fin N) := {k | signedWeight q (s k) = t0}
  set S1 : Finset (Fin N) := {k | signedWeight q (s k) = t1}
  set S2 : Finset (Fin N) := {k | signedWeight q (s k) = t2}
  set S3 : Finset (Fin N) := {k | signedWeight q (s k) = t3}
  have d01 : Disjoint S0 S1 := by
    refine disjoint_left.mpr ?_; intro x hx0 hx1
    simp only [S0, S1, mem_filter, mem_univ, true_and] at hx0 hx1
    omega
  have d02 : Disjoint S0 S2 := by
    refine disjoint_left.mpr ?_; intro x hx0 hx2
    simp only [S0, S2, mem_filter, mem_univ, true_and] at hx0 hx2
    omega
  have d03 : Disjoint S0 S3 := by
    refine disjoint_left.mpr ?_; intro x hx0 hx3
    simp only [S0, S3, mem_filter, mem_univ, true_and] at hx0 hx3
    omega
  have d12 : Disjoint S1 S2 := by
    refine disjoint_left.mpr ?_; intro x hx1 hx2
    simp only [S1, S2, mem_filter, mem_univ, true_and] at hx1 hx2
    omega
  have d13 : Disjoint S1 S3 := by
    refine disjoint_left.mpr ?_; intro x hx1 hx3
    simp only [S1, S3, mem_filter, mem_univ, true_and] at hx1 hx3
    omega
  have d23 : Disjoint S2 S3 := by
    refine disjoint_left.mpr ?_; intro x hx2 hx3
    simp only [S2, S3, mem_filter, mem_univ, true_and] at hx2 hx3
    omega
  have hcover : S0 ∪ S1 ∪ S2 ∪ S3 = univ := by
    ext k
    constructor
    · intro; exact mem_univ _
    · intro _
      simp only [S0, S1, S2, S3, mem_union, mem_filter, mem_univ, true_and]
      simpa [or_assoc] using hmem k
  have hcard : (S0 ∪ S1 ∪ S2 ∪ S3).card = N := by
    rw [hcover, card_univ, Fintype.card_fin]
  have d01_2 : Disjoint (S0 ∪ S1) S2 := Disjoint.sup_left d02 d12
  have d012_3 : Disjoint (S0 ∪ S1 ∪ S2) S3 :=
    Disjoint.sup_left (Disjoint.sup_left d03 d13) d23
  rw [card_union_of_disjoint d012_3, card_union_of_disjoint d01_2,
    card_union_of_disjoint d01] at hcard
  simpa [countT, S0, S1, S2, S3] using hcard

lemma norm_structureFactor_eq_div {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ) (q : Fin 3 → ℝ) :
    ‖structureFactor (fun k => centroidPoint (n k) (s k)) q‖ =
      ‖(∑ k : Fin N,
          exp (2 * Real.pi * I * dot3 q (centroidPoint (n k) (s k))))‖ /
        (N : ℝ) := by
  unfold structureFactor
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  field_simp

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

lemma c0_div_N3_le_sigma_div_N {N : ℕ} (hN : 1 ≤ N)
    {c0 σ0 H : ℝ} (hc0 : c0 = 1 / H) (hHpos : (0 : ℝ) < H)
    (_hσ : (0 : ℝ) < σ0) (hcmp : 1 / H ≤ σ0) :
    c0 / (N : ℝ) ^ 3 ≤ σ0 / N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hN2 : (1 : ℝ) ≤ (N : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  rw [hc0]
  have heqL : (1 / H) / (N : ℝ) ^ 3 = 1 / (H * (N : ℝ) ^ 3) := by field_simp
  rw [heqL]
  have h1 : (1 : ℝ) ≤ σ0 * H := by
    have := mul_le_mul_of_nonneg_right hcmp (le_of_lt hHpos)
    field_simp [ne_of_gt hHpos] at this
    simpa [mul_comm] using this
  have hdenpos : (0 : ℝ) < H * (N : ℝ) ^ 3 := by positivity
  rw [div_le_div_iff₀ hdenpos hNpos]
  calc
    (1 : ℝ) * N ≤ (σ0 * H) * N := by nlinarith [h1]
    _ ≤ (σ0 * H) * (N : ℝ) ^ 3 := by
        have : (N : ℝ) ≤ (N : ℝ) ^ 3 := by nlinarith [hN2, hNpos]
        nlinarith [h1]
    _ = σ0 * (H * (N : ℝ) ^ 3) := by ring

lemma c0_div_N3_le_one_div_N_of {N : ℕ} (hN : 1 ≤ N)
    {c0 H : ℝ} (hc0 : c0 = 1 / H) (hHge : (1 : ℝ) ≤ H) :
    c0 / (N : ℝ) ^ 3 ≤ (1 : ℝ) / N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hN2 : (1 : ℝ) ≤ (N : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  have hHpos : (0 : ℝ) < H := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hHge
  rw [hc0]
  have heqL : (1 / H) / (N : ℝ) ^ 3 = 1 / (H * (N : ℝ) ^ 3) := by field_simp
  rw [heqL]
  have hdenpos : (0 : ℝ) < H * (N : ℝ) ^ 3 := by positivity
  rw [div_le_div_iff₀ hdenpos hNpos]
  have h1 : (1 : ℝ) ≤ H * (N : ℝ) ^ 2 := by nlinarith [hHge, hN2]
  calc
    (1 : ℝ) * N ≤ (H * (N : ℝ) ^ 2) * N := by nlinarith [h1]
    _ = 1 * (H * (N : ℝ) ^ 3) := by ring

lemma c0_div_N3_le_one_of {N : ℕ} (hN : 1 ≤ N)
    {c0 H : ℝ} (hc0 : c0 = 1 / H) (hHge : (1 : ℝ) ≤ H) :
    c0 / (N : ℝ) ^ 3 ≤ 1 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  exact le_trans (c0_div_N3_le_one_div_N_of hN hc0 hHge)
    (div_le_one_of_le₀ (by exact_mod_cast hN : (1 : ℝ) ≤ N) hNpos.le)

/-- Generic cubic lower bound from three counts and a linear-form estimate. -/
lemma norm_ge_c0_div_N3_of_counts {N : ℕ} (hN : 1 ≤ N)
    (a b b' : ℕ) (hcard : a + b + b' = N)
    (c sθ H c0 σ0 : ℝ) (S : ℂ)
    (hre_of_eq : b = b' →
      |S.re| = |((a : ℝ) + (2 * (b : ℝ)) * c)|)
    (him : S.im = ((b' : ℝ) - (b : ℝ)) * sθ)
    (hσpos : (0 : ℝ) < σ0) (hsin : σ0 ≤ sθ)
    (hHge : (1 : ℝ) ≤ H) (hc0 : c0 = 1 / H)
    (hlin : ∀ (p q : ℤ), q ≠ 0 →
      |((p : ℝ) + (q : ℝ) * c)| < 1 →
        1 / (H * (q : ℝ) ^ 2) ≤ |((p : ℝ) + (q : ℝ) * c)|)
    (hcmpσ : 1 / H ≤ σ0) :
    c0 / (N : ℝ) ^ 3 ≤ ‖S‖ / N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hHpos : (0 : ℝ) < H := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hHge
  by_cases hbb : b = b'
  · have him0 : S.im = 0 := by rw [him, hbb, sub_self, zero_mul]
    have hNF : ‖S‖ = |((a : ℝ) + (2 * (b : ℝ)) * c)| := by
      have hS : S = (S.re : ℂ) := Complex.ext (by simp) (by simp [him0])
      have habs : ‖(S.re : ℂ)‖ = |S.re| := by
        rw [Complex.norm_real, Real.norm_eq_abs]
      rw [hS, habs, hre_of_eq hbb]
    rw [hNF]
    set p : ℤ := (a : ℤ)
    set q : ℤ := 2 * (b : ℤ)
    have hpq : ((a : ℝ) + (2 * (b : ℝ)) * c) =
        ((p : ℝ) + (q : ℝ) * c) := by
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
      have : |((a : ℝ) + (2 * (b : ℝ)) * c)| = (N : ℝ) := by
        simp [hb0, haN]
      rw [this, div_self (ne_of_gt hNpos)]
      exact c0_div_N3_le_one_of hN hc0 hHge
    · have hqne : q ≠ 0 := by
        unfold q
        have : (b : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hb0
        omega
      rw [hpq]
      by_cases hge1 : 1 ≤ |((p : ℝ) + (q : ℝ) * c)|
      · have : 1 / (N : ℝ) ≤ |((p : ℝ) + (q : ℝ) * c)| / N :=
          div_le_div_of_nonneg_right hge1 hNpos.le
        exact le_trans (c0_div_N3_le_one_div_N_of hN hc0 hHge) this
      · have hsmall : |((p : ℝ) + (q : ℝ) * c)| < 1 := lt_of_not_ge hge1
        have hlb := hlin p q hqne hsmall
        have hstep :
            1 / (H * (q : ℝ) ^ 2) / N ≤ |((p : ℝ) + (q : ℝ) * c)| / N :=
          div_le_div_of_nonneg_right hlb hNpos.le
        have hq2 : (q : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := by
          have h1 : (q : ℝ) ^ 2 = |(q : ℝ)| ^ 2 := (sq_abs (q : ℝ)).symm
          rw [h1]
          exact pow_le_pow_left₀ (abs_nonneg (q : ℝ)) hqN 2
        have hcmp : c0 / (N : ℝ) ^ 3 ≤ 1 / (H * (q : ℝ) ^ 2) / N := by
          rw [hc0]
          have hL : (1 / H) / N ^ 3 = 1 / (H * N ^ 3) := by field_simp
          have hR : (1 : ℝ) / (H * (q : ℝ) ^ 2) / N =
              1 / (H * (q : ℝ) ^ 2 * N) := by field_simp
          rw [hL, hR]
          have hpos1 : (0 : ℝ) < H * N ^ 3 := by positivity
          have hpos2 : (0 : ℝ) < H * (q : ℝ) ^ 2 * N := by
            have : (q : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hqne
            positivity
          rw [one_div_le_one_div hpos1 hpos2]
          have hle_q : H * (q : ℝ) ^ 2 * N ≤ H * (N : ℝ) ^ 2 * N := by
            have hmid : H * (q : ℝ) ^ 2 ≤ H * (N : ℝ) ^ 2 :=
              mul_le_mul_of_nonneg_left hq2 (le_of_lt hHpos)
            exact mul_le_mul_of_nonneg_right hmid (le_of_lt hNpos)
          have heq_N : H * (N : ℝ) ^ 2 * N = H * (N : ℝ) ^ 3 := by ring
          rw [← heq_N]
          exact hle_q
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
    have himabs : σ0 ≤ |S.im| := by
      rw [him, abs_mul, abs_of_pos (lt_of_lt_of_le hσpos hsin)]
      nlinarith [hsin, hdiff]
    have hSbound : σ0 ≤ ‖S‖ :=
      le_trans himabs (Complex.abs_im_le_norm S)
    have hle : σ0 / N ≤ ‖S‖ / N :=
      div_le_div_of_nonneg_right hSbound hNpos.le
    exact le_trans (c0_div_N3_le_sigma_div_N hN hc0 hHpos hσpos hcmpσ) hle

/-! ## Cosine `cos(2π/7)`: cubic identity and `|h| < 38` -/

noncomputable def c2 : ℝ := Real.cos (2 * Real.pi / 7)
noncomputable def s2 : ℝ := Real.sin (2 * Real.pi / 7)
noncomputable def c0_110 : ℝ := 1 / 38

lemma zeta7_add_pow_six :
    zeta7 + zeta7 ^ 6 = 2 * (c2 : ℂ) := by
  have hz1 : zeta7 ^ (1 : ℕ) = exp (2 * Real.pi * I * (1 : ℕ) / 7) := zeta7_pow 1
  have hz6 : zeta7 ^ (6 : ℕ) = exp (2 * Real.pi * I * (6 : ℕ) / 7) := zeta7_pow 6
  have hz : zeta7 + zeta7 ^ 6 = zeta7 ^ 1 + zeta7 ^ 6 := by rw [pow_one]
  rw [hz, hz1, hz6]
  have h1 : (2 * Real.pi * I * (1 : ℕ) / 7 : ℂ) =
      (↑(2 * Real.pi / 7) : ℂ) * I := by
    push_cast; ring
  have h6 : (2 * Real.pi * I * (6 : ℕ) / 7 : ℂ) =
      (↑(-(2 * Real.pi / 7)) : ℂ) * I + 2 * Real.pi * I := by
    push_cast; ring
  rw [h1, h6, exp_add]
  have h2π : exp (2 * Real.pi * I) = 1 := by
    have h := exp_two_pi_I_int (1 : ℤ)
    have heq : (2 * Real.pi * I : ℂ) = 2 * Real.pi * I * ((1 : ℤ) : ℝ) := by
      push_cast; ring
    rw [heq, h]
  rw [h2π, mul_one]
  rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
  rw [Real.cos_neg, Real.sin_neg]
  unfold c2
  push_cast
  ring

lemma eta2_cubic_zero :
    (zeta7 + zeta7 ^ 6) ^ 3 + (zeta7 + zeta7 ^ 6) ^ 2
      - 2 * (zeta7 + zeta7 ^ 6) - 1 = 0 := by
  set z := zeta7
  have hz7 : z ^ 7 = 1 := zeta7_pow_seven
  have h8 : z ^ 8 = z := by
    rw [show (8 : ℕ) = 1 + 7 from by decide, zeta7_pow_add_seven, pow_one]
  have h11 : z ^ 11 = z ^ 4 := by
    rw [show (11 : ℕ) = 4 + 7 from by decide, zeta7_pow_add_seven]
  have h12 : z ^ 12 = z ^ 5 := by
    rw [show (12 : ℕ) = 5 + 7 from by decide, zeta7_pow_add_seven]
  have hη2 : (z + z ^ 6) ^ 2 = z ^ 2 + 2 + z ^ 5 := by
    have hexp :
        (z + z ^ 6) ^ 2 = z * z + z * z ^ 6 + z ^ 6 * z + z ^ 6 * z ^ 6 := by
      ring
    have p11 : z * z = z ^ 2 := by rw [← pow_two]
    have p16 : z * z ^ 6 = z ^ 7 := by
      have : z * z ^ 6 = z ^ 1 * z ^ 6 := by rw [pow_one]
      rw [this, ← pow_add]
    have p61 : z ^ 6 * z = z ^ 7 := by rw [← pow_succ]
    have p66 : z ^ 6 * z ^ 6 = z ^ 12 := by rw [← pow_add]
    rw [hexp, p11, p16, p61, p66, hz7, h12]
    ring
  have hη3 : (z + z ^ 6) ^ 3 = 3 * z + z ^ 3 + z ^ 4 + 3 * z ^ 6 := by
    have hmul : (z + z ^ 6) ^ 3 = (z + z ^ 6) * (z + z ^ 6) ^ 2 := by ring
    rw [hmul, hη2]
    have hexp :
        (z + z ^ 6) * (z ^ 2 + 2 + z ^ 5) =
          z * z ^ 2 + z * 2 + z * z ^ 5 +
            z ^ 6 * z ^ 2 + z ^ 6 * 2 + z ^ 6 * z ^ 5 := by ring
    have pz2 : z * z ^ 2 = z ^ 3 := by
      have : z * z ^ 2 = z ^ 1 * z ^ 2 := by rw [pow_one]
      rw [this, ← pow_add]
    have pz5 : z * z ^ 5 = z ^ 6 := by
      have : z * z ^ 5 = z ^ 1 * z ^ 5 := by rw [pow_one]
      rw [this, ← pow_add]
    have p62 : z ^ 6 * z ^ 2 = z ^ 8 := by rw [← pow_add]
    have p65 : z ^ 6 * z ^ 5 = z ^ 11 := by rw [← pow_add]
    rw [hexp, pz2, pz5, p62, p65, h8, h11]
    ring
  rw [hη3, hη2]
  have hsum := sum_zeta7_explicit
  convert hsum using 1
  ring

lemma gR_c2_eq_zero : gR c2 = 0 := by
  have hη := eta2_cubic_zero
  rw [zeta7_add_pow_six] at hη
  have hC : ((gR c2 : ℝ) : ℂ) = 0 := by
    unfold gR
    convert hη using 1
    push_cast
    ring
  exact_mod_cast (ofReal_eq_zero.mp hC)

lemma two_pi_div_seven_lt_pi_div_three :
    (2 : ℝ) * Real.pi / 7 < Real.pi / 3 := by
  have hmul : ((2 : ℝ) / 7) * Real.pi < ((1 : ℝ) / 3) * Real.pi :=
    mul_lt_mul_of_pos_right (by norm_num) Real.pi_pos
  convert hmul using 1 <;> ring

lemma c2_gt_half : (1 / 2 : ℝ) < c2 := by
  unfold c2
  have hcos3 : Real.cos (Real.pi / 3) = 1 / 2 := Real.cos_pi_div_three
  have hlt := two_pi_div_seven_lt_pi_div_three
  have hlo : 0 ≤ (2 : ℝ) * Real.pi / 7 := by positivity
  have : Real.cos (Real.pi / 3) < Real.cos (2 * Real.pi / 7) :=
    Real.cos_lt_cos_of_nonneg_of_le_pi hlo (by linarith [Real.pi_pos]) hlt
  rwa [hcos3] at this

lemma gR_eval_five_eighths : (0 : ℝ) < gR (5 / 8) := by
  unfold gR
  norm_num

lemma c2_lt_five_eighths : c2 < 5 / 8 := by
  have hc0 : gR c2 = 0 := gR_c2_eq_zero
  have h58 : (1 / 2 : ℝ) ≤ 5 / 8 := by norm_num
  have hmono : ∀ {x y : ℝ}, (1 / 2 : ℝ) ≤ x → x < y → gR x < gR y := by
    intro x y hx hxy
    have hdiff : gR y - gR x = (y - x) * hR y x := gR_sub y x
    have hq : 0 < hR y x := by
      unfold hR
      have hx2 : (1 / 4 : ℝ) ≤ x ^ 2 := by
        have hmul := mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 1 / 2) hx
        have hL : (1 / 2 : ℝ) * (1 / 2) = 1 / 4 := by norm_num
        have hsq : x * x = x ^ 2 := by ring
        rwa [hL, hsq] at hmul
      have hy : (1 / 2 : ℝ) ≤ y := le_trans hx (le_of_lt hxy)
      have hy2 : (1 / 4 : ℝ) ≤ y ^ 2 := by
        have hmul := mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 1 / 2) hy
        have hL : (1 / 2 : ℝ) * (1 / 2) = 1 / 4 := by norm_num
        have hsq : y * y = y ^ 2 := by ring
        rwa [hL, hsq] at hmul
      have hxyterm : (1 / 4 : ℝ) ≤ y * x := by
        have hmul : (1 / 2 : ℝ) * (1 / 2) ≤ y * x :=
          mul_le_mul hy hx (by norm_num) (by linarith)
        have hL : (1 / 2 : ℝ) * (1 / 2) = 1 / 4 := by norm_num
        rwa [hL] at hmul
      nlinarith
    have : 0 < gR y - gR x := by
      rw [hdiff]
      exact mul_pos (sub_pos.mpr hxy) hq
    linarith
  by_contra h
  have hle : (5 / 8 : ℝ) ≤ c2 := le_of_not_gt h
  have hne : (5 / 8 : ℝ) ≠ c2 := by
    intro heq
    have : (0 : ℝ) < gR (5 / 8) := gR_eval_five_eighths
    rw [heq, hc0] at this
    exact (lt_irrefl (0 : ℝ) this)
  have hlt : (5 / 8 : ℝ) < c2 := lt_of_le_of_ne hle hne
  have : gR (5 / 8) < gR c2 := hmono h58 hlt
  rw [hc0] at this
  linarith [gR_eval_five_eighths]

lemma s2_pos : 0 < s2 := by
  unfold s2
  have hgt : 0 < (2 : ℝ) * Real.pi / 7 := by positivity
  have hlt : (2 : ℝ) * Real.pi / 7 < Real.pi := by
    have : (2 : ℝ) / 7 < 1 := by norm_num
    calc
      (2 : ℝ) * Real.pi / 7 = ((2 : ℝ) / 7) * Real.pi := by ring
      _ < 1 * Real.pi := mul_lt_mul_of_pos_right this Real.pi_pos
      _ = Real.pi := one_mul _
  exact Real.sin_pos_of_mem_Ioo ⟨hgt, hlt⟩

lemma s2_ge_three_quarters : (3 / 4 : ℝ) ≤ s2 := by
  have hsin2 : s2 ^ 2 = 1 - c2 ^ 2 := by
    unfold s2 c2
    rw [← Real.sin_sq_add_cos_sq (2 * Real.pi / 7)]
    ring
  have hc2 : c2 ^ 2 < (5 / 8 : ℝ) ^ 2 := by
    have hpos : 0 ≤ c2 := le_of_lt (lt_trans (by norm_num : (0 : ℝ) < 1 / 2) c2_gt_half)
    have hmul := mul_self_lt_mul_self hpos c2_lt_five_eighths
    have hL : c2 * c2 = c2 ^ 2 := by ring
    have hR : (5 / 8 : ℝ) * (5 / 8) = (5 / 8) ^ 2 := by ring
    rwa [hL, hR] at hmul
  have : (3 / 4 : ℝ) ^ 2 ≤ s2 ^ 2 := by
    have : 1 - (5 / 8 : ℝ) ^ 2 = 39 / 64 := by norm_num
    have : (3 / 4 : ℝ) ^ 2 = 9 / 16 := by norm_num
    have : (9 / 16 : ℝ) ≤ 39 / 64 := by norm_num
    have h1 : 1 - c2 ^ 2 > 1 - (5 / 8 : ℝ) ^ 2 := by linarith
    rw [← hsin2] at h1
    linarith
  exact (sq_le_sq₀ (by norm_num) (le_of_lt s2_pos)).mp this

lemma hR_sub_same (x y c : ℝ) :
    hR x c - hR y c = (x - y) * (8 * (x + y) + 8 * c + 4) := by
  unfold hR
  ring

lemma hR_eval_left (c : ℝ) : hR (c - 1) c = 24 * c ^ 2 - 16 * c := by
  unfold hR; ring

lemma hR_eval_right (c : ℝ) : hR (c + 1) c = 24 * c ^ 2 + 32 * c + 8 := by
  unfold hR; ring

lemma vertex_le_c2_sub_one : -(2 * c2 + 1) / 4 ≤ c2 - 1 := by
  -- equivalent to c2 ≥ 1/2, strict actually, but ≤ holds
  have : (1 / 2 : ℝ) ≤ c2 := le_of_lt c2_gt_half
  linarith

lemma hR_strict_mono_c2 {x y : ℝ}
    (hx : c2 - 1 ≤ x) (hxy : x < y) :
    hR x c2 < hR y c2 := by
  have hdiff : hR y c2 - hR x c2 =
      (y - x) * (8 * (y + x) + 8 * c2 + 4) := hR_sub_same y x c2
  have hposd : 0 < y - x := sub_pos.mpr hxy
  have hfac : 0 < 8 * (y + x) + 8 * c2 + 4 := by
    have hgt : 8 * (y + x) + 8 * c2 + 4 > 16 * x + 8 * c2 + 4 := by linarith
    have hge : 16 * x + 8 * c2 + 4 ≥ 16 * (c2 - 1) + 8 * c2 + 4 := by
      linarith [hx]
    have heq : 16 * (c2 - 1) + 8 * c2 + 4 = 24 * c2 - 12 := by ring
    have hpos : 0 < 24 * c2 - 12 := by linarith [c2_gt_half]
    linarith
  have : 0 < hR y c2 - hR x c2 := by
    rw [hdiff]
    exact mul_pos hposd hfac
  linarith

lemma hR_right_c2_lt_thirtyeight : hR (c2 + 1) c2 < 38 := by
  rw [hR_eval_right]
  have hc := c2_lt_five_eighths
  have hpos : 0 < c2 := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) c2_gt_half
  have hsq : c2 ^ 2 < (5 / 8 : ℝ) ^ 2 := by
    have hmul := mul_self_lt_mul_self (le_of_lt hpos) hc
    have hL : c2 * c2 = c2 ^ 2 := by ring
    have hR : (5 / 8 : ℝ) * (5 / 8) = (5 / 8) ^ 2 := by ring
    rwa [hL, hR] at hmul
  have hlin : 32 * c2 < 32 * (5 / 8 : ℝ) := by nlinarith [hc]
  have hnum : 24 * (5 / 8 : ℝ) ^ 2 + 32 * (5 / 8) + 8 < 38 := by norm_num
  nlinarith [hpos]

lemma hR_left_c2_gt_neg_thirtyeight : -38 < hR (c2 - 1) c2 := by
  rw [hR_eval_left]
  have hlo : (1 / 2 : ℝ) < c2 := c2_gt_half
  have hhi : c2 < 5 / 8 := c2_lt_five_eighths
  -- 24 c² - 16 c > 24*(1/2)² - 16*(5/8) = 6 - 10 = -4 > -38
  have hsq : (1 / 4 : ℝ) < c2 ^ 2 := by
    have hpos : 0 < c2 := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hlo
    have hmul := mul_self_lt_mul_self (le_of_lt (by norm_num : (0 : ℝ) < 1 / 2)) hlo
    have hL : (1 / 2 : ℝ) * (1 / 2) = 1 / 4 := by norm_num
    have hR : c2 * c2 = c2 ^ 2 := by ring
    rwa [hL, hR] at hmul
  nlinarith

lemma abs_hR_lt_thirtyeight (x : ℝ) (hx : |x - c2| < 1) :
    |hR x c2| < 38 := by
  have hxabs := abs_lt.mp hx
  have hxI : c2 - 1 < x ∧ x < c2 + 1 :=
    ⟨by linarith [hxabs.1], by linarith [hxabs.2]⟩
  have hltL : hR (c2 - 1) c2 < hR x c2 :=
    hR_strict_mono_c2 le_rfl hxI.1
  have hltR : hR x c2 < hR (c2 + 1) c2 :=
    hR_strict_mono_c2 (by linarith [hxI.1]) hxI.2
  have hlo : -38 < hR x c2 := lt_trans hR_left_c2_gt_neg_thirtyeight hltL
  have hhi : hR x c2 < 38 := lt_trans hltR hR_right_c2_lt_thirtyeight
  exact abs_lt.mpr ⟨hlo, hhi⟩

lemma abs_linform_ge_of_small_c2 (p q : ℤ) (hq : q ≠ 0)
    (hsmall : |((p : ℝ) + (q : ℝ) * c2)| < 1) :
    1 / (38 * (q : ℝ) ^ 2) ≤ |((p : ℝ) + (q : ℝ) * c2)| := by
  have hqR : (q : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hq
  set x0 : ℝ := -((p : ℝ) / q)
  have hdiff : x0 - c2 = -((p : ℝ) + (q : ℝ) * c2) / q := by
    unfold x0
    field_simp [hqR]
    ring
  have hdiffabs : |x0 - c2| = |((p : ℝ) + (q : ℝ) * c2)| / |(q : ℝ)| := by
    rw [hdiff, abs_div, abs_neg]
  have hqabs : (1 : ℝ) ≤ |(q : ℝ)| := abs_one_le_int hq
  have hxlt : |x0 - c2| < 1 := by
    rw [hdiffabs]
    exact (div_lt_one (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hqabs)).2
      (lt_of_lt_of_le hsmall hqabs)
  have hfact : gR x0 = (x0 - c2) * hR x0 c2 := by
    have : gR x0 = gR x0 - gR c2 := by rw [gR_c2_eq_zero, sub_zero]
    rw [this, gR_sub]
  have hgZ : (gZ p q : ℝ) = (q : ℝ) ^ 3 * gR x0 := by
    rw [gZ_eq_q_pow p q hq]
    congr 2
    unfold x0
    field_simp [hqR]
  have hgz0 : gZ p q ≠ 0 := gZ_ne_zero p q hq
  have habsZ : (1 : ℝ) ≤ |(gZ p q : ℝ)| := abs_one_le_int hgz0
  have hh : |hR x0 c2| < 38 := abs_hR_lt_thirtyeight x0 hxlt
  have hh0 : hR x0 c2 ≠ 0 := by
    intro hz
    have hg0 : gR x0 = 0 := by rw [hfact, hz, mul_zero]
    have hxQ : (gQ ((-p : ℚ) / q) : ℝ) = gR x0 := by
      unfold gQ gR x0; push_cast; field_simp [hqR]
    have : gQ ((-p : ℚ) / q) = 0 := by
      have hcast : ((gQ ((-p : ℚ) / q) : ℚ) : ℝ) = 0 := by
        rw [hxQ, hg0]
      exact_mod_cast hcast
    exact gQ_ne_zero _ this
  have hprod : |gR x0| = |x0 - c2| * |hR x0 c2| := by
    rw [hfact, abs_mul]
  have hgRabs : |(q : ℝ) ^ 3| * |gR x0| = |(gZ p q : ℝ)| := by
    have habs := congrArg abs hgZ
    rw [abs_mul] at habs
    exact habs.symm
  have hq3 : |(q : ℝ) ^ 3| = |(q : ℝ)| ^ 3 := abs_pow _ _
  have hfinal :
      |((p : ℝ) + (q : ℝ) * c2)| =
        |(gZ p q : ℝ)| / (|(q : ℝ)| ^ 2 * |hR x0 c2|) := by
    have hxeq : |((p : ℝ) + (q : ℝ) * c2)| = |(q : ℝ)| * |x0 - c2| := by
      have hne : |(q : ℝ)| ≠ 0 := abs_ne_zero.mpr hqR
      rw [hdiffabs, mul_div_cancel₀ _ hne]
    have hge : |x0 - c2| = |gR x0| / |hR x0 c2| := by
      have hne : |hR x0 c2| ≠ 0 := abs_ne_zero.mpr hh0
      rw [hprod]
      field_simp [hne]
    have hgR' : |gR x0| = |(gZ p q : ℝ)| / |(q : ℝ) ^ 3| := by
      have hne : |(q : ℝ) ^ 3| ≠ 0 := by simp [hqR]
      exact eq_div_of_mul_eq hne (by rw [mul_comm]; exact hgRabs)
    rw [hxeq, hge, hgR', hq3]
    have hne1 : |hR x0 c2| ≠ 0 := abs_ne_zero.mpr hh0
    have hne2 : |(q : ℝ)| ≠ 0 := abs_ne_zero.mpr hqR
    field_simp [hne1, hne2]
  rw [hfinal]
  have hdenpos : 0 < |(q : ℝ)| ^ 2 * |hR x0 c2| := by
    have : 0 < |hR x0 c2| := abs_pos.mpr hh0
    positivity
  have hcmp : |(q : ℝ)| ^ 2 * |hR x0 c2| ≤ 38 * (q : ℝ) ^ 2 := by
    have hsq : (q : ℝ) ^ 2 = |(q : ℝ)| ^ 2 := (sq_abs (q : ℝ)).symm
    rw [hsq]
    nlinarith [le_of_lt hh, sq_nonneg |(q : ℝ)|]
  have hnumpos : 0 < 38 * (q : ℝ) ^ 2 := by
    have : (q : ℝ) ≠ 0 := hqR
    positivity
  refine (div_le_div_iff₀ hnumpos hdenpos).mpr ?_
  nlinarith [habsZ, hcmp, sq_nonneg |(q : ℝ)|]

/-! ## (1,1,0) -/

def qZ110 : Fin 3 → ℤ := qOf 1 1 0
noncomputable def q110 : Fin 3 → ℝ := qReal qZ110

lemma signedWeight_qZ110_mem (s : Fin 3 → ℤ) (hs : ∀ j, s j = 1 ∨ s j = -1) :
    signedWeight qZ110 s = 0 ∨ signedWeight qZ110 s = 2 ∨
      signedWeight qZ110 s = -2 := by
  have h0 := hs 0
  have h1 := hs 1
  simp only [signedWeight, qZ110, qOf, Fin.sum_univ_three]
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> simp [h0, h1]

lemma exp_centroid_at_110_t2 (n s : Fin 3 → ℤ)
    (ht : signedWeight qZ110 s = 2) :
    exp (2 * Real.pi * I * dot3 q110 (centroidPoint n s)) =
      (↑c2 : ℂ) - I * ↑s2 := by
  rw [show q110 = qReal qZ110 from rfl, exp_centroid_int_q, ht]
  have hθ : (-(Real.pi * ((2 : ℤ) : ℝ) / 7) : ℝ) = -(2 * Real.pi / 7) := by
    push_cast; ring
  rw [hθ, Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
  unfold c2 s2
  push_cast
  ring

lemma exp_centroid_at_110_t0 (n s : Fin 3 → ℤ)
    (ht : signedWeight qZ110 s = 0) :
    exp (2 * Real.pi * I * dot3 q110 (centroidPoint n s)) = 1 := by
  rw [show q110 = qReal qZ110 from rfl, exp_centroid_int_q, ht]
  simp

lemma exp_centroid_at_110_tneg2 (n s : Fin 3 → ℤ)
    (ht : signedWeight qZ110 s = -2) :
    exp (2 * Real.pi * I * dot3 q110 (centroidPoint n s)) =
      (↑c2 : ℂ) + I * ↑s2 := by
  rw [show q110 = qReal qZ110 from rfl, exp_centroid_int_q, ht]
  have hθ : (-(Real.pi * ((-2 : ℤ) : ℝ) / 7) : ℝ) = 2 * Real.pi / 7 := by
    push_cast; ring
  rw [hθ, Complex.exp_ofReal_mul_I]
  unfold c2 s2
  push_cast
  ring

lemma countT_110_add {N : ℕ} (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    countT qZ110 s 0 + countT qZ110 s 2 + countT qZ110 s (-2) = N :=
  countT_partition3 qZ110 s (by decide : (0 : ℤ) ≠ 2)
    (by decide : (0 : ℤ) ≠ -2) (by decide : (2 : ℤ) ≠ -2)
    (fun k => signedWeight_qZ110_mem (s k) (hs k))

lemma sum_exp_eq_counts_110 {N : ℕ}
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (∑ k : Fin N,
        exp (2 * Real.pi * I * dot3 q110 (centroidPoint (n k) (s k)))) =
      (countT qZ110 s 0 : ℂ) +
        (countT qZ110 s 2 : ℂ) * ((↑c2 : ℂ) - I * ↑s2) +
        (countT qZ110 s (-2) : ℂ) * ((↑c2 : ℂ) + I * ↑s2) := by
  classical
  set S0 : Finset (Fin N) := {k | signedWeight qZ110 (s k) = 0}
  set S2 : Finset (Fin N) := {k | signedWeight qZ110 (s k) = 2}
  set Sm : Finset (Fin N) := {k | signedWeight qZ110 (s k) = -2}
  have hdisj01 : Disjoint S0 S2 := by
    refine disjoint_left.mpr ?_
    intro x hx0 hx2
    simp only [S0, S2, mem_filter, mem_univ, true_and] at hx0 hx2
    exact absurd hx2 (by omega)
  have hdisj02 : Disjoint S0 Sm := by
    refine disjoint_left.mpr ?_
    intro x hx0 hxm
    simp only [S0, Sm, mem_filter, mem_univ, true_and] at hx0 hxm
    exact absurd hxm (by omega)
  have hdisj12 : Disjoint S2 Sm := by
    refine disjoint_left.mpr ?_
    intro x hx2 hxm
    simp only [S2, Sm, mem_filter, mem_univ, true_and] at hx2 hxm
    exact absurd hxm (by omega)
  have hcover : S0 ∪ S2 ∪ Sm = univ := by
    ext k
    constructor
    · intro; exact mem_univ _
    · intro _
      simp only [S0, S2, Sm, mem_union, mem_filter, mem_univ, true_and]
      rcases signedWeight_qZ110_mem (s k) (hs k) with h | h | h <;> simp [h]
  have hdisj_left : Disjoint (S0 ∪ S2) Sm :=
    Disjoint.sup_left hdisj02 hdisj12
  have hsum :
      (∑ k : Fin N,
          exp (2 * Real.pi * I * dot3 q110 (centroidPoint (n k) (s k)))) =
        (∑ k ∈ S0,
            exp (2 * Real.pi * I * dot3 q110 (centroidPoint (n k) (s k)))) +
          (∑ k ∈ S2,
              exp (2 * Real.pi * I * dot3 q110 (centroidPoint (n k) (s k)))) +
            (∑ k ∈ Sm,
                exp (2 * Real.pi * I * dot3 q110 (centroidPoint (n k) (s k)))) := by
    calc
      (∑ k : Fin N,
            exp (2 * Real.pi * I * dot3 q110 (centroidPoint (n k) (s k))))
          = ∑ k ∈ univ,
              exp (2 * Real.pi * I * dot3 q110 (centroidPoint (n k) (s k))) := rfl
      _ = ∑ k ∈ S0 ∪ S2 ∪ Sm,
              exp (2 * Real.pi * I * dot3 q110 (centroidPoint (n k) (s k))) := by
                rw [hcover]
      _ = ∑ k ∈ S0 ∪ S2,
              exp (2 * Real.pi * I * dot3 q110 (centroidPoint (n k) (s k))) +
            ∑ k ∈ Sm,
              exp (2 * Real.pi * I * dot3 q110 (centroidPoint (n k) (s k))) :=
            sum_union hdisj_left
      _ = (∑ k ∈ S0,
              exp (2 * Real.pi * I * dot3 q110 (centroidPoint (n k) (s k))) +
            ∑ k ∈ S2,
              exp (2 * Real.pi * I * dot3 q110 (centroidPoint (n k) (s k)))) +
            ∑ k ∈ Sm,
              exp (2 * Real.pi * I * dot3 q110 (centroidPoint (n k) (s k))) := by
            rw [sum_union hdisj01]
      _ = _ := by abel
  have h0 : ∀ k ∈ S0,
      exp (2 * Real.pi * I * dot3 q110 (centroidPoint (n k) (s k))) = 1 := by
    intro k hk; simp only [S0, mem_filter, mem_univ, true_and] at hk
    exact exp_centroid_at_110_t0 (n k) (s k) hk
  have h2 : ∀ k ∈ S2,
      exp (2 * Real.pi * I * dot3 q110 (centroidPoint (n k) (s k))) =
        (↑c2 : ℂ) - I * ↑s2 := by
    intro k hk; simp only [S2, mem_filter, mem_univ, true_and] at hk
    exact exp_centroid_at_110_t2 (n k) (s k) hk
  have hm : ∀ k ∈ Sm,
      exp (2 * Real.pi * I * dot3 q110 (centroidPoint (n k) (s k))) =
        (↑c2 : ℂ) + I * ↑s2 := by
    intro k hk; simp only [Sm, mem_filter, mem_univ, true_and] at hk
    exact exp_centroid_at_110_tneg2 (n k) (s k) hk
  rw [hsum, sum_congr rfl h0, sum_congr rfl h2, sum_congr rfl hm]
  simp only [sum_const, nsmul_eq_mul, mul_one]
  simp only [countT, S0, S2, Sm]

lemma re_sum_eq_110 {N : ℕ}
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (∑ k : Fin N,
        exp (2 * Real.pi * I * dot3 q110 (centroidPoint (n k) (s k)))).re =
      (countT qZ110 s 0 : ℝ) +
        ((countT qZ110 s 2 : ℝ) + (countT qZ110 s (-2) : ℝ)) * c2 := by
  rw [sum_exp_eq_counts_110 n s hs]
  have hpos := re_of_cos_sub_I_sin c2 s2
  have hneg := re_of_cos_add_I_sin c2 s2
  have hipos := im_of_cos_sub_I_sin c2 s2
  have hineg := im_of_cos_add_I_sin c2 s2
  rw [add_re, add_re, mul_re, mul_re]
  simp only [natCast_re, natCast_im, hpos, hneg, hipos, hineg]
  ring

lemma im_sum_eq_110 {N : ℕ}
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (∑ k : Fin N,
        exp (2 * Real.pi * I * dot3 q110 (centroidPoint (n k) (s k)))).im =
      ((countT qZ110 s (-2) : ℝ) - (countT qZ110 s 2 : ℝ)) * s2 := by
  rw [sum_exp_eq_counts_110 n s hs]
  have hpos := re_of_cos_sub_I_sin c2 s2
  have hneg := re_of_cos_add_I_sin c2 s2
  have hipos := im_of_cos_sub_I_sin c2 s2
  have hineg := im_of_cos_add_I_sin c2 s2
  rw [add_im, add_im, mul_im, mul_im]
  simp only [natCast_re, natCast_im, hpos, hneg, hipos, hineg]
  ring

/-- `[P, Lean]` `‖F‖ ≥ (1/38) / N³` at `q = (1,1,0)`. -/
theorem norm_structureFactor_ge_c0_div_N_pow_three_at_110
    {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    c0_110 / (N : ℝ) ^ 3 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) q110‖ := by
  set a := countT qZ110 s 0
  set b := countT qZ110 s 2
  set b' := countT qZ110 s (-2)
  have hcard : a + b + b' = N := countT_110_add s hs
  set S := (∑ k : Fin N,
      exp (2 * Real.pi * I * dot3 q110 (centroidPoint (n k) (s k))))
  have hnormF := norm_structureFactor_eq_div hN n s q110
  have hre : S.re = (a : ℝ) + ((b : ℝ) + (b' : ℝ)) * c2 := re_sum_eq_110 n s hs
  have him : S.im = ((b' : ℝ) - (b : ℝ)) * s2 := im_sum_eq_110 n s hs
  have hre_of_eq : b = b' →
      |S.re| = |((a : ℝ) + (2 * (b : ℝ)) * c2)| := by
    intro hbb
    have : S.re = (a : ℝ) + (2 * (b : ℝ)) * c2 := by rw [hre, hbb]; ring
    rw [this]
  have hlin : ∀ (p q : ℤ), q ≠ 0 →
      |((p : ℝ) + (q : ℝ) * c2)| < 1 →
        1 / (38 * (q : ℝ) ^ 2) ≤ |((p : ℝ) + (q : ℝ) * c2)| :=
    abs_linform_ge_of_small_c2
  have hmain :=
    norm_ge_c0_div_N3_of_counts hN a b b' hcard c2 s2 38 c0_110 (3 / 4) S
      hre_of_eq him (by norm_num) s2_ge_three_quarters (by norm_num) rfl
      hlin (by norm_num)
  rw [hnormF]
  exact hmain

theorem normSq_structureFactor_ge_c0_sq_div_N_pow_six_at_110
    {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    c0_110 ^ 2 / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) q110‖ ^ 2 := by
  have h := norm_structureFactor_ge_c0_div_N_pow_three_at_110 hN n s hs
  have hnn : 0 ≤ c0_110 / (N : ℝ) ^ 3 := by
    unfold c0_110; positivity
  have hF : 0 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) q110‖ :=
    norm_nonneg _
  have hsq := mul_le_mul h h hnn hF
  have hL : (c0_110 / (N : ℝ) ^ 3) * (c0_110 / (N : ℝ) ^ 3) =
      c0_110 ^ 2 / (N : ℝ) ^ 6 := by field_simp
  have hR : ‖structureFactor (fun k => centroidPoint (n k) (s k)) q110‖ *
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) q110‖ =
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) q110‖ ^ 2 := by
    ring
  rwa [hL, hR] at hsq


/-! ## (6,1,0) -/

def qZ610 : Fin 3 → ℤ := qOf 6 1 0
noncomputable def q610 : Fin 3 → ℝ := qReal qZ610
noncomputable def c0_610 : ℝ := 1 / 38

lemma signedWeight_qZ610_mem (s : Fin 3 → ℤ) (hs : ∀ j, s j = 1 ∨ s j = -1) :
    signedWeight qZ610 s = 7 ∨ signedWeight qZ610 s = 5 ∨
      signedWeight qZ610 s = -5 ∨ signedWeight qZ610 s = -7 := by
  have h0 := hs 0
  have h1 := hs 1
  simp only [signedWeight, qZ610, qOf, Fin.sum_univ_three]
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> simp [h0, h1]

lemma cos_five_pi_div_seven : Real.cos (5 * Real.pi / 7) = -c2 := by
  have : (5 : ℝ) * Real.pi / 7 = Real.pi - 2 * Real.pi / 7 := by ring
  rw [this, Real.cos_pi_sub]
  unfold c2
  rfl

lemma sin_five_pi_div_seven : Real.sin (5 * Real.pi / 7) = s2 := by
  have : (5 : ℝ) * Real.pi / 7 = Real.pi - 2 * Real.pi / 7 := by ring
  rw [this, Real.sin_pi_sub]
  unfold s2
  rfl

lemma exp_centroid_at_610_t7 (n s : Fin 3 → ℤ)
    (ht : signedWeight qZ610 s = 7 ∨ signedWeight qZ610 s = -7) :
    exp (2 * Real.pi * I * dot3 q610 (centroidPoint n s)) = -1 := by
  rw [show q610 = qReal qZ610 from rfl, exp_centroid_int_q]
  rcases ht with ht | ht
  · rw [ht]
    have h7 : ((7 : ℤ) : ℝ) = 7 := by norm_num
    have hθ : (-(Real.pi * ((7 : ℤ) : ℝ) / 7) : ℝ) = -Real.pi := by
      rw [h7]; field_simp
    rw [hθ, Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg,
      Real.cos_pi, Real.sin_pi]
    simp
  · rw [ht]
    have h7 : ((-7 : ℤ) : ℝ) = -7 := by norm_num
    have hθ : (-(Real.pi * ((-7 : ℤ) : ℝ) / 7) : ℝ) = Real.pi := by
      rw [h7]; field_simp
    rw [hθ, Complex.exp_ofReal_mul_I, Real.cos_pi, Real.sin_pi]
    simp

lemma exp_centroid_at_610_t5 (n s : Fin 3 → ℤ)
    (ht : signedWeight qZ610 s = 5) :
    exp (2 * Real.pi * I * dot3 q610 (centroidPoint n s)) =
      (↑(Real.cos (5 * Real.pi / 7)) : ℂ) -
        I * ↑(Real.sin (5 * Real.pi / 7)) := by
  rw [show q610 = qReal qZ610 from rfl, exp_centroid_int_q, ht]
  have hθ : (-(Real.pi * ((5 : ℤ) : ℝ) / 7) : ℝ) = -(5 * Real.pi / 7) := by
    push_cast; ring
  rw [hθ, Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
  push_cast
  ring

lemma exp_centroid_at_610_tneg5 (n s : Fin 3 → ℤ)
    (ht : signedWeight qZ610 s = -5) :
    exp (2 * Real.pi * I * dot3 q610 (centroidPoint n s)) =
      (↑(Real.cos (5 * Real.pi / 7)) : ℂ) +
        I * ↑(Real.sin (5 * Real.pi / 7)) := by
  rw [show q610 = qReal qZ610 from rfl, exp_centroid_int_q, ht]
  have hθ : (-(Real.pi * ((-5 : ℤ) : ℝ) / 7) : ℝ) = 5 * Real.pi / 7 := by
    push_cast; ring
  rw [hθ, Complex.exp_ofReal_mul_I]
  push_cast
  ring

lemma countT_610_add {N : ℕ} (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    countT qZ610 s 7 + countT qZ610 s 5 + countT qZ610 s (-5) +
      countT qZ610 s (-7) = N :=
  countT_partition4 qZ610 s
    (by decide : (7 : ℤ) ≠ 5) (by decide : (7 : ℤ) ≠ -5)
    (by decide : (7 : ℤ) ≠ -7) (by decide : (5 : ℤ) ≠ -5)
    (by decide : (5 : ℤ) ≠ -7) (by decide : (-5 : ℤ) ≠ -7)
    (fun k => signedWeight_qZ610_mem (s k) (hs k))

-- Remaining 610 sum/re/im/main plus 520 and 430 will be in part 3b if this is too long.

lemma sum_exp_eq_counts_610 {N : ℕ}
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (∑ k : Fin N,
        exp (2 * Real.pi * I * dot3 q610 (centroidPoint (n k) (s k)))) =
      (countT qZ610 s 7 : ℂ) * (-1) +
        (countT qZ610 s 5 : ℂ) *
          ((↑(Real.cos (5 * Real.pi / 7)) : ℂ) -
            I * ↑(Real.sin (5 * Real.pi / 7))) +
        (countT qZ610 s (-5) : ℂ) *
          ((↑(Real.cos (5 * Real.pi / 7)) : ℂ) +
            I * ↑(Real.sin (5 * Real.pi / 7))) +
        (countT qZ610 s (-7) : ℂ) * (-1) := by
  classical
  set S7 : Finset (Fin N) := {k | signedWeight qZ610 (s k) = 7}
  set S5 : Finset (Fin N) := {k | signedWeight qZ610 (s k) = 5}
  set Sm5 : Finset (Fin N) := {k | signedWeight qZ610 (s k) = -5}
  set Sm7 : Finset (Fin N) := {k | signedWeight qZ610 (s k) = -7}
  have d75 : Disjoint S7 S5 := by
    refine disjoint_left.mpr ?_; intro x hx hy
    simp only [S7, S5, mem_filter, mem_univ, true_and] at hx hy; omega
  have d7m5 : Disjoint S7 Sm5 := by
    refine disjoint_left.mpr ?_; intro x hx hy
    simp only [S7, Sm5, mem_filter, mem_univ, true_and] at hx hy; omega
  have d7m7 : Disjoint S7 Sm7 := by
    refine disjoint_left.mpr ?_; intro x hx hy
    simp only [S7, Sm7, mem_filter, mem_univ, true_and] at hx hy; omega
  have d5m5 : Disjoint S5 Sm5 := by
    refine disjoint_left.mpr ?_; intro x hx hy
    simp only [S5, Sm5, mem_filter, mem_univ, true_and] at hx hy; omega
  have d5m7 : Disjoint S5 Sm7 := by
    refine disjoint_left.mpr ?_; intro x hx hy
    simp only [S5, Sm7, mem_filter, mem_univ, true_and] at hx hy; omega
  have dm5m7 : Disjoint Sm5 Sm7 := by
    refine disjoint_left.mpr ?_; intro x hx hy
    simp only [Sm5, Sm7, mem_filter, mem_univ, true_and] at hx hy; omega
  have hcover : S7 ∪ S5 ∪ Sm5 ∪ Sm7 = univ := by
    ext k
    constructor
    · intro; exact mem_univ _
    · intro _
      simp only [S7, S5, Sm5, Sm7, mem_union, mem_filter, mem_univ, true_and]
      simpa [or_assoc] using signedWeight_qZ610_mem (s k) (hs k)
  have d75_m5 : Disjoint (S7 ∪ S5) Sm5 := Disjoint.sup_left d7m5 d5m5
  have d75m5_m7 : Disjoint (S7 ∪ S5 ∪ Sm5) Sm7 :=
    Disjoint.sup_left (Disjoint.sup_left d7m7 d5m7) dm5m7
  have hsum :
      (∑ k : Fin N,
          exp (2 * Real.pi * I * dot3 q610 (centroidPoint (n k) (s k)))) =
        (∑ k ∈ S7, exp (2 * Real.pi * I * dot3 q610 (centroidPoint (n k) (s k)))) +
          (∑ k ∈ S5, exp (2 * Real.pi * I * dot3 q610 (centroidPoint (n k) (s k)))) +
            (∑ k ∈ Sm5, exp (2 * Real.pi * I * dot3 q610 (centroidPoint (n k) (s k)))) +
              (∑ k ∈ Sm7, exp (2 * Real.pi * I * dot3 q610 (centroidPoint (n k) (s k)))) := by
    calc
      (∑ k : Fin N,
            exp (2 * Real.pi * I * dot3 q610 (centroidPoint (n k) (s k))))
          = ∑ k ∈ univ,
              exp (2 * Real.pi * I * dot3 q610 (centroidPoint (n k) (s k))) := rfl
      _ = ∑ k ∈ S7 ∪ S5 ∪ Sm5 ∪ Sm7,
              exp (2 * Real.pi * I * dot3 q610 (centroidPoint (n k) (s k))) := by
                rw [hcover]
      _ = ∑ k ∈ S7 ∪ S5 ∪ Sm5,
              exp (2 * Real.pi * I * dot3 q610 (centroidPoint (n k) (s k))) +
            ∑ k ∈ Sm7,
              exp (2 * Real.pi * I * dot3 q610 (centroidPoint (n k) (s k))) :=
            sum_union d75m5_m7
      _ = (∑ k ∈ S7 ∪ S5,
              exp (2 * Real.pi * I * dot3 q610 (centroidPoint (n k) (s k))) +
            ∑ k ∈ Sm5,
              exp (2 * Real.pi * I * dot3 q610 (centroidPoint (n k) (s k)))) +
            ∑ k ∈ Sm7,
              exp (2 * Real.pi * I * dot3 q610 (centroidPoint (n k) (s k))) := by
            rw [sum_union d75_m5]
      _ = ((∑ k ∈ S7,
              exp (2 * Real.pi * I * dot3 q610 (centroidPoint (n k) (s k))) +
            ∑ k ∈ S5,
              exp (2 * Real.pi * I * dot3 q610 (centroidPoint (n k) (s k)))) +
            ∑ k ∈ Sm5,
              exp (2 * Real.pi * I * dot3 q610 (centroidPoint (n k) (s k)))) +
            ∑ k ∈ Sm7,
              exp (2 * Real.pi * I * dot3 q610 (centroidPoint (n k) (s k))) := by
            rw [sum_union d75]
      _ = _ := by abel
  have h7 : ∀ k ∈ S7,
      exp (2 * Real.pi * I * dot3 q610 (centroidPoint (n k) (s k))) = -1 := by
    intro k hk; simp only [S7, mem_filter, mem_univ, true_and] at hk
    exact exp_centroid_at_610_t7 (n k) (s k) (Or.inl hk)
  have hm7 : ∀ k ∈ Sm7,
      exp (2 * Real.pi * I * dot3 q610 (centroidPoint (n k) (s k))) = -1 := by
    intro k hk; simp only [Sm7, mem_filter, mem_univ, true_and] at hk
    exact exp_centroid_at_610_t7 (n k) (s k) (Or.inr hk)
  have h5 : ∀ k ∈ S5,
      exp (2 * Real.pi * I * dot3 q610 (centroidPoint (n k) (s k))) =
        (↑(Real.cos (5 * Real.pi / 7)) : ℂ) -
          I * ↑(Real.sin (5 * Real.pi / 7)) := by
    intro k hk; simp only [S5, mem_filter, mem_univ, true_and] at hk
    exact exp_centroid_at_610_t5 (n k) (s k) hk
  have hm5 : ∀ k ∈ Sm5,
      exp (2 * Real.pi * I * dot3 q610 (centroidPoint (n k) (s k))) =
        (↑(Real.cos (5 * Real.pi / 7)) : ℂ) +
          I * ↑(Real.sin (5 * Real.pi / 7)) := by
    intro k hk; simp only [Sm5, mem_filter, mem_univ, true_and] at hk
    exact exp_centroid_at_610_tneg5 (n k) (s k) hk
  rw [hsum, sum_congr rfl h7, sum_congr rfl h5, sum_congr rfl hm5, sum_congr rfl hm7]
  simp only [sum_const, nsmul_eq_mul, mul_neg, mul_one]
  simp only [countT, S7, S5, Sm5, Sm7]

lemma re_sum_eq_610 {N : ℕ}
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (∑ k : Fin N,
        exp (2 * Real.pi * I * dot3 q610 (centroidPoint (n k) (s k)))).re =
      -((countT qZ610 s 7 : ℝ) + (countT qZ610 s (-7) : ℝ)) +
        ((countT qZ610 s 5 : ℝ) + (countT qZ610 s (-5) : ℝ)) *
          Real.cos (5 * Real.pi / 7) := by
  rw [sum_exp_eq_counts_610 n s hs]
  set c := Real.cos (5 * Real.pi / 7)
  set σ := Real.sin (5 * Real.pi / 7)
  have hpos := re_of_cos_sub_I_sin c σ
  have hneg := re_of_cos_add_I_sin c σ
  have hipos := im_of_cos_sub_I_sin c σ
  have hineg := im_of_cos_add_I_sin c σ
  rw [add_re, add_re, add_re, mul_re, mul_re, mul_re, mul_re]
  simp only [natCast_re, natCast_im, hpos, hneg, hipos, hineg, one_re, one_im,
    neg_re, neg_im]
  ring

lemma im_sum_eq_610 {N : ℕ}
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (∑ k : Fin N,
        exp (2 * Real.pi * I * dot3 q610 (centroidPoint (n k) (s k)))).im =
      ((countT qZ610 s (-5) : ℝ) - (countT qZ610 s 5 : ℝ)) *
        Real.sin (5 * Real.pi / 7) := by
  rw [sum_exp_eq_counts_610 n s hs]
  set c := Real.cos (5 * Real.pi / 7)
  set σ := Real.sin (5 * Real.pi / 7)
  have hpos := re_of_cos_sub_I_sin c σ
  have hneg := re_of_cos_add_I_sin c σ
  have hipos := im_of_cos_sub_I_sin c σ
  have hineg := im_of_cos_add_I_sin c σ
  rw [add_im, add_im, add_im, mul_im, mul_im, mul_im, mul_im]
  simp only [natCast_re, natCast_im, hpos, hneg, hipos, hineg, one_re, one_im,
    neg_re, neg_im]
  ring

/-- `[P, Lean]` `‖F‖ ≥ (1/38) / N³` at `q = (6,1,0)`. -/
theorem norm_structureFactor_ge_c0_div_N_pow_three_at_610
    {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    c0_610 / (N : ℝ) ^ 3 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) q610‖ := by
  set a := countT qZ610 s 7 + countT qZ610 s (-7)
  set b := countT qZ610 s 5
  set b' := countT qZ610 s (-5)
  have hcard : a + b + b' = N := by
    have := countT_610_add s hs
    unfold a; omega
  set S := (∑ k : Fin N,
      exp (2 * Real.pi * I * dot3 q610 (centroidPoint (n k) (s k))))
  have hnormF := norm_structureFactor_eq_div hN n s q610
  have hre : S.re =
      -((a : ℝ)) + ((b : ℝ) + (b' : ℝ)) * Real.cos (5 * Real.pi / 7) := by
    have := re_sum_eq_610 n s hs
    unfold a at *
    -- a is a nat sum; casts
    convert this using 1
    push_cast
    ring
  have him : S.im = ((b' : ℝ) - (b : ℝ)) * s2 := by
    have := im_sum_eq_610 n s hs
    rw [sin_five_pi_div_seven] at this
    exact this
  have hre_of_eq : b = b' →
      |S.re| = |((a : ℝ) + (2 * (b : ℝ)) * c2)| := by
    intro hbb
    have hrew : S.re = -((a : ℝ) + (2 * (b : ℝ)) * c2) := by
      rw [hre, hbb, cos_five_pi_div_seven]
      ring
    rw [hrew, abs_neg]
  have hlin : ∀ (p q : ℤ), q ≠ 0 →
      |((p : ℝ) + (q : ℝ) * c2)| < 1 →
        1 / (38 * (q : ℝ) ^ 2) ≤ |((p : ℝ) + (q : ℝ) * c2)| :=
    abs_linform_ge_of_small_c2
  have hmain :=
    norm_ge_c0_div_N3_of_counts hN a b b' hcard c2 s2 38 c0_610 (3 / 4) S
      hre_of_eq him (by norm_num) s2_ge_three_quarters (by norm_num) rfl
      hlin (by norm_num)
  rw [hnormF]
  exact hmain

theorem normSq_structureFactor_ge_c0_sq_div_N_pow_six_at_610
    {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    c0_610 ^ 2 / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) q610‖ ^ 2 := by
  have h := norm_structureFactor_ge_c0_div_N_pow_three_at_610 hN n s hs
  have hnn : 0 ≤ c0_610 / (N : ℝ) ^ 3 := by unfold c0_610; positivity
  have hF : 0 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) q610‖ :=
    norm_nonneg _
  have hsq := mul_le_mul h h hnn hF
  have hL : (c0_610 / (N : ℝ) ^ 3) * (c0_610 / (N : ℝ) ^ 3) =
      c0_610 ^ 2 / (N : ℝ) ^ 6 := by field_simp
  have hR : ‖structureFactor (fun k => centroidPoint (n k) (s k)) q610‖ *
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) q610‖ =
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) q610‖ ^ 2 := by
    ring
  rwa [hL, hR] at hsq


/-! ## (5,2,0) -/

def qZ520 : Fin 3 → ℤ := qOf 5 2 0
noncomputable def q520 : Fin 3 → ℝ := qReal qZ520
noncomputable def c0_520 : ℝ := 1 / 30

lemma signedWeight_qZ520_mem (s : Fin 3 → ℤ) (hs : ∀ j, s j = 1 ∨ s j = -1) :
    signedWeight qZ520 s = 7 ∨ signedWeight qZ520 s = 3 ∨
      signedWeight qZ520 s = -3 ∨ signedWeight qZ520 s = -7 := by
  have h0 := hs 0
  have h1 := hs 1
  simp only [signedWeight, qZ520, qOf, Fin.sum_univ_three]
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> simp [h0, h1]

lemma cos_three_pi_div_seven : Real.cos (3 * Real.pi / 7) = -cθ := by
  have : (3 : ℝ) * Real.pi / 7 = Real.pi - 4 * Real.pi / 7 := by ring
  rw [this, Real.cos_pi_sub]
  unfold cθ
  rfl

lemma sin_three_pi_div_seven : Real.sin (3 * Real.pi / 7) = sθ := by
  unfold sθ
  have hangle : Real.pi - 4 * Real.pi / 7 = 3 * Real.pi / 7 := by ring
  rw [← hangle, Real.sin_pi_sub]

lemma exp_centroid_at_520_t7 (n s : Fin 3 → ℤ)
    (ht : signedWeight qZ520 s = 7 ∨ signedWeight qZ520 s = -7) :
    exp (2 * Real.pi * I * dot3 q520 (centroidPoint n s)) = -1 := by
  rw [show q520 = qReal qZ520 from rfl, exp_centroid_int_q]
  rcases ht with ht | ht
  · rw [ht]
    have h7 : ((7 : ℤ) : ℝ) = 7 := by norm_num
    have hθ : (-(Real.pi * ((7 : ℤ) : ℝ) / 7) : ℝ) = -Real.pi := by
      rw [h7]; field_simp
    rw [hθ, Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg,
      Real.cos_pi, Real.sin_pi]
    simp
  · rw [ht]
    have h7 : ((-7 : ℤ) : ℝ) = -7 := by norm_num
    have hθ : (-(Real.pi * ((-7 : ℤ) : ℝ) / 7) : ℝ) = Real.pi := by
      rw [h7]; field_simp
    rw [hθ, Complex.exp_ofReal_mul_I, Real.cos_pi, Real.sin_pi]
    simp

lemma exp_centroid_at_520_tpos (n s : Fin 3 → ℤ)
    (ht : signedWeight qZ520 s = 3) :
    exp (2 * Real.pi * I * dot3 q520 (centroidPoint n s)) =
      (↑(Real.cos (3 * Real.pi / 7)) : ℂ) -
        I * ↑(Real.sin (3 * Real.pi / 7)) := by
  rw [show q520 = qReal qZ520 from rfl, exp_centroid_int_q, ht]
  have hθ : (-(Real.pi * ((3 : ℤ) : ℝ) / 7) : ℝ) = -(3 * Real.pi / 7) := by
    push_cast; ring
  rw [hθ, Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
  push_cast
  ring

lemma exp_centroid_at_520_tneg (n s : Fin 3 → ℤ)
    (ht : signedWeight qZ520 s = -3) :
    exp (2 * Real.pi * I * dot3 q520 (centroidPoint n s)) =
      (↑(Real.cos (3 * Real.pi / 7)) : ℂ) +
        I * ↑(Real.sin (3 * Real.pi / 7)) := by
  rw [show q520 = qReal qZ520 from rfl, exp_centroid_int_q, ht]
  have hθ : (-(Real.pi * ((-3 : ℤ) : ℝ) / 7) : ℝ) = 3 * Real.pi / 7 := by
    push_cast; ring
  rw [hθ, Complex.exp_ofReal_mul_I]
  push_cast
  ring

lemma countT_520_add {N : ℕ} (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    countT qZ520 s 7 + countT qZ520 s 3 + countT qZ520 s (-3) +
      countT qZ520 s (-7) = N :=
  countT_partition4 qZ520 s
    (by decide : (7 : ℤ) ≠ 3) (by decide : (7 : ℤ) ≠ -3)
    (by decide : (7 : ℤ) ≠ -7) (by decide : (3 : ℤ) ≠ -3)
    (by decide : (3 : ℤ) ≠ -7) (by decide : (-3 : ℤ) ≠ -7)
    (fun k => signedWeight_qZ520_mem (s k) (hs k))

lemma sum_exp_eq_counts_520 {N : ℕ}
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (∑ k : Fin N,
        exp (2 * Real.pi * I * dot3 q520 (centroidPoint (n k) (s k)))) =
      (countT qZ520 s 7 : ℂ) * (-1) +
        (countT qZ520 s 3 : ℂ) *
          ((↑(Real.cos (3 * Real.pi / 7)) : ℂ) -
            I * ↑(Real.sin (3 * Real.pi / 7))) +
        (countT qZ520 s (-3) : ℂ) *
          ((↑(Real.cos (3 * Real.pi / 7)) : ℂ) +
            I * ↑(Real.sin (3 * Real.pi / 7))) +
        (countT qZ520 s (-7) : ℂ) * (-1) := by
  classical
  set S7 : Finset (Fin N) := {k | signedWeight qZ520 (s k) = 7}
  set Sp : Finset (Fin N) := {k | signedWeight qZ520 (s k) = 3}
  set Sn : Finset (Fin N) := {k | signedWeight qZ520 (s k) = -3}
  set Sm7 : Finset (Fin N) := {k | signedWeight qZ520 (s k) = -7}
  have d7p : Disjoint S7 Sp := by
    refine disjoint_left.mpr ?_; intro x hx hy
    simp only [S7, Sp, mem_filter, mem_univ, true_and] at hx hy; omega
  have d7n : Disjoint S7 Sn := by
    refine disjoint_left.mpr ?_; intro x hx hy
    simp only [S7, Sn, mem_filter, mem_univ, true_and] at hx hy; omega
  have d7m7 : Disjoint S7 Sm7 := by
    refine disjoint_left.mpr ?_; intro x hx hy
    simp only [S7, Sm7, mem_filter, mem_univ, true_and] at hx hy; omega
  have dpn : Disjoint Sp Sn := by
    refine disjoint_left.mpr ?_; intro x hx hy
    simp only [Sp, Sn, mem_filter, mem_univ, true_and] at hx hy; omega
  have dpm7 : Disjoint Sp Sm7 := by
    refine disjoint_left.mpr ?_; intro x hx hy
    simp only [Sp, Sm7, mem_filter, mem_univ, true_and] at hx hy; omega
  have dnm7 : Disjoint Sn Sm7 := by
    refine disjoint_left.mpr ?_; intro x hx hy
    simp only [Sn, Sm7, mem_filter, mem_univ, true_and] at hx hy; omega
  have hcover : S7 ∪ Sp ∪ Sn ∪ Sm7 = univ := by
    ext k
    constructor
    · intro; exact mem_univ _
    · intro _
      simp only [S7, Sp, Sn, Sm7, mem_union, mem_filter, mem_univ, true_and]
      simpa [or_assoc] using signedWeight_qZ520_mem (s k) (hs k)
  have d7p_n : Disjoint (S7 ∪ Sp) Sn := Disjoint.sup_left d7n dpn
  have d7pn_m7 : Disjoint (S7 ∪ Sp ∪ Sn) Sm7 :=
    Disjoint.sup_left (Disjoint.sup_left d7m7 dpm7) dnm7
  have hsum :
      (∑ k : Fin N,
          exp (2 * Real.pi * I * dot3 q520 (centroidPoint (n k) (s k)))) =
        (∑ k ∈ S7, exp (2 * Real.pi * I * dot3 q520 (centroidPoint (n k) (s k)))) +
          (∑ k ∈ Sp, exp (2 * Real.pi * I * dot3 q520 (centroidPoint (n k) (s k)))) +
            (∑ k ∈ Sn, exp (2 * Real.pi * I * dot3 q520 (centroidPoint (n k) (s k)))) +
              (∑ k ∈ Sm7, exp (2 * Real.pi * I * dot3 q520 (centroidPoint (n k) (s k)))) := by
    calc
      (∑ k : Fin N,
            exp (2 * Real.pi * I * dot3 q520 (centroidPoint (n k) (s k))))
          = ∑ k ∈ univ,
              exp (2 * Real.pi * I * dot3 q520 (centroidPoint (n k) (s k))) := rfl
      _ = ∑ k ∈ S7 ∪ Sp ∪ Sn ∪ Sm7,
              exp (2 * Real.pi * I * dot3 q520 (centroidPoint (n k) (s k))) := by
                rw [hcover]
      _ = ∑ k ∈ S7 ∪ Sp ∪ Sn,
              exp (2 * Real.pi * I * dot3 q520 (centroidPoint (n k) (s k))) +
            ∑ k ∈ Sm7,
              exp (2 * Real.pi * I * dot3 q520 (centroidPoint (n k) (s k))) :=
            sum_union d7pn_m7
      _ = (∑ k ∈ S7 ∪ Sp,
              exp (2 * Real.pi * I * dot3 q520 (centroidPoint (n k) (s k))) +
            ∑ k ∈ Sn,
              exp (2 * Real.pi * I * dot3 q520 (centroidPoint (n k) (s k)))) +
            ∑ k ∈ Sm7,
              exp (2 * Real.pi * I * dot3 q520 (centroidPoint (n k) (s k))) := by
            rw [sum_union d7p_n]
      _ = ((∑ k ∈ S7,
              exp (2 * Real.pi * I * dot3 q520 (centroidPoint (n k) (s k))) +
            ∑ k ∈ Sp,
              exp (2 * Real.pi * I * dot3 q520 (centroidPoint (n k) (s k)))) +
            ∑ k ∈ Sn,
              exp (2 * Real.pi * I * dot3 q520 (centroidPoint (n k) (s k)))) +
            ∑ k ∈ Sm7,
              exp (2 * Real.pi * I * dot3 q520 (centroidPoint (n k) (s k))) := by
            rw [sum_union d7p]
      _ = _ := by abel
  have h7 : ∀ k ∈ S7,
      exp (2 * Real.pi * I * dot3 q520 (centroidPoint (n k) (s k))) = -1 := by
    intro k hk; simp only [S7, mem_filter, mem_univ, true_and] at hk
    exact exp_centroid_at_520_t7 (n k) (s k) (Or.inl hk)
  have hm7 : ∀ k ∈ Sm7,
      exp (2 * Real.pi * I * dot3 q520 (centroidPoint (n k) (s k))) = -1 := by
    intro k hk; simp only [Sm7, mem_filter, mem_univ, true_and] at hk
    exact exp_centroid_at_520_t7 (n k) (s k) (Or.inr hk)
  have hp : ∀ k ∈ Sp,
      exp (2 * Real.pi * I * dot3 q520 (centroidPoint (n k) (s k))) =
        (↑(Real.cos (3 * Real.pi / 7)) : ℂ) -
          I * ↑(Real.sin (3 * Real.pi / 7)) := by
    intro k hk; simp only [Sp, mem_filter, mem_univ, true_and] at hk
    exact exp_centroid_at_520_tpos (n k) (s k) hk
  have hn : ∀ k ∈ Sn,
      exp (2 * Real.pi * I * dot3 q520 (centroidPoint (n k) (s k))) =
        (↑(Real.cos (3 * Real.pi / 7)) : ℂ) +
          I * ↑(Real.sin (3 * Real.pi / 7)) := by
    intro k hk; simp only [Sn, mem_filter, mem_univ, true_and] at hk
    exact exp_centroid_at_520_tneg (n k) (s k) hk
  rw [hsum, sum_congr rfl h7, sum_congr rfl hp, sum_congr rfl hn, sum_congr rfl hm7]
  simp only [sum_const, nsmul_eq_mul, mul_neg, mul_one]
  simp only [countT, S7, Sp, Sn, Sm7]

lemma re_sum_eq_520 {N : ℕ}
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (∑ k : Fin N,
        exp (2 * Real.pi * I * dot3 q520 (centroidPoint (n k) (s k)))).re =
      -((countT qZ520 s 7 : ℝ) + (countT qZ520 s (-7) : ℝ)) +
        ((countT qZ520 s 3 : ℝ) + (countT qZ520 s (-3) : ℝ)) *
          Real.cos (3 * Real.pi / 7) := by
  rw [sum_exp_eq_counts_520 n s hs]
  set c := Real.cos (3 * Real.pi / 7)
  set σ := Real.sin (3 * Real.pi / 7)
  have hpos := re_of_cos_sub_I_sin c σ
  have hneg := re_of_cos_add_I_sin c σ
  have hipos := im_of_cos_sub_I_sin c σ
  have hineg := im_of_cos_add_I_sin c σ
  rw [add_re, add_re, add_re, mul_re, mul_re, mul_re, mul_re]
  simp only [natCast_re, natCast_im, hpos, hneg, hipos, hineg, one_re, one_im,
    neg_re, neg_im]
  ring

lemma im_sum_eq_520 {N : ℕ}
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (∑ k : Fin N,
        exp (2 * Real.pi * I * dot3 q520 (centroidPoint (n k) (s k)))).im =
      ((countT qZ520 s (-3) : ℝ) - (countT qZ520 s 3 : ℝ)) *
        Real.sin (3 * Real.pi / 7) := by
  rw [sum_exp_eq_counts_520 n s hs]
  set c := Real.cos (3 * Real.pi / 7)
  set σ := Real.sin (3 * Real.pi / 7)
  have hpos := re_of_cos_sub_I_sin c σ
  have hneg := re_of_cos_add_I_sin c σ
  have hipos := im_of_cos_sub_I_sin c σ
  have hineg := im_of_cos_add_I_sin c σ
  rw [add_im, add_im, add_im, mul_im, mul_im, mul_im, mul_im]
  simp only [natCast_re, natCast_im, hpos, hneg, hipos, hineg, one_re, one_im,
    neg_re, neg_im]
  ring

/-- `[P, Lean]` `‖F‖ ≥ (1 / 30) / N³` at `q = (5,2,0)`. -/
theorem norm_structureFactor_ge_c0_div_N_pow_three_at_520
    {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    c0_520 / (N : ℝ) ^ 3 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) q520‖ := by
  set a := countT qZ520 s 7 + countT qZ520 s (-7)
  set b := countT qZ520 s 3
  set b' := countT qZ520 s (-3)
  have hcard : a + b + b' = N := by
    have := countT_520_add s hs
    unfold a; omega
  set S := (∑ k : Fin N,
      exp (2 * Real.pi * I * dot3 q520 (centroidPoint (n k) (s k))))
  have hnormF := norm_structureFactor_eq_div hN n s q520
  have hre : S.re =
      -((a : ℝ)) + ((b : ℝ) + (b' : ℝ)) * Real.cos (3 * Real.pi / 7) := by
    have := re_sum_eq_520 n s hs
    unfold a at *
    convert this using 1
    push_cast
    ring
  have him : S.im = ((b' : ℝ) - (b : ℝ)) * sθ := by
    have := im_sum_eq_520 n s hs
    rw [sin_three_pi_div_seven] at this
    exact this
  have hre_of_eq : b = b' →
      |S.re| = |((a : ℝ) + (2 * (b : ℝ)) * cθ)| := by
    intro hbb
    have hrew : S.re = -((a : ℝ) + (2 * (b : ℝ)) * cθ) := by
      rw [hre, hbb, cos_three_pi_div_seven]
      ring
    rw [hrew, abs_neg]
  have hlin : ∀ (p q : ℤ), q ≠ 0 →
      |((p : ℝ) + (q : ℝ) * cθ)| < 1 →
        1 / (30 * (q : ℝ) ^ 2) ≤ |((p : ℝ) + (q : ℝ) * cθ)| :=
    abs_linform_ge_of_small
  have hmain :=
    norm_ge_c0_div_N3_of_counts hN a b b' hcard cθ sθ 30 c0_520 (1 / 2) S
      hre_of_eq him (by norm_num) sin_four_pi_div_seven_ge_half (by norm_num) rfl
      hlin (by norm_num)
  rw [hnormF]
  exact hmain

theorem normSq_structureFactor_ge_c0_sq_div_N_pow_six_at_520
    {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    c0_520 ^ 2 / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) q520‖ ^ 2 := by
  have h := norm_structureFactor_ge_c0_div_N_pow_three_at_520 hN n s hs
  have hnn : 0 ≤ c0_520 / (N : ℝ) ^ 3 := by unfold c0_520; positivity
  have hF : 0 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) q520‖ :=
    norm_nonneg _
  have hsq := mul_le_mul h h hnn hF
  have hL : (c0_520 / (N : ℝ) ^ 3) * (c0_520 / (N : ℝ) ^ 3) =
      c0_520 ^ 2 / (N : ℝ) ^ 6 := by field_simp
  have hR : ‖structureFactor (fun k => centroidPoint (n k) (s k)) q520‖ *
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) q520‖ =
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) q520‖ ^ 2 := by
    ring
  rwa [hL, hR] at hsq


/-! ## (4,3,0) -/

def qZ430 : Fin 3 → ℤ := qOf 4 3 0
noncomputable def q430 : Fin 3 → ℝ := qReal qZ430
noncomputable def c0_430 : ℝ := 1 / 34

lemma signedWeight_qZ430_mem (s : Fin 3 → ℤ) (hs : ∀ j, s j = 1 ∨ s j = -1) :
    signedWeight qZ430 s = 7 ∨ signedWeight qZ430 s = 1 ∨
      signedWeight qZ430 s = -1 ∨ signedWeight qZ430 s = -7 := by
  have h0 := hs 0
  have h1 := hs 1
  simp only [signedWeight, qZ430, qOf, Fin.sum_univ_three]
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> simp [h0, h1]

lemma cos_pi_div_seven : Real.cos (Real.pi / 7) = -cθ' := by
  rw [cθ'_eq_neg_cos_pi_div_seven, neg_neg]

lemma sin_pi_div_seven : Real.sin (Real.pi / 7) = sθ' :=
  sθ'_eq_sin_pi_div_seven.symm

lemma exp_centroid_at_430_t7 (n s : Fin 3 → ℤ)
    (ht : signedWeight qZ430 s = 7 ∨ signedWeight qZ430 s = -7) :
    exp (2 * Real.pi * I * dot3 q430 (centroidPoint n s)) = -1 := by
  rw [show q430 = qReal qZ430 from rfl, exp_centroid_int_q]
  rcases ht with ht | ht
  · rw [ht]
    have h7 : ((7 : ℤ) : ℝ) = 7 := by norm_num
    have hθ : (-(Real.pi * ((7 : ℤ) : ℝ) / 7) : ℝ) = -Real.pi := by
      rw [h7]; field_simp
    rw [hθ, Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg,
      Real.cos_pi, Real.sin_pi]
    simp
  · rw [ht]
    have h7 : ((-7 : ℤ) : ℝ) = -7 := by norm_num
    have hθ : (-(Real.pi * ((-7 : ℤ) : ℝ) / 7) : ℝ) = Real.pi := by
      rw [h7]; field_simp
    rw [hθ, Complex.exp_ofReal_mul_I, Real.cos_pi, Real.sin_pi]
    simp

lemma exp_centroid_at_430_tpos (n s : Fin 3 → ℤ)
    (ht : signedWeight qZ430 s = 1) :
    exp (2 * Real.pi * I * dot3 q430 (centroidPoint n s)) =
      (↑(Real.cos (Real.pi / 7)) : ℂ) -
        I * ↑(Real.sin (Real.pi / 7)) := by
  rw [show q430 = qReal qZ430 from rfl, exp_centroid_int_q, ht]
  have hθ : (-(Real.pi * ((1 : ℤ) : ℝ) / 7) : ℝ) = -(Real.pi / 7) := by
    push_cast; ring
  rw [hθ, Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
  push_cast
  ring

lemma exp_centroid_at_430_tneg (n s : Fin 3 → ℤ)
    (ht : signedWeight qZ430 s = -1) :
    exp (2 * Real.pi * I * dot3 q430 (centroidPoint n s)) =
      (↑(Real.cos (Real.pi / 7)) : ℂ) +
        I * ↑(Real.sin (Real.pi / 7)) := by
  rw [show q430 = qReal qZ430 from rfl, exp_centroid_int_q, ht]
  have hθ : (-(Real.pi * ((-1 : ℤ) : ℝ) / 7) : ℝ) = Real.pi / 7 := by
    push_cast; ring
  rw [hθ, Complex.exp_ofReal_mul_I]
  push_cast
  ring

lemma countT_430_add {N : ℕ} (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    countT qZ430 s 7 + countT qZ430 s 1 + countT qZ430 s (-1) +
      countT qZ430 s (-7) = N :=
  countT_partition4 qZ430 s
    (by decide : (7 : ℤ) ≠ 1) (by decide : (7 : ℤ) ≠ -1)
    (by decide : (7 : ℤ) ≠ -7) (by decide : (1 : ℤ) ≠ -1)
    (by decide : (1 : ℤ) ≠ -7) (by decide : (-1 : ℤ) ≠ -7)
    (fun k => signedWeight_qZ430_mem (s k) (hs k))

lemma sum_exp_eq_counts_430 {N : ℕ}
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (∑ k : Fin N,
        exp (2 * Real.pi * I * dot3 q430 (centroidPoint (n k) (s k)))) =
      (countT qZ430 s 7 : ℂ) * (-1) +
        (countT qZ430 s 1 : ℂ) *
          ((↑(Real.cos (Real.pi / 7)) : ℂ) -
            I * ↑(Real.sin (Real.pi / 7))) +
        (countT qZ430 s (-1) : ℂ) *
          ((↑(Real.cos (Real.pi / 7)) : ℂ) +
            I * ↑(Real.sin (Real.pi / 7))) +
        (countT qZ430 s (-7) : ℂ) * (-1) := by
  classical
  set S7 : Finset (Fin N) := {k | signedWeight qZ430 (s k) = 7}
  set Sp : Finset (Fin N) := {k | signedWeight qZ430 (s k) = 1}
  set Sn : Finset (Fin N) := {k | signedWeight qZ430 (s k) = -1}
  set Sm7 : Finset (Fin N) := {k | signedWeight qZ430 (s k) = -7}
  have d7p : Disjoint S7 Sp := by
    refine disjoint_left.mpr ?_; intro x hx hy
    simp only [S7, Sp, mem_filter, mem_univ, true_and] at hx hy; omega
  have d7n : Disjoint S7 Sn := by
    refine disjoint_left.mpr ?_; intro x hx hy
    simp only [S7, Sn, mem_filter, mem_univ, true_and] at hx hy; omega
  have d7m7 : Disjoint S7 Sm7 := by
    refine disjoint_left.mpr ?_; intro x hx hy
    simp only [S7, Sm7, mem_filter, mem_univ, true_and] at hx hy; omega
  have dpn : Disjoint Sp Sn := by
    refine disjoint_left.mpr ?_; intro x hx hy
    simp only [Sp, Sn, mem_filter, mem_univ, true_and] at hx hy; omega
  have dpm7 : Disjoint Sp Sm7 := by
    refine disjoint_left.mpr ?_; intro x hx hy
    simp only [Sp, Sm7, mem_filter, mem_univ, true_and] at hx hy; omega
  have dnm7 : Disjoint Sn Sm7 := by
    refine disjoint_left.mpr ?_; intro x hx hy
    simp only [Sn, Sm7, mem_filter, mem_univ, true_and] at hx hy; omega
  have hcover : S7 ∪ Sp ∪ Sn ∪ Sm7 = univ := by
    ext k
    constructor
    · intro; exact mem_univ _
    · intro _
      simp only [S7, Sp, Sn, Sm7, mem_union, mem_filter, mem_univ, true_and]
      simpa [or_assoc] using signedWeight_qZ430_mem (s k) (hs k)
  have d7p_n : Disjoint (S7 ∪ Sp) Sn := Disjoint.sup_left d7n dpn
  have d7pn_m7 : Disjoint (S7 ∪ Sp ∪ Sn) Sm7 :=
    Disjoint.sup_left (Disjoint.sup_left d7m7 dpm7) dnm7
  have hsum :
      (∑ k : Fin N,
          exp (2 * Real.pi * I * dot3 q430 (centroidPoint (n k) (s k)))) =
        (∑ k ∈ S7, exp (2 * Real.pi * I * dot3 q430 (centroidPoint (n k) (s k)))) +
          (∑ k ∈ Sp, exp (2 * Real.pi * I * dot3 q430 (centroidPoint (n k) (s k)))) +
            (∑ k ∈ Sn, exp (2 * Real.pi * I * dot3 q430 (centroidPoint (n k) (s k)))) +
              (∑ k ∈ Sm7, exp (2 * Real.pi * I * dot3 q430 (centroidPoint (n k) (s k)))) := by
    calc
      (∑ k : Fin N,
            exp (2 * Real.pi * I * dot3 q430 (centroidPoint (n k) (s k))))
          = ∑ k ∈ univ,
              exp (2 * Real.pi * I * dot3 q430 (centroidPoint (n k) (s k))) := rfl
      _ = ∑ k ∈ S7 ∪ Sp ∪ Sn ∪ Sm7,
              exp (2 * Real.pi * I * dot3 q430 (centroidPoint (n k) (s k))) := by
                rw [hcover]
      _ = ∑ k ∈ S7 ∪ Sp ∪ Sn,
              exp (2 * Real.pi * I * dot3 q430 (centroidPoint (n k) (s k))) +
            ∑ k ∈ Sm7,
              exp (2 * Real.pi * I * dot3 q430 (centroidPoint (n k) (s k))) :=
            sum_union d7pn_m7
      _ = (∑ k ∈ S7 ∪ Sp,
              exp (2 * Real.pi * I * dot3 q430 (centroidPoint (n k) (s k))) +
            ∑ k ∈ Sn,
              exp (2 * Real.pi * I * dot3 q430 (centroidPoint (n k) (s k)))) +
            ∑ k ∈ Sm7,
              exp (2 * Real.pi * I * dot3 q430 (centroidPoint (n k) (s k))) := by
            rw [sum_union d7p_n]
      _ = ((∑ k ∈ S7,
              exp (2 * Real.pi * I * dot3 q430 (centroidPoint (n k) (s k))) +
            ∑ k ∈ Sp,
              exp (2 * Real.pi * I * dot3 q430 (centroidPoint (n k) (s k)))) +
            ∑ k ∈ Sn,
              exp (2 * Real.pi * I * dot3 q430 (centroidPoint (n k) (s k)))) +
            ∑ k ∈ Sm7,
              exp (2 * Real.pi * I * dot3 q430 (centroidPoint (n k) (s k))) := by
            rw [sum_union d7p]
      _ = _ := by abel
  have h7 : ∀ k ∈ S7,
      exp (2 * Real.pi * I * dot3 q430 (centroidPoint (n k) (s k))) = -1 := by
    intro k hk; simp only [S7, mem_filter, mem_univ, true_and] at hk
    exact exp_centroid_at_430_t7 (n k) (s k) (Or.inl hk)
  have hm7 : ∀ k ∈ Sm7,
      exp (2 * Real.pi * I * dot3 q430 (centroidPoint (n k) (s k))) = -1 := by
    intro k hk; simp only [Sm7, mem_filter, mem_univ, true_and] at hk
    exact exp_centroid_at_430_t7 (n k) (s k) (Or.inr hk)
  have hp : ∀ k ∈ Sp,
      exp (2 * Real.pi * I * dot3 q430 (centroidPoint (n k) (s k))) =
        (↑(Real.cos (Real.pi / 7)) : ℂ) -
          I * ↑(Real.sin (Real.pi / 7)) := by
    intro k hk; simp only [Sp, mem_filter, mem_univ, true_and] at hk
    exact exp_centroid_at_430_tpos (n k) (s k) hk
  have hn : ∀ k ∈ Sn,
      exp (2 * Real.pi * I * dot3 q430 (centroidPoint (n k) (s k))) =
        (↑(Real.cos (Real.pi / 7)) : ℂ) +
          I * ↑(Real.sin (Real.pi / 7)) := by
    intro k hk; simp only [Sn, mem_filter, mem_univ, true_and] at hk
    exact exp_centroid_at_430_tneg (n k) (s k) hk
  rw [hsum, sum_congr rfl h7, sum_congr rfl hp, sum_congr rfl hn, sum_congr rfl hm7]
  simp only [sum_const, nsmul_eq_mul, mul_neg, mul_one]
  simp only [countT, S7, Sp, Sn, Sm7]

lemma re_sum_eq_430 {N : ℕ}
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (∑ k : Fin N,
        exp (2 * Real.pi * I * dot3 q430 (centroidPoint (n k) (s k)))).re =
      -((countT qZ430 s 7 : ℝ) + (countT qZ430 s (-7) : ℝ)) +
        ((countT qZ430 s 1 : ℝ) + (countT qZ430 s (-1) : ℝ)) *
          Real.cos (Real.pi / 7) := by
  rw [sum_exp_eq_counts_430 n s hs]
  set c := Real.cos (Real.pi / 7)
  set σ := Real.sin (Real.pi / 7)
  have hpos := re_of_cos_sub_I_sin c σ
  have hneg := re_of_cos_add_I_sin c σ
  have hipos := im_of_cos_sub_I_sin c σ
  have hineg := im_of_cos_add_I_sin c σ
  rw [add_re, add_re, add_re, mul_re, mul_re, mul_re, mul_re]
  simp only [natCast_re, natCast_im, hpos, hneg, hipos, hineg, one_re, one_im,
    neg_re, neg_im]
  ring

lemma im_sum_eq_430 {N : ℕ}
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (∑ k : Fin N,
        exp (2 * Real.pi * I * dot3 q430 (centroidPoint (n k) (s k)))).im =
      ((countT qZ430 s (-1) : ℝ) - (countT qZ430 s 1 : ℝ)) *
        Real.sin (Real.pi / 7) := by
  rw [sum_exp_eq_counts_430 n s hs]
  set c := Real.cos (Real.pi / 7)
  set σ := Real.sin (Real.pi / 7)
  have hpos := re_of_cos_sub_I_sin c σ
  have hneg := re_of_cos_add_I_sin c σ
  have hipos := im_of_cos_sub_I_sin c σ
  have hineg := im_of_cos_add_I_sin c σ
  rw [add_im, add_im, add_im, mul_im, mul_im, mul_im, mul_im]
  simp only [natCast_re, natCast_im, hpos, hneg, hipos, hineg, one_re, one_im,
    neg_re, neg_im]
  ring

/-- `[P, Lean]` `‖F‖ ≥ (1 / 34) / N³` at `q = (4,3,0)`. -/
theorem norm_structureFactor_ge_c0_div_N_pow_three_at_430
    {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    c0_430 / (N : ℝ) ^ 3 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) q430‖ := by
  set a := countT qZ430 s 7 + countT qZ430 s (-7)
  set b := countT qZ430 s 1
  set b' := countT qZ430 s (-1)
  have hcard : a + b + b' = N := by
    have := countT_430_add s hs
    unfold a; omega
  set S := (∑ k : Fin N,
      exp (2 * Real.pi * I * dot3 q430 (centroidPoint (n k) (s k))))
  have hnormF := norm_structureFactor_eq_div hN n s q430
  have hre : S.re =
      -((a : ℝ)) + ((b : ℝ) + (b' : ℝ)) * Real.cos (Real.pi / 7) := by
    have := re_sum_eq_430 n s hs
    unfold a at *
    convert this using 1
    push_cast
    ring
  have him : S.im = ((b' : ℝ) - (b : ℝ)) * sθ' := by
    have := im_sum_eq_430 n s hs
    rw [sin_pi_div_seven] at this
    exact this
  have hre_of_eq : b = b' →
      |S.re| = |((a : ℝ) + (2 * (b : ℝ)) * cθ')| := by
    intro hbb
    have hrew : S.re = -((a : ℝ) + (2 * (b : ℝ)) * cθ') := by
      rw [hre, hbb, cos_pi_div_seven]
      ring
    rw [hrew, abs_neg]
  have hlin : ∀ (p q : ℤ), q ≠ 0 →
      |((p : ℝ) + (q : ℝ) * cθ')| < 1 →
        1 / (34 * (q : ℝ) ^ 2) ≤ |((p : ℝ) + (q : ℝ) * cθ')| :=
    LeanLab.Scratch.LemmaDLowerBound330Sharper.abs_linform_ge_of_small
  have hmain :=
    norm_ge_c0_div_N3_of_counts hN a b b' hcard cθ' sθ' 34 c0_430 (2 / 5) S
      hre_of_eq him (by norm_num) sθ'_ge_two_div_five (by norm_num) rfl
      hlin (by norm_num)
  rw [hnormF]
  exact hmain

theorem normSq_structureFactor_ge_c0_sq_div_N_pow_six_at_430
    {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    c0_430 ^ 2 / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) q430‖ ^ 2 := by
  have h := norm_structureFactor_ge_c0_div_N_pow_three_at_430 hN n s hs
  have hnn : 0 ≤ c0_430 / (N : ℝ) ^ 3 := by unfold c0_430; positivity
  have hF : 0 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) q430‖ :=
    norm_nonneg _
  have hsq := mul_le_mul h h hnn hF
  have hL : (c0_430 / (N : ℝ) ^ 3) * (c0_430 / (N : ℝ) ^ 3) =
      c0_430 ^ 2 / (N : ℝ) ^ 6 := by field_simp
  have hR : ‖structureFactor (fun k => centroidPoint (n k) (s k)) q430‖ *
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) q430‖ =
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) q430‖ ^ 2 := by
    ring
  rwa [hL, hR] at hsq


#print axioms gR_c2_eq_zero
#print axioms abs_hR_lt_thirtyeight
#print axioms norm_structureFactor_ge_c0_div_N_pow_three_at_110
#print axioms normSq_structureFactor_ge_c0_sq_div_N_pow_six_at_110
#print axioms norm_structureFactor_ge_c0_div_N_pow_three_at_610
#print axioms normSq_structureFactor_ge_c0_sq_div_N_pow_six_at_610
#print axioms norm_structureFactor_ge_c0_div_N_pow_three_at_520
#print axioms normSq_structureFactor_ge_c0_sq_div_N_pow_six_at_520
#print axioms norm_structureFactor_ge_c0_div_N_pow_three_at_430
#print axioms normSq_structureFactor_ge_c0_sq_div_N_pow_six_at_430

end LeanLab.Scratch.LemmaDLowerBoundL1SevenCubic
