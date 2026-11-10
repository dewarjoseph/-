import LeanLab.Scratch.LemmaDLowerBound330
import LeanLab.Scratch.LemmaDOrbitNoZero
import LeanLab.Scratch.LemmaDL1SevenClassification

/-!
# Conditional `c(κ)/N²` bound at `(3,3,0)` (public-screen copy)

Public-screen copy of FILE G (official pin src
`d6e426acc26a618e8be0a893180825148b16888c740c282cae4bf78009a31dcd`).
Header redacted only; theorem bodies are unchanged. This copy is not
a replacement pin.


**[P, Lean, conditional]** If `cos(6π/7)` is badly approximable with an
explicit positive constant `κ`, then every nonempty equal-weight D-form
box at `q = (3,3,0)` satisfies `‖F‖ ≥ c(κ) / N²`, where
`c(κ) = min(κ, 2/5)`.

The hypothesis is an explicit assumption on the theorem
(`hBA : ∀ (u v : ℤ), v ≠ 0 → κ ≤ |v| * |u + v * cθ'|`). This file
does **not** claim the hypothesis holds, does **not** prove that
`cθ' = cos(6π/7)` is badly approximable, and does **not** inhabit
`hBA`. The hypothesis is an open problem (Khinchin); see
Cao–Erazo–Moreira, arXiv:2602.09700v1.

The reduction reuses LemmaDLowerBound330
identities. Write `a = count(t=0)`, `b = count(t=+6)`,
`b' = count(t=−6)`.

* If `b ≠ b'` (unbalanced), `|Im(N·F)| ≥ sin(6π/7) ≥ 2/5`, so
  `‖F‖ ≥ (2/5)/N`. For every `N ≥ 1` one has
  `(2/5)/N ≥ (2/5)/N²`, hence `‖F‖ ≥ (2/5)/N²`.
* If `b = b'` (symmetric), `N·F = p + q cθ'` with `p = a ≥ 0`,
  `q = 2b ≥ 0` even, and `p + q = N`. If `q ≠ 0`, the hypothesis
  gives `|p + q cθ'| ≥ κ/|q| ≥ κ/N`, so `‖F‖ ≥ κ/N²`. If `q = 0`,
  then `N·F = N` and `‖F‖ = 1 ≥ c(κ)/N²`.
* Combined: `c(κ) = min(κ, 2/5)` works uniformly for all `N ≥ 1`.

The same constant transfers to the full signed-permutation orbit of
`(3,3,0)` by the existing `structureFactor_orbit_pull` relabeling
(same `c(κ)`). Sharpness stays `[X]`. No claim that `κ` is realized,
and no unconditional numeric `c`.

D-form class only. Scratch; not a Lake target of the orientation-phase
worktree; not peer reviewed. Licenses nothing about ETH (false stays
`[X]`), R2/R4/R5, ScaleLiftToRAM, PrimToRAM, CH-V-020, or Theorem F.

Dated 2026-11-09.
-/

namespace LeanLab.Scratch.LemmaDConditionalN2_330

open Complex Equiv
open LeanLab.Scratch.LemmaD4 (structureFactor centroidPoint)
open LeanLab.Scratch.LemmaDIntVec (qReal)
open LeanLab.Scratch.LemmaDL1Six (qZ330 q330)
open LeanLab.Scratch.LemmaDLowerBound330
  (cθ' sθ' sθ'_ge_two_div_five countT countT_add_eq_card
    re_sum_eq im_sum_eq norm_structureFactor_eq)
open LeanLab.Scratch.LemmaDLowerBound220 (abs_one_le_int)
open LeanLab.Scratch.LemmaDOrbitNoZero
  (orbitQ pullVec pullVec_is_sign structureFactor_orbit_pull)
open LeanLab.Scratch.LemmaDL1SevenClassification (qOf)

/-- The explicit constant in the conditional `c(κ)/N²` bound. -/
noncomputable def c_of_kappa (κ : ℝ) : ℝ := min κ (2 / 5)

lemma c_of_kappa_le_kappa (κ : ℝ) : c_of_kappa κ ≤ κ :=
  min_le_left _ _

lemma c_of_kappa_le_two_fifths (κ : ℝ) : c_of_kappa κ ≤ 2 / 5 :=
  min_le_right _ _

lemma c_of_kappa_nonneg {κ : ℝ} (hκ : 0 ≤ κ) : 0 ≤ c_of_kappa κ :=
  le_min hκ (by norm_num : (0 : ℝ) ≤ 2 / 5)

lemma two_fifths_div_N_sq_le_div_N {N : ℕ} (hN : 1 ≤ N) :
    (2 / 5 : ℝ) / (N : ℝ) ^ 2 ≤ (2 / 5 : ℝ) / N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have h25 : (0 : ℝ) ≤ 2 / 5 := by norm_num
  have hle : (1 : ℝ) / (N : ℝ) ^ 2 ≤ 1 / N := by
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hNle : (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith [hN1]
    exact (one_div_le_one_div (sq_pos_of_pos hNpos) hNpos).mpr hNle
  have hL : (2 / 5 : ℝ) / (N : ℝ) ^ 2 = (2 / 5) * (1 / (N : ℝ) ^ 2) := by
    field_simp
  have hR : (2 / 5 : ℝ) / N = (2 / 5) * (1 / N) := by
    field_simp
  rw [hL, hR]
  exact mul_le_mul_of_nonneg_left hle h25

lemma qZ330_eq_qOf : qZ330 = qOf 3 3 0 := by
  ext i; fin_cases i <;> rfl

/-- `[P, Lean, conditional]` If `cθ'` is badly approximable with
constant `κ > 0`, then `‖F‖ ≥ min(κ, 2/5) / N²` at `q = (3,3,0)`. -/
theorem norm_structureFactor_ge_c_of_kappa_div_N_pow_two
    {N : ℕ} (hN : 1 ≤ N) {κ : ℝ} (hκ : 0 < κ)
    (hBA : ∀ (u v : ℤ), v ≠ 0 →
      κ ≤ |(v : ℝ)| * |((u : ℝ) + (v : ℝ) * cθ')|)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    c_of_kappa κ / (N : ℝ) ^ 2 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) q330‖ := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  set a := countT s 0
  set b := countT s 6
  set b' := countT s (-6)
  have hcard : a + b + b' = N := countT_add_eq_card s hs
  set S := (∑ k : Fin N,
      exp (2 * Real.pi * I *
        LeanLab.Scratch.LemmaD4.dot3 q330 (centroidPoint (n k) (s k))))
  have hnormF := norm_structureFactor_eq hN n s
  have hre : S.re = (a : ℝ) + ((b : ℝ) + (b' : ℝ)) * cθ' :=
    re_sum_eq n s hs
  have him : S.im = ((b' : ℝ) - (b : ℝ)) * sθ' :=
    im_sum_eq n s hs
  have hck_le_25 := c_of_kappa_le_two_fifths κ
  have hck_le_κ := c_of_kappa_le_kappa κ
  have hck_nn : 0 ≤ c_of_kappa κ := c_of_kappa_nonneg hκ.le
  have hgoal25 : c_of_kappa κ / (N : ℝ) ^ 2 ≤ (2 / 5 : ℝ) / N :=
    le_trans (div_le_div_of_nonneg_right hck_le_25 (sq_nonneg _))
      (two_fifths_div_N_sq_le_div_N hN)
  by_cases hbb : b = b'
  · -- Symmetric: N·F = p + q cθ'
    have him0 : S.im = 0 := by
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
    rw [hpq]
    by_cases hb0 : b = 0
    · have haN : a = N := by omega
      have : |((p : ℝ) + (q : ℝ) * cθ')| = (N : ℝ) := by
        simp [p, q, hb0, haN]
      rw [this, div_self hNpos.ne']
      have : c_of_kappa κ / (N : ℝ) ^ 2 ≤ 1 := by
        have hle : c_of_kappa κ / (N : ℝ) ^ 2 ≤ (2 / 5 : ℝ) / (N : ℝ) ^ 2 :=
          div_le_div_of_nonneg_right hck_le_25 (sq_nonneg _)
        have h25 : (2 / 5 : ℝ) / (N : ℝ) ^ 2 ≤ 1 := by
          have : (2 / 5 : ℝ) ≤ (N : ℝ) ^ 2 := by
            have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
            nlinarith [hN1]
          exact div_le_one_of_le₀ this (sq_nonneg _)
        exact le_trans hle h25
      exact this
    · have hqne : q ≠ 0 := by
        unfold q
        have : (b : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hb0
        omega
      have hBA' := hBA p q hqne
      have hqabs : |(q : ℝ)| ≤ (N : ℝ) := by
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
      have hqpos : (0 : ℝ) < |(q : ℝ)| :=
        abs_pos.mpr (Int.cast_ne_zero.mpr hqne)
      have hform : κ / |(q : ℝ)| ≤ |((p : ℝ) + (q : ℝ) * cθ')| := by
        rw [div_le_iff₀ hqpos, mul_comm]
        exact hBA'
      have hstep : κ / |(q : ℝ)| / N ≤
          |((p : ℝ) + (q : ℝ) * cθ')| / N :=
        div_le_div_of_nonneg_right hform hNpos.le
      have hκN : κ / (N : ℝ) ^ 2 ≤ κ / |(q : ℝ)| / N := by
        have hL : κ / (N : ℝ) ^ 2 = κ / (N * N) := by ring
        have hR : κ / |(q : ℝ)| / N = κ / (|(q : ℝ)| * N) := by field_simp
        rw [hL, hR]
        have hpos1 : (0 : ℝ) < N * N := by positivity
        have hpos2 : (0 : ℝ) < |(q : ℝ)| * N := by positivity
        rw [div_le_div_iff₀ hpos1 hpos2]
        have : |(q : ℝ)| * N ≤ N * N := by
          exact mul_le_mul_of_nonneg_right hqabs hNpos.le
        nlinarith [hκ.le, this]
      have hck : c_of_kappa κ / (N : ℝ) ^ 2 ≤ κ / (N : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hck_le_κ (sq_nonneg _)
      exact le_trans hck (le_trans hκN hstep)
  · -- Unbalanced: ‖F‖ ≥ (2/5)/N ≥ (2/5)/N² ≥ c(κ)/N²
    have hdiff : (1 : ℝ) ≤ |((b' : ℝ) - (b : ℝ))| := by
      have hne : (b : ℤ) ≠ (b' : ℤ) := Nat.cast_injective.ne hbb
      have hz : ((b' : ℤ) - (b : ℤ)) ≠ 0 := sub_ne_zero.mpr (hne.symm)
      have hle' : (1 : ℝ) ≤ |(((b' : ℤ) - (b : ℤ) : ℤ) : ℝ)| :=
        abs_one_le_int hz
      have hcast : |(((b' : ℤ) - (b : ℤ) : ℤ) : ℝ)| =
          |((b' : ℝ) - (b : ℝ))| := by
        push_cast; rfl
      exact (hcast ▸ hle')
    have himabs : (2 / 5 : ℝ) ≤ |S.im| := by
      rw [him, abs_mul,
        abs_of_pos (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2 / 5)
          sθ'_ge_two_div_five)]
      nlinarith [sθ'_ge_two_div_five, hdiff]
    have hSbound : (2 / 5 : ℝ) ≤ ‖S‖ :=
      le_trans himabs (Complex.abs_im_le_norm S)
    have hle : (2 / 5 : ℝ) / N ≤ ‖S‖ / N :=
      div_le_div_of_nonneg_right hSbound hNpos.le
    rw [hnormF]
    exact le_trans hgoal25 hle

theorem normSq_structureFactor_ge_c_of_kappa_sq_div_N_pow_four
    {N : ℕ} (hN : 1 ≤ N) {κ : ℝ} (hκ : 0 < κ)
    (hBA : ∀ (u v : ℤ), v ≠ 0 →
      κ ≤ |(v : ℝ)| * |((u : ℝ) + (v : ℝ) * cθ')|)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (c_of_kappa κ) ^ 2 / (N : ℝ) ^ 4 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) q330‖ ^ 2 := by
  have h :=
    norm_structureFactor_ge_c_of_kappa_div_N_pow_two hN hκ hBA n s hs
  have hnn : 0 ≤ c_of_kappa κ / (N : ℝ) ^ 2 :=
    div_nonneg (c_of_kappa_nonneg hκ.le) (by positivity)
  have hpow := pow_le_pow_left₀ hnn h (n := 2)
  have hsq : (c_of_kappa κ / (N : ℝ) ^ 2) ^ 2 =
      (c_of_kappa κ) ^ 2 / (N : ℝ) ^ 4 := by field_simp
  rwa [hsq] at hpow

/-- `[P, Lean, conditional]` The same `c(κ)/N²` bound on the full
signed-permutation orbit of `(3,3,0)`. -/
theorem norm_structureFactor_ge_c_of_kappa_div_N_pow_two_orbit
    {N : ℕ} (hN : 1 ≤ N) {κ : ℝ} (hκ : 0 < κ)
    (hBA : ∀ (u v : ℤ), v ≠ 0 →
      κ ≤ |(v : ℝ)| * |((u : ℝ) + (v : ℝ) * cθ')|)
    (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    c_of_kappa κ / (N : ℝ) ^ 2 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (orbitQ (qOf 3 3 0) σ eps))‖ := by
  have hs_pull : ∀ k j,
      pullVec σ eps (s k) j = 1 ∨ pullVec σ eps (s k) j = -1 :=
    fun k => pullVec_is_sign σ eps heps (s k) (hs k)
  have hEq := structureFactor_orbit_pull qZ330 σ eps heps n s
  have hbound :=
    norm_structureFactor_ge_c_of_kappa_div_N_pow_two hN hκ hBA
      (fun k => pullVec σ eps (n k)) (fun k => pullVec σ eps (s k)) hs_pull
  -- q330 = qReal qZ330, and qZ330 = qOf 3 3 0
  have hq : q330 = qReal qZ330 := rfl
  have hEq' :
      structureFactor
          (fun k => centroidPoint (pullVec σ eps (n k)) (pullVec σ eps (s k)))
          q330 =
        structureFactor (fun k => centroidPoint (n k) (s k))
          (qReal (orbitQ (qOf 3 3 0) σ eps)) := by
    simpa [hq, qZ330_eq_qOf] using hEq
  rwa [← hEq']

#print axioms norm_structureFactor_ge_c_of_kappa_div_N_pow_two
#print axioms normSq_structureFactor_ge_c_of_kappa_sq_div_N_pow_four
#print axioms norm_structureFactor_ge_c_of_kappa_div_N_pow_two_orbit

end LeanLab.Scratch.LemmaDConditionalN2_330
