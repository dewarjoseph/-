import Mathlib

/-!
# Chair44 Lemma D4: equal-weight average of box intensities
(public-screen)

Public-screen v2 copy of LeanLab.Scratch.LemmaD4 (official pin src
`f55f3bbea8023c14f21e7ff42b891b89f79dd4a520392f66a553c0c2ccf6f80a`).
Header redacted; theorem bodies are unchanged. This copy is not a
replacement pin.

Displayed D4: M≥1 boxes; box sizes `N : Fin M → ℕ` with `∀ B, 1 ≤ N B`;
per box, points `r_B,k = n_B,k − s_B,k/14` with `n` integer-valued and
`s B k j = 1 ∨ s B k j = -1`; box intensity `I_B = ‖F_B(e_a)‖²`; equal-weight
average `I(e_a) = M⁻¹ Σ_B I_B`. Then `cos²(π/7) ≤ I(e_a) ≤ 1`. Also the
exact average identity from D2:
`I(e_a) = cos²(π/7) + M⁻¹ Σ_B μ_{B,a}² sin²(π/7)`.

This file is a standalone copy of D1–D3 from LemmaD (official pin src
`ecef2a10bd37fdb3ebfe32052166a80d33d65dc9aeffbbc6b703fb1bad472990`;
with only the namespace renamed), then D4.

Fidelity:
* Integer `lo_B` only (hypothesis form absorbs only an integer box origin into `n`);
  non-integer shifts are not claimed.
* `b=1` and the 13/14 centroid geometry are not encoded.
* No `I(e_a)=I(0)`, tails, fade, or hull.
* Scratch only; not a Lake target; not peer reviewed.

This file is source-only and is not a Lake package. It claims nothing
beyond the theorems stated below.

Dated 2026-11-10.
-/

namespace LeanLab.Scratch.LemmaD4

open Complex Finset

/-- Explicit ℝ³ Euclidean dot product (standalone copy; not imported from Lemma A). -/
def dot3 (q x : Fin 3 → ℝ) : ℝ :=
  ∑ i : Fin 3, q i * x i

/-- Structure factor at a wavevector: `F(q) = (1/N) Σ_k exp(2 π i q · r_k)`. -/
noncomputable def structureFactor {N : ℕ} (r : Fin N → Fin 3 → ℝ) (q : Fin 3 → ℝ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ k : Fin N, exp (2 * Real.pi * I * (dot3 q (r k)))

/-- Mean sign on coordinate `a`: `μ_a = N⁻¹ Σ_k s_{k,a}`. -/
noncomputable def meanSign {N : ℕ} (s : Fin N → Fin 3 → ℤ) (a : Fin 3) : ℝ :=
  (N : ℝ)⁻¹ * ∑ k : Fin N, (s k a : ℝ)

/-- Point of the hypothesis form `r = n − s/14`. -/
noncomputable def centroidPoint (n : Fin 3 → ℤ) (s : Fin 3 → ℤ) : Fin 3 → ℝ :=
  fun j => (n j : ℝ) - (s j : ℝ) / 14

/-- Unit vector `e_a`. -/
noncomputable def eVec (a : Fin 3) : Fin 3 → ℝ :=
  Pi.single a (1 : ℝ)

lemma dot3_eVec (a : Fin 3) (x : Fin 3 → ℝ) :
    dot3 (eVec a) x = x a := by
  simp [dot3, eVec, Pi.single_apply]

/-- Integer phase factor: `exp(2 π i n) = 1` for `n : ℤ`. -/
lemma exp_two_pi_I_int (n : ℤ) :
    exp (2 * Real.pi * I * (n : ℝ)) = 1 := by
  have h : (2 * Real.pi * I * (n : ℝ) : ℂ) = (n : ℂ) * (2 * Real.pi * I) := by
    push_cast; ring
  rw [h]; simpa [mul_assoc] using Complex.exp_int_mul_two_pi_mul_I n

/-- One summand at `e_a`: `exp(2 π i e_a · (n − s/14)) = cos(π/7) − i s_a sin(π/7)`. -/
lemma exp_centroid_at_e (n : Fin 3 → ℤ) (s : Fin 3 → ℤ) (a : Fin 3)
    (hs : s a = 1 ∨ s a = -1) :
    exp (2 * Real.pi * I * dot3 (eVec a) (centroidPoint n s)) =
      (Real.cos (Real.pi / 7) : ℂ) - I * (s a : ℝ) * Real.sin (Real.pi / 7) := by
  rw [dot3_eVec, centroidPoint]
  rcases hs with hs | hs
  · rw [hs]
    convert_to exp ((2 * Real.pi * I * (n a : ℝ) : ℂ) + ((-(Real.pi / 7) : ℂ) * I)) = _
      using 1
    · push_cast; ring
    rw [exp_add, exp_two_pi_I_int (n a), one_mul, Complex.exp_mul_I]
    simp [ofReal_cos, ofReal_sin]
    ring
  · rw [hs]
    convert_to exp ((2 * Real.pi * I * (n a : ℝ) : ℂ) + (((Real.pi / 7) : ℂ) * I)) = _
      using 1
    · push_cast; ring
    rw [exp_add, exp_two_pi_I_int (n a), one_mul, Complex.exp_mul_I]
    simp [ofReal_cos, ofReal_sin]
    ring

/-- (D1) Closed form for `F(e_a)`. -/
theorem structureFactor_e_eq {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) (a : Fin 3) :
    structureFactor (fun k => centroidPoint (n k) (s k)) (eVec a) =
      (Real.cos (Real.pi / 7) : ℂ) - I * meanSign s a * Real.sin (Real.pi / 7) := by
  have hNne : (N : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (Nat.zero_lt_of_lt hN))
  unfold structureFactor meanSign
  have hterm : ∀ k, exp (2 * Real.pi * I * dot3 (eVec a) (centroidPoint (n k) (s k))) =
      (Real.cos (Real.pi / 7) : ℂ) - I * (s k a : ℝ) * Real.sin (Real.pi / 7) :=
    fun k => exp_centroid_at_e (n k) (s k) a (hs k a)
  simp_rw [hterm]
  set c : ℂ := (Real.cos (Real.pi / 7) : ℂ)
  set σ : ℂ := (Real.sin (Real.pi / 7) : ℂ)
  have hsummand : ∀ k, c - I * (s k a : ℝ) * σ = c + (-I * σ) * (s k a : ℝ) := by
    intro k; ring
  simp_rw [hsummand]
  rw [sum_add_distrib, sum_const, nsmul_eq_mul, ← mul_sum]
  have : (N : ℂ)⁻¹ * ((N : ℂ) * c + (-I * σ) * ∑ k : Fin N, (s k a : ℝ)) =
      c - I * (((N : ℝ)⁻¹ * ∑ k : Fin N, (s k a : ℝ) : ℝ) : ℂ) * σ := by
    have hcast : (((N : ℝ)⁻¹ * ∑ k : Fin N, (s k a : ℝ) : ℝ) : ℂ) =
        (N : ℂ)⁻¹ * ∑ k : Fin N, (s k a : ℝ) := by
      push_cast; rfl
    calc
      (N : ℂ)⁻¹ * ((N : ℂ) * c + (-I * σ) * ∑ k : Fin N, (s k a : ℝ))
          = (N : ℂ)⁻¹ * (N : ℂ) * c +
              (N : ℂ)⁻¹ * ((-I * σ) * ∑ k : Fin N, (s k a : ℝ)) := by ring
      _ = c + (N : ℂ)⁻¹ * (-I * σ) * ∑ k : Fin N, (s k a : ℝ) := by
            field_simp [hNne]
      _ = c + (-I * σ) * ((N : ℂ)⁻¹ * ∑ k : Fin N, (s k a : ℝ)) := by ring
      _ = c + (-I * σ) * (((N : ℝ)⁻¹ * ∑ k : Fin N, (s k a : ℝ) : ℝ) : ℂ) := by
            rw [hcast]
      _ = c - I * (((N : ℝ)⁻¹ * ∑ k : Fin N, (s k a : ℝ) : ℝ) : ℂ) * σ := by ring
  simpa [c, σ] using this

/-- Helper: ‖c − i t‖² = c² + t² for real c, t. -/
lemma norm_sq_cos_sub_I_mul (c t : ℝ) :
    ‖(c : ℂ) - I * (t : ℂ)‖ ^ 2 = c ^ 2 + t ^ 2 := by
  have hn : ‖(c : ℂ) - I * (t : ℂ)‖ ^ 2 =
      ((c : ℂ) - I * t).re ^ 2 + ((c : ℂ) - I * t).im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  simp [hn, sub_re, sub_im, mul_re, mul_im, I_re, I_im]

/-- (D2) Squared modulus closed form. -/
theorem normSq_structureFactor_e {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) (a : Fin 3) :
    ‖structureFactor (fun k => centroidPoint (n k) (s k)) (eVec a)‖ ^ 2 =
      Real.cos (Real.pi / 7) ^ 2 +
        meanSign s a ^ 2 * Real.sin (Real.pi / 7) ^ 2 := by
  rw [structureFactor_e_eq hN n s hs a]
  have hform :
      ((Real.cos (Real.pi / 7) : ℂ) - I * meanSign s a * Real.sin (Real.pi / 7)) =
        (Real.cos (Real.pi / 7) : ℂ) -
          I * ((meanSign s a * Real.sin (Real.pi / 7) : ℝ) : ℂ) := by
    push_cast; ring
  rw [hform, norm_sq_cos_sub_I_mul]; ring

/-- Mean sign squared is at most 1. -/
lemma meanSign_sq_le_one {N : ℕ} (hN : 1 ≤ N)
    (s : Fin N → Fin 3 → ℤ) (hs : ∀ k j, s k j = 1 ∨ s k j = -1)
    (a : Fin 3) :
    meanSign s a ^ 2 ≤ 1 := by
  have habs : ∀ k : Fin N, |(s k a : ℝ)| = 1 := by
    intro k; rcases hs k a with h | h <;> simp [h]
  have hsum : |∑ k : Fin N, (s k a : ℝ)| ≤ (N : ℝ) := by
    calc
      |∑ k : Fin N, (s k a : ℝ)| ≤ ∑ k : Fin N, |(s k a : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = (N : ℝ) := by simp [habs]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hN)
  have hmu : |meanSign s a| ≤ 1 := by
    unfold meanSign
    rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (le_of_lt hNpos))]
    have : (N : ℝ)⁻¹ * |∑ k : Fin N, (s k a : ℝ)| ≤ (N : ℝ)⁻¹ * N := by gcongr
    rwa [inv_mul_cancel₀ (ne_of_gt hNpos)] at this
  have := abs_le.mp hmu
  nlinarith

/-- (D3) Two-sided bound. -/
theorem cos_sq_le_normSq_structureFactor_e_le_one {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) (a : Fin 3) :
    Real.cos (Real.pi / 7) ^ 2 ≤
        ‖structureFactor (fun k => centroidPoint (n k) (s k)) (eVec a)‖ ^ 2 ∧
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) (eVec a)‖ ^ 2 ≤ 1 := by
  rw [normSq_structureFactor_e hN n s hs a]
  have hmu : meanSign s a ^ 2 ≤ 1 := meanSign_sq_le_one hN s hs a
  have hsin : 0 ≤ Real.sin (Real.pi / 7) ^ 2 := sq_nonneg _
  have htrig : Real.cos (Real.pi / 7) ^ 2 + Real.sin (Real.pi / 7) ^ 2 = 1 :=
    Real.cos_sq_add_sin_sq _
  constructor
  · nlinarith
  · nlinarith

/-- Combined D1–D3. -/
theorem lemma_D {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) (a : Fin 3) :
    structureFactor (fun k => centroidPoint (n k) (s k)) (eVec a) =
        (Real.cos (Real.pi / 7) : ℂ) -
          I * meanSign s a * Real.sin (Real.pi / 7) ∧
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) (eVec a)‖ ^ 2 =
        Real.cos (Real.pi / 7) ^ 2 +
          meanSign s a ^ 2 * Real.sin (Real.pi / 7) ^ 2 ∧
      Real.cos (Real.pi / 7) ^ 2 ≤
          ‖structureFactor (fun k => centroidPoint (n k) (s k)) (eVec a)‖ ^ 2 ∧
        ‖structureFactor (fun k => centroidPoint (n k) (s k)) (eVec a)‖ ^ 2 ≤ 1 :=
  ⟨structureFactor_e_eq hN n s hs a,
    normSq_structureFactor_e hN n s hs a,
    (cos_sq_le_normSq_structureFactor_e_le_one hN n s hs a).1,
    (cos_sq_le_normSq_structureFactor_e_le_one hN n s hs a).2⟩

#print axioms structureFactor_e_eq
#print axioms normSq_structureFactor_e
#print axioms meanSign_sq_le_one
#print axioms cos_sq_le_normSq_structureFactor_e_le_one
#print axioms lemma_D


/-! ## D4: equal-weight average of box intensities -/

/-- Equal-weight average of reals stays inside a common closed interval. -/
lemma avg_mem_Icc {M : ℕ} (hM : 1 ≤ M) (x : Fin M → ℝ) (lo hi : ℝ)
    (hx : ∀ B, lo ≤ x B ∧ x B ≤ hi) :
    lo ≤ (M : ℝ)⁻¹ * ∑ B : Fin M, x B ∧
      (M : ℝ)⁻¹ * ∑ B : Fin M, x B ≤ hi := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hM)
  have hsum_lo : (M : ℝ) * lo ≤ ∑ B : Fin M, x B := by
    have : ∑ B : Fin M, lo ≤ ∑ B : Fin M, x B :=
      Finset.sum_le_sum fun B _ => (hx B).1
    simpa [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] using this
  have hsum_hi : ∑ B : Fin M, x B ≤ (M : ℝ) * hi := by
    have : ∑ B : Fin M, x B ≤ ∑ B : Fin M, hi :=
      Finset.sum_le_sum fun B _ => (hx B).2
    simpa [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] using this
  constructor
  · rw [le_inv_mul_iff₀ hMpos]; exact hsum_lo
  · rw [inv_mul_le_iff₀ hMpos]; exact hsum_hi

/-- Exact average identity from D2: averaged intensity equals
`cos²(π/7) + M⁻¹ Σ_B μ_{B,a}² sin²(π/7)`. -/
theorem avg_normSq_structureFactor_e_eq {M : ℕ} (hM : 1 ≤ M)
    (N : Fin M → ℕ) (hN : ∀ B, 1 ≤ N B)
    (n : (B : Fin M) → Fin (N B) → Fin 3 → ℤ)
    (s : (B : Fin M) → Fin (N B) → Fin 3 → ℤ)
    (hs : ∀ B k j, s B k j = 1 ∨ s B k j = -1)
    (a : Fin 3) :
    (M : ℝ)⁻¹ * ∑ B : Fin M,
        ‖structureFactor (fun k => centroidPoint (n B k) (s B k)) (eVec a)‖ ^ 2 =
      Real.cos (Real.pi / 7) ^ 2 +
        (M : ℝ)⁻¹ * ∑ B : Fin M,
          meanSign (s B) a ^ 2 * Real.sin (Real.pi / 7) ^ 2 := by
  have hterm : ∀ B,
      ‖structureFactor (fun k => centroidPoint (n B k) (s B k)) (eVec a)‖ ^ 2 =
        Real.cos (Real.pi / 7) ^ 2 +
          meanSign (s B) a ^ 2 * Real.sin (Real.pi / 7) ^ 2 :=
    fun B => normSq_structureFactor_e (hN B) (n B) (s B) (hs B) a
  simp_rw [hterm]
  set c : ℝ := Real.cos (Real.pi / 7) ^ 2
  set t : Fin M → ℝ := fun B =>
    meanSign (s B) a ^ 2 * Real.sin (Real.pi / 7) ^ 2
  have hMne : (M : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (Nat.zero_lt_of_lt hM))
  calc
    (M : ℝ)⁻¹ * ∑ B : Fin M, (c + t B)
        = (M : ℝ)⁻¹ * (∑ B : Fin M, c + ∑ B : Fin M, t B) := by
            rw [sum_add_distrib]
    _ = (M : ℝ)⁻¹ * ((M : ℝ) * c + ∑ B : Fin M, t B) := by
            simp [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = (M : ℝ)⁻¹ * (M : ℝ) * c + (M : ℝ)⁻¹ * ∑ B : Fin M, t B := by ring
    _ = c + (M : ℝ)⁻¹ * ∑ B : Fin M, t B := by field_simp [hMne]

/-- (D4) Equal-weight average of box intensities each satisfying D3 stays in
`[cos²(π/7), 1]`. -/
theorem lemma_D4 {M : ℕ} (hM : 1 ≤ M)
    (N : Fin M → ℕ) (hN : ∀ B, 1 ≤ N B)
    (n : (B : Fin M) → Fin (N B) → Fin 3 → ℤ)
    (s : (B : Fin M) → Fin (N B) → Fin 3 → ℤ)
    (hs : ∀ B k j, s B k j = 1 ∨ s B k j = -1)
    (a : Fin 3) :
    Real.cos (Real.pi / 7) ^ 2 ≤
        (M : ℝ)⁻¹ * ∑ B : Fin M,
          ‖structureFactor (fun k => centroidPoint (n B k) (s B k)) (eVec a)‖ ^ 2 ∧
      (M : ℝ)⁻¹ * ∑ B : Fin M,
          ‖structureFactor (fun k => centroidPoint (n B k) (s B k)) (eVec a)‖ ^ 2 ≤ 1 := by
  set I : Fin M → ℝ := fun B =>
    ‖structureFactor (fun k => centroidPoint (n B k) (s B k)) (eVec a)‖ ^ 2
  have hx : ∀ B, Real.cos (Real.pi / 7) ^ 2 ≤ I B ∧ I B ≤ 1 := by
    intro B
    exact cos_sq_le_normSq_structureFactor_e_le_one (hN B) (n B) (s B) (hs B) a
  simpa [I] using avg_mem_Icc hM I (Real.cos (Real.pi / 7) ^ 2) 1 hx

#print axioms avg_mem_Icc
#print axioms avg_normSq_structureFactor_e_eq
#print axioms lemma_D4

end LeanLab.Scratch.LemmaD4
