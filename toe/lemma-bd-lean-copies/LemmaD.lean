import Mathlib

/-!
# Chair44 Lemma D: finite chair-centroid integer-peak bound (scratch)

Source: `/home/box/shared/theory-of-everything/chair44-antidiagonal-mechanism-2026-11-07.md`
sha256 `08e4ceed4c1c9b1a4cb9e15b3af5484550636dfe377bb124409761f932cb7e64`, §6 Lemma D.
QIS scoping `/home/box/shared/qis-eth/lean/lemmas-b-d-statement-dependencies-scoping-2026-11-09.md`
sha256 `c7b46dc3ecd2543b84354315bed5ba93b232bb96c37192bd06fbde40be6e4e93`.

Displayed: N≥1, r_k = n_k − s_k/14 with n_k ∈ Z³, s_k ∈ {−1,+1}³, b=1.
For coordinate a, μ_a = N⁻¹ Σ_k s_{k,a}. Then
  F(e_a) = cos(π/7) − i μ_a sin(π/7),
  |F(e_a)|² = cos²(π/7) + μ_a² sin²(π/7),
  cos²(π/7) ≤ |F(e_a)|² ≤ 1.

Fidelity:
* Hypothesis form is `r k j = (n k j : ℝ) − (s k j : ℝ)/14` with
  `∀ k j, s k j = 1 ∨ s k j = -1`. This absorbs an **integer** box origin
  `lo_B` into `n` (as §2 says); it does **not** claim to cover a non-integer shift.
* `b=1` unused and not encoded. The 13/14 centroid geometry is not encoded.
* No statement at non-integer q; no `I(e_a)=I(0)`, tails, fade, or hull.
* Standalone: copies a small `dot3`; does not import LemmaA.lean.
* D4 (equal-weight average of boxes) is **skipped** here to keep the file focused
  on D1–D3 (would be a short separate corollary; omitted by choice).
* Scratch only; not a Lake target; not peer reviewed. Licenses nothing about
  ScaleLiftToRAM, PrimToRAM, ETH, R2/R4/R5, fade, CH-V-020, or Theorem F.
-/

namespace LeanLab.Scratch.LemmaD

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

end LeanLab.Scratch.LemmaD
