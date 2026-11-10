import Mathlib

/-!
# Chair44 Lemma A: finite normalized-average intensity bounds (scratch)

Source: `/home/box/shared/theory-of-everything/chair44-antidiagonal-mechanism-2026-11-07.md`
sha256 `08e4ceed4c1c9b1a4cb9e15b3af5484550636dfe377bb124409761f932cb7e64`, §6 Lemma A
(and §1 definitions). QIS scoping note
`/home/box/shared/qis-eth/lean/lemma-a-statement-dependencies-scoping-2026-11-09.md`
sha256 `3fc669088dd5a35321bd9c6a7d78e78761ed9815f89c92d8520e939cd6e6fb8f`.

Displayed statement (source §6): Let M≥1, each N_B≥1, r_{B,k} in R³, b=1, and
F_B, I as in §1. For every real q, 0 ≤ I(q) ≤ 1 and I(0) = 1.

§1 definitions:
  F_B(q) = (1/N_B) Σ_k exp(2 π i q·(r_{B,k} − lo_B))
  I(q)   = (1/M) Σ_B |F_B(q)|²   (equal box weights, not N_B-weighted)

Fidelity choices (match QIS scoping, do not strengthen/weaken):
* Positions are `Fin 3 → ℝ` with explicit Euclidean dot product `Σ_i q_i x_i`
  (not `EuclideanSpace`).
* The box origin shift `lo_B` is absorbed into the arbitrary real points
  `r_{B,k}` (QIS §2: both covered by quantifying over arbitrary reals).
* The source mentions `b=1` but never uses it in the bounds; it is not encoded.
* Hypotheses `1 ≤ M` and `1 ≤ N B` are exactly the source's M≥1, N_B≥1
  (needed for nonempty averages / nonzero denominators).

This file is scratch only: not in any Lake target, not peer reviewed. It proves
the finite normalized-average bounds only. It does not license ScaleLiftToRAM,
PrimToRAM, ETH, fade, CH-V-020, Theorem F, or any Chair44 spectral claim.
-/

namespace LeanLab.Scratch.LemmaA

open Complex Finset

/-- Explicit ℝ³ Euclidean dot product: `Σ_{i : Fin 3} q i * x i`. -/
def dot3 (q x : Fin 3 → ℝ) : ℝ :=
  ∑ i : Fin 3, q i * x i

/-- Box structure factor
`F(q) = (1/N) Σ_k exp(2 π i q · r_k)` over a nonempty finite point set.
The §1 shift by `lo_B` is absorbed into the arbitrary real positions. -/
noncomputable def boxStructureFactor {N : ℕ} (r : Fin N → Fin 3 → ℝ)
    (q : Fin 3 → ℝ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ k : Fin N, exp (2 * Real.pi * I * (dot3 q (r k) : ℝ))

/-- Equal-weight average of box intensities
`I(q) = (1/M) Σ_B |F_B(q)|²`. -/
noncomputable def averagedIntensity {M : ℕ} {N : Fin M → ℕ}
    (r : (B : Fin M) → Fin (N B) → Fin 3 → ℝ) (q : Fin 3 → ℝ) : ℝ :=
  (M : ℝ)⁻¹ * ∑ B : Fin M, ‖boxStructureFactor (r B) q‖ ^ 2

/-- Each summand of `F` has complex modulus 1. -/
theorem norm_exp_dot3 (q x : Fin 3 → ℝ) :
    ‖exp (2 * Real.pi * I * (dot3 q x : ℝ))‖ = 1 := by
  -- `‖exp (θ * I)‖ = 1` for real θ; rewrite `2π I · θ = (2π θ) * I`.
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    Complex.norm_exp_ofReal_mul_I (2 * Real.pi * dot3 q x)

/-- Triangle inequality: `|F_B(q)| ≤ 1` whenever `N_B ≥ 1`. -/
theorem norm_boxStructureFactor_le_one {N : ℕ} (hN : 1 ≤ N)
    (r : Fin N → Fin 3 → ℝ) (q : Fin 3 → ℝ) :
    ‖boxStructureFactor r q‖ ≤ 1 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hN)
  have hInv : ‖(N : ℂ)⁻¹‖ = (N : ℝ)⁻¹ := by
    rw [norm_inv, Complex.norm_natCast]
  calc
    ‖boxStructureFactor r q‖
        = ‖(N : ℂ)⁻¹‖ * ‖∑ k : Fin N, exp (2 * Real.pi * I * (dot3 q (r k) : ℝ))‖ := by
          simp [boxStructureFactor]
    _ = (N : ℝ)⁻¹ *
          ‖∑ k : Fin N, exp (2 * Real.pi * I * (dot3 q (r k) : ℝ))‖ := by
          rw [hInv]
    _ ≤ (N : ℝ)⁻¹ *
          ∑ k : Fin N, ‖exp (2 * Real.pi * I * (dot3 q (r k) : ℝ))‖ := by
          gcongr; exact norm_sum_le _ _
    _ = (N : ℝ)⁻¹ * ∑ k : Fin N, (1 : ℝ) := by
          simp [norm_exp_dot3]
    _ = (N : ℝ)⁻¹ * N := by
          simp
    _ = 1 := by
          field_simp

/-- Nonnegativity of `I(q)`. -/
theorem averagedIntensity_nonneg {M : ℕ} {N : Fin M → ℕ}
    (r : (B : Fin M) → Fin (N B) → Fin 3 → ℝ) (q : Fin 3 → ℝ) :
    0 ≤ averagedIntensity r q := by
  refine mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (sum_nonneg ?_)
  intro B _
  exact sq_nonneg _

/-- Upper bound `I(q) ≤ 1` for `M ≥ 1` and each `N_B ≥ 1`. -/
theorem averagedIntensity_le_one {M : ℕ} (hM : 1 ≤ M) {N : Fin M → ℕ}
    (hN : ∀ B, 1 ≤ N B)
    (r : (B : Fin M) → Fin (N B) → Fin 3 → ℝ) (q : Fin 3 → ℝ) :
    averagedIntensity r q ≤ 1 := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hM)
  have hMne : (M : ℝ) ≠ 0 := ne_of_gt hMpos
  have hterm : ∀ B : Fin M, ‖boxStructureFactor (r B) q‖ ^ 2 ≤ 1 := by
    intro B
    have hle := norm_boxStructureFactor_le_one (hN B) (r B) q
    have hnn : 0 ≤ ‖boxStructureFactor (r B) q‖ := norm_nonneg _
    nlinarith [sq_nonneg (‖boxStructureFactor (r B) q‖ - 1)]
  calc
    averagedIntensity r q
        = (M : ℝ)⁻¹ * ∑ B : Fin M, ‖boxStructureFactor (r B) q‖ ^ 2 := rfl
    _ ≤ (M : ℝ)⁻¹ * ∑ B : Fin M, (1 : ℝ) := by
          gcongr; exact hterm _
    _ = (M : ℝ)⁻¹ * M := by simp
    _ = 1 := by field_simp

/-- At `q = 0`, each `F_B(0) = 1`, so `I(0) = 1`. -/
theorem boxStructureFactor_at_zero {N : ℕ} (hN : 1 ≤ N)
    (r : Fin N → Fin 3 → ℝ) :
    boxStructureFactor r (fun _ => 0) = 1 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hN)
  have hNne : (N : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hNpos)
  have hdot : ∀ k : Fin N, dot3 (fun _ => (0 : ℝ)) (r k) = 0 := by
    intro k; simp [dot3]
  simp only [boxStructureFactor, hdot, ofReal_zero, mul_zero, exp_zero]
  -- ∑_k 1 = N, so (N:ℂ)⁻¹ * N = 1
  have hsum : (∑ _k : Fin N, (1 : ℂ)) = (N : ℂ) := by
    simp
  rw [hsum, inv_mul_cancel₀ hNne]

theorem averagedIntensity_at_zero {M : ℕ} (hM : 1 ≤ M) {N : Fin M → ℕ}
    (hN : ∀ B, 1 ≤ N B)
    (r : (B : Fin M) → Fin (N B) → Fin 3 → ℝ) :
    averagedIntensity r (fun _ => 0) = 1 := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hM)
  have hMne : (M : ℝ) ≠ 0 := ne_of_gt hMpos
  have hF : ∀ B : Fin M, ‖boxStructureFactor (r B) (fun _ => 0)‖ ^ 2 = 1 := by
    intro B
    rw [boxStructureFactor_at_zero (hN B) (r B), norm_one, one_pow]
  simp only [averagedIntensity, hF]
  -- (M:ℝ)⁻¹ * Σ 1 = 1
  have hsum : (∑ _B : Fin M, (1 : ℝ)) = (M : ℝ) := by simp
  rw [hsum]; field_simp

/-- Combined Lemma A statement: `0 ≤ I(q) ≤ 1` and `I(0) = 1`. -/
theorem lemma_A {M : ℕ} (hM : 1 ≤ M) {N : Fin M → ℕ} (hN : ∀ B, 1 ≤ N B)
    (r : (B : Fin M) → Fin (N B) → Fin 3 → ℝ) (q : Fin 3 → ℝ) :
    0 ≤ averagedIntensity r q ∧ averagedIntensity r q ≤ 1 ∧
      averagedIntensity r (fun _ => 0) = 1 :=
  ⟨averagedIntensity_nonneg r q,
    averagedIntensity_le_one hM hN r q,
    averagedIntensity_at_zero hM hN r⟩

#print axioms norm_boxStructureFactor_le_one
#print axioms averagedIntensity_nonneg
#print axioms averagedIntensity_le_one
#print axioms boxStructureFactor_at_zero
#print axioms averagedIntensity_at_zero
#print axioms lemma_A

end LeanLab.Scratch.LemmaA
