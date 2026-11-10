import Mathlib

/-!
# Chair44 Lemma A: finite normalized-average intensity bounds
(public-screen)

Public-screen v2 copy of LeanLab.Scratch.LemmaAInt (official pin src
`d0c0078207007a1f893448be8dd5cda9ee613c4aaacfd3aec684d9b31d4a5239`).
Header redacted; theorem bodies are unchanged. This copy is not a
replacement pin.

**LemmaAInt.lean (2026-11-09):** standalone copy of LemmaA.lean (all prior
theorems byte-identical in body; namespace renamed) plus an integer-origin section at the
end: `lemma_A_lo_int` (lo : Fin M → Fin 3 → ℤ) and the bridge `averagedIntensity_lo_dForm_int`
showing that for points of the D-form `n − s/14` an integer origin `lo` is absorbed into the
integer part (`n ↦ n − lo`), so the shifted family is again in D-form with the same signs `s`.
Scratch only; not a Lake target; not peer reviewed. It does not prove or restate any Lemma D/D4
bound; it only exposes the integer-origin absorption D/D4 need from their caller.

Displayed statement: Let M≥1, each N_B≥1, r_{B,k} in R³, b=1, and
F_B, I as below. For every real q, 0 ≤ I(q) ≤ 1 and I(0) = 1.

Definitions:
  F_B(q) = (1/N_B) Σ_k exp(2 π i q·(r_{B,k} − lo_B))
  I(q)   = (1/M) Σ_B |F_B(q)|²   (equal box weights, not N_B-weighted)

Fidelity choices (do not strengthen/weaken):
* Positions are `Fin 3 → ℝ` with explicit Euclidean dot product `Σ_i q_i x_i`
  (not `EuclideanSpace`).
* The primary theorems absorb the box origin shift `lo_B` into arbitrary real
  points `r_{B,k}`. An explicit `lo_B`-form corollary is also
  stated below: `boxStructureFactor_lo` / `averagedIntensity_lo` / `lemma_A_lo`,
  reducing to the absorbed form by `r' B k := r B k - lo B`.
* A parameter `b=1` is mentioned in the informal statement but never used
  in the bounds; it is not encoded.
* Hypotheses `1 ≤ M` and `1 ≤ N B` are exactly M≥1, N_B≥1
  (needed for nonempty averages / nonzero denominators).

This file is source-only and is not a Lake package. It claims nothing
beyond the theorems stated below.

Dated 2026-11-10.
-/

namespace LeanLab.Scratch.LemmaAInt

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

/-- §1 box structure factor with explicit origin shift `lo`:
`F_B(q) = (1/N_B) Σ_k exp(2 π i q · (r_{B,k} − lo_B))`. -/
noncomputable def boxStructureFactor_lo {N : ℕ}
    (r : Fin N → Fin 3 → ℝ) (lo : Fin 3 → ℝ) (q : Fin 3 → ℝ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ k : Fin N, exp (2 * Real.pi * I * (dot3 q (r k - lo) : ℝ))

/-- §1 equal-weight average with explicit box origins `lo B`. -/
noncomputable def averagedIntensity_lo {M : ℕ} {N : Fin M → ℕ}
    (r : (B : Fin M) → Fin (N B) → Fin 3 → ℝ) (lo : Fin M → Fin 3 → ℝ)
    (q : Fin 3 → ℝ) : ℝ :=
  (M : ℝ)⁻¹ * ∑ B : Fin M, ‖boxStructureFactor_lo (r B) (lo B) q‖ ^ 2

/-- Shifting each point by `lo` recovers the absorbed-form `boxStructureFactor`. -/
theorem boxStructureFactor_lo_eq {N : ℕ}
    (r : Fin N → Fin 3 → ℝ) (lo : Fin 3 → ℝ) (q : Fin 3 → ℝ) :
    boxStructureFactor_lo r lo q =
      boxStructureFactor (fun k => r k - lo) q := by
  -- `r k - lo` is pointwise (`Pi.sub` / `Pi.sub_apply`); both defs use that same term.
  simp [boxStructureFactor_lo, boxStructureFactor]

/-- The §1 `lo`-form intensity equals the absorbed-form intensity on shifted points. -/
theorem averagedIntensity_lo_eq {M : ℕ} {N : Fin M → ℕ}
    (r : (B : Fin M) → Fin (N B) → Fin 3 → ℝ) (lo : Fin M → Fin 3 → ℝ)
    (q : Fin 3 → ℝ) :
    averagedIntensity_lo r lo q =
      averagedIntensity (fun B k => r B k - lo B) q := by
  simp [averagedIntensity_lo, averagedIntensity, boxStructureFactor_lo_eq]

/-- Lemma A in the explicit §1 `lo_B` form: corollary of `lemma_A` by
instantiating points as `r B k − lo B`. -/
theorem lemma_A_lo {M : ℕ} (hM : 1 ≤ M) {N : Fin M → ℕ} (hN : ∀ B, 1 ≤ N B)
    (r : (B : Fin M) → Fin (N B) → Fin 3 → ℝ) (lo : Fin M → Fin 3 → ℝ)
    (q : Fin 3 → ℝ) :
    0 ≤ averagedIntensity_lo r lo q ∧ averagedIntensity_lo r lo q ≤ 1 ∧
      averagedIntensity_lo r lo (fun _ => 0) = 1 := by
  simpa [averagedIntensity_lo_eq] using
    lemma_A hM hN (fun B k => r B k - lo B) q

/-- Integer box origins, viewed as real origins. -/
def intOrigin {M : ℕ} (lo : Fin M → Fin 3 → ℤ) : Fin M → Fin 3 → ℝ :=
  fun B j => (lo B j : ℝ)

/-- Lemma A in the §1 `lo_B` form with integer origins `lo B ∈ ℤ³`: instance of `lemma_A_lo`. -/
theorem lemma_A_lo_int {M : ℕ} (hM : 1 ≤ M) {N : Fin M → ℕ} (hN : ∀ B, 1 ≤ N B)
    (r : (B : Fin M) → Fin (N B) → Fin 3 → ℝ) (lo : Fin M → Fin 3 → ℤ)
    (q : Fin 3 → ℝ) :
    0 ≤ averagedIntensity_lo r (intOrigin lo) q ∧ averagedIntensity_lo r (intOrigin lo) q ≤ 1 ∧
      averagedIntensity_lo r (intOrigin lo) (fun _ => 0) = 1 :=
  lemma_A_lo hM hN r (intOrigin lo) q

/-- Point of the D hypothesis form `r = n − s/14` (same shape as `centroidPoint` in LemmaD.lean). -/
noncomputable def dForm (n s : Fin 3 → ℤ) : Fin 3 → ℝ :=
  fun j => (n j : ℝ) - (s j : ℝ) / 14

/-- An integer origin is absorbed into the integer part of a D-form point; signs `s` unchanged. -/
theorem dForm_sub_int (n s lo : Fin 3 → ℤ) :
    dForm n s - (fun j => (lo j : ℝ)) = dForm (n - lo) s := by
  funext j
  simp [dForm]
  ring

/-- For D-form points and integer origins, the §1 `lo_B`-form intensity equals the absorbed-form
intensity of the D-form family with integer parts `n − lo` and the same signs `s`. -/
theorem averagedIntensity_lo_dForm_int {M : ℕ} {N : Fin M → ℕ}
    (n s : (B : Fin M) → Fin (N B) → Fin 3 → ℤ) (lo : Fin M → Fin 3 → ℤ)
    (q : Fin 3 → ℝ) :
    averagedIntensity_lo (fun B k => dForm (n B k) (s B k)) (intOrigin lo) q =
      averagedIntensity (fun B k => dForm (n B k - lo B) (s B k)) q := by
  rw [averagedIntensity_lo_eq]
  congr 2
  funext B k
  exact dForm_sub_int (n B k) (s B k) (lo B)

#print axioms norm_boxStructureFactor_le_one
#print axioms averagedIntensity_nonneg
#print axioms averagedIntensity_le_one
#print axioms boxStructureFactor_at_zero
#print axioms averagedIntensity_at_zero
#print axioms lemma_A
#print axioms boxStructureFactor_lo_eq
#print axioms averagedIntensity_lo_eq
#print axioms lemma_A_lo
#print axioms lemma_A_lo_int
#print axioms dForm_sub_int
#print axioms averagedIntensity_lo_dForm_int

end LeanLab.Scratch.LemmaAInt
