/-
Scratch file, dated 2026-11-10. Not a Lake target. Not peer reviewed.

Generic extras: extreme points of equal-norm sets, and a free orbit of size 60 under the
official icosahedral rotation group. Statement text was frozen before proving.

Imports `IcosahedralAbstractions_2026-11-10` (src dc045da6…) unchanged. No existing file is edited.
-/
import «IcosahedralAbstractions_2026-11-10»
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.LinearAlgebra.Matrix.DotProduct

open Equiv Matrix

/-! ## (1) Equal-norm sets -/

theorem combo_dot_identity {n : Type*} [Fintype n] (y z : n → ℝ) {a b : ℝ} (hab : a + b = 1) :
    (a • y + b • z) ⬝ᵥ (a • y + b • z) =
      a * (y ⬝ᵥ y) + b * (z ⬝ᵥ z) - a * b * ((y - z) ⬝ᵥ (y - z)) := by
  have hb : b = 1 - a := by linarith
  subst hb
  simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, sub_dotProduct,
    dotProduct_sub, smul_eq_mul, dotProduct_comm z y]
  ring

theorem dot_self_nonneg' {n : Type*} [Fintype n] (v : n → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

theorem convex_dot_le {n : Type*} [Fintype n] (c : ℝ) : Convex ℝ {y : n → ℝ | y ⬝ᵥ y ≤ c} := by
  intro y hy z hz a b ha hb hab
  simp only [Set.mem_ofPred_eq] at hy hz ⊢
  rw [combo_dot_identity y z hab]
  have h0 := dot_self_nonneg' (y - z)
  have h1 : a * (y ⬝ᵥ y) ≤ a * c := mul_le_mul_of_nonneg_left hy ha
  have h2 : b * (z ⬝ᵥ z) ≤ b * c := mul_le_mul_of_nonneg_left hz hb
  have h3 : 0 ≤ a * b * ((y - z) ⬝ᵥ (y - z)) := mul_nonneg (mul_nonneg ha hb) h0
  have h4 : a * c + b * c = c := by rw [← add_mul, hab, one_mul]
  linarith

theorem mem_extremePoints_convexHull_of_dotProduct_self_eq {n : Type*} [Fintype n]
    {S : Set (n → ℝ)} {c : ℝ} (hS : ∀ y ∈ S, y ⬝ᵥ y = c) {x : n → ℝ} (hx : x ∈ S) :
    x ∈ (convexHull ℝ S).extremePoints ℝ := by
  have hsub : convexHull ℝ S ⊆ {y : n → ℝ | y ⬝ᵥ y ≤ c} :=
    convexHull_min (fun y hy => le_of_eq (hS y hy)) (convex_dot_le c)
  rw [mem_extremePoints]
  refine ⟨subset_convexHull ℝ S hx, ?_⟩
  rintro x₁ h₁ x₂ h₂ ⟨a, b, ha, hb, hab, hcomb⟩
  have e1 : x₁ ⬝ᵥ x₁ ≤ c := hsub h₁
  have e2 : x₂ ⬝ᵥ x₂ ≤ c := hsub h₂
  have ex := hS x hx
  rw [← hcomb, combo_dot_identity x₁ x₂ hab] at ex
  have h0 := dot_self_nonneg' (x₁ - x₂)
  have hab0 : 0 < a * b := mul_pos ha hb
  have hd : (x₁ - x₂) ⬝ᵥ (x₁ - x₂) = 0 := by
    by_contra hne
    have hpos : 0 < (x₁ - x₂) ⬝ᵥ (x₁ - x₂) := lt_of_le_of_ne h0 (Ne.symm hne)
    have h1 : a * (x₁ ⬝ᵥ x₁) ≤ a * c := mul_le_mul_of_nonneg_left e1 ha.le
    have h2 : b * (x₂ ⬝ᵥ x₂) ≤ b * c := mul_le_mul_of_nonneg_left e2 hb.le
    have h3 := mul_pos hab0 hpos
    have h4 : a * c + b * c = c := by rw [← add_mul, hab, one_mul]
    linarith
  have h12 : x₁ = x₂ := sub_eq_zero.mp (dotProduct_self_eq_zero.mp hd)
  subst h12
  have hx1 : x = x₁ := by rw [← hcomb, ← add_smul, hab, one_smul]
  exact ⟨hx1.symm, hx1.symm⟩

theorem extremePoints_convexHull_eq_of_dotProduct_self_eq {n : Type*} [Fintype n]
    {S : Set (n → ℝ)} {c : ℝ} (hS : ∀ y ∈ S, y ⬝ᵥ y = c) :
    (convexHull ℝ S).extremePoints ℝ = S :=
  Set.Subset.antisymm extremePoints_convexHull_subset
    (fun _ hx => mem_extremePoints_convexHull_of_dotProduct_self_eq hS hx)

theorem extremePoints_convexHull_eq_of_norm_eq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {S : Set E} {r : ℝ} (hS : ∀ y ∈ S, ‖y‖ = r) :
    (convexHull ℝ S).extremePoints ℝ = S := by
  refine Set.Subset.antisymm extremePoints_convexHull_subset (fun x hx => ?_)
  have hsub : convexHull ℝ S ⊆ Metric.closedBall 0 r :=
    convexHull_min (fun y hy => by rw [mem_closedBall_zero_iff, hS y hy])
      (convex_closedBall 0 r)
  rw [mem_extremePoints]
  refine ⟨subset_convexHull ℝ S hx, ?_⟩
  rintro x₁ h₁ x₂ h₂ ⟨a, b, ha, hb, hab, hcomb⟩
  have e1 : ‖x₁‖ ≤ r := mem_closedBall_zero_iff.mp (hsub h₁)
  have e2 : ‖x₂‖ ≤ r := mem_closedBall_zero_iff.mp (hsub h₂)
  have h12 : x₁ = x₂ := by
    by_contra hne
    have hlt := norm_combo_lt_of_ne e1 e2 hne ha hb hab
    rw [hcomb, hS x hx] at hlt
    exact lt_irrefl _ hlt
  subst h12
  have hx1 : x = x₁ := by rw [← hcomb, ← add_smul, hab, one_smul]
  exact ⟨hx1.symm, hx1.symm⟩

theorem icosahedronVerticesZsqrt5_dot3 :
    ∀ v ∈ icosahedronVerticesZsqrt5, dot3 v v = ⟨10, 2⟩ := by decide +kernel

theorem icosahedronVertexSet_dotProduct_self :
    ∀ v ∈ icosahedronVertexSet, v ⬝ᵥ v = (5 + Real.sqrt 5) / 2 := by
  intro v hv
  rw [← halveToReal_image_icosahedronVerticesZsqrt5] at hv
  obtain ⟨w, hw, rfl⟩ := hv
  rw [dotProduct_halveToReal, icosahedronVerticesZsqrt5_dot3 w hw, zsqrt5ToReal_apply]
  push_cast
  ring

theorem extremePoints_convexHull_icosahedronVertexSet :
    (convexHull ℝ icosahedronVertexSet).extremePoints ℝ = icosahedronVertexSet :=
  extremePoints_convexHull_eq_of_dotProduct_self_eq icosahedronVertexSet_dotProduct_self

/-! ## (2) Orbits -/

theorem natCard_orbit_of_trivial_stabilizer (p : Fin 3 → ℝ)
    (hp : ∀ g : icosahedralRotationGroup,
      ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ p = p → g = 1) :
    Nat.card (Set.range fun g : icosahedralRotationGroup =>
      ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ p) = 60 := by
  rw [Nat.card_range_of_injective, icosahedralRotationGroup_natCard]
  intro g h hgh
  simp only at hgh
  have key : ((h⁻¹ * g : icosahedralRotationGroup) : specialOrthogonalGroup (Fin 3) ℝ) *ᵥ p = p := by
    have e1 : (((h⁻¹ * g : icosahedralRotationGroup) : specialOrthogonalGroup (Fin 3) ℝ) :
        Matrix (Fin 3) (Fin 3) ℝ) *ᵥ p =
        ((h⁻¹ : icosahedralRotationGroup) : specialOrthogonalGroup (Fin 3) ℝ) *ᵥ
          (((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ p) :=
      coe_mul_mulVec _ _ p
    have e2 : (((h⁻¹ * h : icosahedralRotationGroup) : specialOrthogonalGroup (Fin 3) ℝ) :
        Matrix (Fin 3) (Fin 3) ℝ) *ᵥ p =
        ((h⁻¹ : icosahedralRotationGroup) : specialOrthogonalGroup (Fin 3) ℝ) *ᵥ
          (((h : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ p) :=
      coe_mul_mulVec _ _ p
    rw [e1, hgh, ← e2, inv_mul_cancel]
    exact one_mulVec p
  have := hp _ key
  rw [inv_mul_eq_one] at this
  exact this.symm

/-- The doubled point `(2, 4, 6)` over `ℤ[√5]`. -/
def p246 : Fin 3 → Zsqrt5 := ![2, 4, 6]

theorem p246_fixed_only_by_identity :
    ∀ A ∈ scaledRotationList, A.mulVec p246 = (4 : Zsqrt5) • p246 → A = M3.scal 4 := by
  decide +kernel

theorem halveToReal_p246 : halveToReal p246 = ![1, 2, 3] := by
  funext i
  fin_cases i <;> simp [halveToReal, p246, zsqrt5ToReal_apply] <;> norm_num

theorem stabilizer_trivial_one_two_three : ∀ g : icosahedralRotationGroup,
    ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ ![1, 2, 3] = ![1, 2, 3] →
      g = 1 := by
  intro g hg
  rw [← halveToReal_p246, mulVec_halveToReal_iff] at hg
  have hA := p246_fixed_only_by_identity _ (toM3_mem g) hg
  have hm : ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
    rw [coe_eq_realQuarter_repM3]
    change realQuarter (toM3 g).toMatrix = 1
    rw [hA]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [realQuarter, M3.scal, M3.toMatrix, map_ofNat]
  exact Subtype.ext (Subtype.ext hm)

theorem natCard_orbit_one_two_three :
    Nat.card (Set.range fun g : icosahedralRotationGroup =>
      ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ ![1, 2, 3]) = 60 :=
  natCard_orbit_of_trivial_stabilizer _ stabilizer_trivial_one_two_three

#print axioms mem_extremePoints_convexHull_of_dotProduct_self_eq
#print axioms extremePoints_convexHull_eq_of_dotProduct_self_eq
#print axioms extremePoints_convexHull_eq_of_norm_eq
#print axioms icosahedronVertexSet_dotProduct_self
#print axioms extremePoints_convexHull_icosahedronVertexSet
#print axioms natCard_orbit_of_trivial_stabilizer
#print axioms stabilizer_trivial_one_two_three
#print axioms natCard_orbit_one_two_three
