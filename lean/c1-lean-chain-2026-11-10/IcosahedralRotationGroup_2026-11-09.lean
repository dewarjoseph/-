/-
Scratch model of the icosahedral rotation group, dated 2026-11-09.
Not a Lake target. Not peer reviewed.

Intended model: the stabilizer, in Mathlib's
`Matrix.specialOrthogonalGroup (Fin 3) ℝ`, of the usual vertex set
of a regular icosahedron (cyclic permutations of `(0, ±1, ±φ)`,
with `φ = Real.goldenRatio`). Chosen because Mathlib already defines
`specialOrthogonalGroup` and `goldenRatio`, and this is the concrete
rotation group used in ToE C1/C4. Mathlib has no ready-made
icosahedral group, and `CoxeterMatrix.H₃` is only a Coxeter matrix
(that file does not prove finiteness or the identification).

This file proves only that the stabilizer is a subgroup. It does not
prove that the vertex set has twelve elements, that the group has
order 60, or that it is isomorphic to `alternatingGroup (Fin 5)`.
Those gaps are the missing piece; `I ≅ A₅` stays `[X]` as a Lean
statement.
-/

import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Data.Fin.VecNotation

open Matrix

attribute [local instance] starRingOfComm

/-- Cyclic permutations of `(0, ±1, ±φ)`. The usual vertices of a regular icosahedron. -/
def icosahedronVertexSet : Set (Fin 3 → ℝ) :=
  { v | ∃ a b : ℝ, (a = 1 ∨ a = -1) ∧ (b = 1 ∨ b = -1) ∧
      (v = ![0, a, b * Real.goldenRatio] ∨
        v = ![b * Real.goldenRatio, 0, a] ∨
        v = ![a, b * Real.goldenRatio, 0]) }

/-- An element of `SO(3, ℝ)` permutes the vertex set. -/
def mem_icosahedralRotationGroup (A : specialOrthogonalGroup (Fin 3) ℝ) : Prop :=
  (fun v => (A : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v) '' icosahedronVertexSet =
    icosahedronVertexSet

lemma coe_mul_mulVec (A B : specialOrthogonalGroup (Fin 3) ℝ) (v : Fin 3 → ℝ) :
    ((A * B : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v =
      (A : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ ((B : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v) := by
  change ((A : Matrix (Fin 3) (Fin 3) ℝ) * (B : Matrix (Fin 3) (Fin 3) ℝ)) *ᵥ v = _
  rw [← mulVec_mulVec]

lemma coe_inv_mul_self_eq_one (A : specialOrthogonalGroup (Fin 3) ℝ) :
    ((A⁻¹ : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *
      (A : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
  -- Inverse in `specialOrthogonalGroup` is `star`, and membership in the
  -- unitary group gives `star A.1 * A.1 = 1`.
  rw [← star_eq_inv A, specialUnitaryGroup.coe_star A]
  exact A.prop.1.1

lemma coe_inv_mul_mulVec (A : specialOrthogonalGroup (Fin 3) ℝ) (v : Fin 3 → ℝ) :
    ((A⁻¹ : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ
      ((A : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v) = v := by
  rw [mulVec_mulVec, coe_inv_mul_self_eq_one, one_mulVec]

/-- The intended concrete model of the icosahedral rotation group:
the stabilizer of `icosahedronVertexSet` in `SO(3, ℝ)`. -/
def icosahedralRotationGroup : Subgroup (specialOrthogonalGroup (Fin 3) ℝ) where
  carrier := { A | mem_icosahedralRotationGroup A }
  one_mem' := by
    change mem_icosahedralRotationGroup 1
    unfold mem_icosahedralRotationGroup
    have : (fun v => ((1 : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v) =
        id := by
      funext v
      change (1 : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v = v
      exact one_mulVec v
    rw [this, Set.image_id]
  mul_mem' := by
    intro A B hA hB
    change mem_icosahedralRotationGroup (A * B)
    unfold mem_icosahedralRotationGroup at *
    have : (fun v => ((A * B : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v) =
        (fun v => (A : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ ((B : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v)) :=
      funext (fun v => coe_mul_mulVec A B v)
    rw [this, ← Set.image_image, hB, hA]
  inv_mem' := by
    intro A hA
    change mem_icosahedralRotationGroup A⁻¹
    unfold mem_icosahedralRotationGroup at *
    have hL :
        (fun v => ((A⁻¹ : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v) ''
          ((fun v => (A : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v) '' icosahedronVertexSet) =
          icosahedronVertexSet := by
      rw [Set.image_image]
      have : (fun x =>
          ((A⁻¹ : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ
            ((A : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ x)) = id :=
        funext (fun v => coe_inv_mul_mulVec A v)
      rw [this, Set.image_id]
    rwa [hA] at hL

/-- Membership in the intended model is exactly the vertex-set stabilizer condition. -/
theorem mem_icosahedralRotationGroup_iff (A : specialOrthogonalGroup (Fin 3) ℝ) :
    A ∈ icosahedralRotationGroup ↔ mem_icosahedralRotationGroup A :=
  Iff.rfl

#print axioms mem_icosahedralRotationGroup_iff
#print axioms icosahedralRotationGroup
#print axioms coe_inv_mul_mulVec
