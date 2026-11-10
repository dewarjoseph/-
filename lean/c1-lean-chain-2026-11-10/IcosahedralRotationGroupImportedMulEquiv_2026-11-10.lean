/-
Scratch file, dated 2026-11-10.
Not a Lake target. Not peer reviewed.

This file imports the official 2026-11-09 icosahedral rotation group
module `IcosahedralRotationGroup_2026-11-09`. The names
`icosahedronVertexSet`, `icosahedralRotationGroup` and
`mem_icosahedralRotationGroup_iff` are those imported constants,
not local copies.

The explicit sixty scaled matrices over `ℤ[√5]`, the order-60
arguments, and the transfer onto the official stabilizer are included
in this file. The matrix-list body follows an earlier exact-arithmetic
development, with one change: the real vertex set is the imported
official definition rather than a second local copy. The
multiplicativity section is new to this file.

This file does not prove a homomorphism to `alternatingGroup (Fin 5)`,
and does not prove I ≅ A5.
-/

import «IcosahedralRotationGroup_2026-11-09»
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.IntervalCases
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Algebra.Group.MinimalAxioms

open Zsqrtd Matrix

/-- The integer ring `ℤ[√5]`. -/
abbrev Zsqrt5 : Type := ℤ√5

/-- The coordinate `2`. -/
def twoZsqrt5 : Zsqrt5 := ⟨2, 0⟩

/-- The coordinate `1 + √5` (twice the golden ratio). -/
def oneAddSqrt5 : Zsqrt5 := ⟨1, 1⟩

/-- The twelve unnormalised icosahedral vertices in `(ℤ[√5])³`. -/
def icosahedronVerticesZsqrt5 : List (Fin 3 → Zsqrt5) :=
  [ ![0, twoZsqrt5, oneAddSqrt5]
  , ![0, twoZsqrt5, -oneAddSqrt5]
  , ![0, -twoZsqrt5, oneAddSqrt5]
  , ![0, -twoZsqrt5, -oneAddSqrt5]
  , ![oneAddSqrt5, 0, twoZsqrt5]
  , ![oneAddSqrt5, 0, -twoZsqrt5]
  , ![-oneAddSqrt5, 0, twoZsqrt5]
  , ![-oneAddSqrt5, 0, -twoZsqrt5]
  , ![twoZsqrt5, oneAddSqrt5, 0]
  , ![twoZsqrt5, -oneAddSqrt5, 0]
  , ![-twoZsqrt5, oneAddSqrt5, 0]
  , ![-twoZsqrt5, -oneAddSqrt5, 0]
  ]


/-! ### Bridge to the official `ℝ` vertex set

In this file `icosahedronVertexSet` is the official definition, imported from the
module `IcosahedralRotationGroup_2026-11-09` (src sha256 fe54b031…). `Real.goldenRatio`
is Mathlib's `(1 + √5) / 2`. -/

/-- The ring map `ℤ[√5] → ℝ` sending `√5` to `Real.sqrt 5`. -/
noncomputable def zsqrt5ToReal : Zsqrt5 →+* ℝ :=
  Zsqrtd.lift ⟨Real.sqrt 5, by rw [Real.mul_self_sqrt (by norm_num)]; norm_num⟩

theorem zsqrt5ToReal_apply (z : Zsqrt5) :
    zsqrt5ToReal z = (z.re : ℝ) + (z.im : ℝ) * Real.sqrt 5 := by
  simp [zsqrt5ToReal]

/-- Map a doubled-scale `ℤ[√5]` vertex to `ℝ³` and halve it. -/
noncomputable def halveToReal (v : Fin 3 → Zsqrt5) : Fin 3 → ℝ :=
  fun i => zsqrt5ToReal (v i) / 2

macro "vtx_tac" : tactic => `(tactic|
  (funext i; fin_cases i <;>
    simp [halveToReal, zsqrt5ToReal_apply, twoZsqrt5, oneAddSqrt5, Real.goldenRatio] <;>
    ring))

/-- Bridge: the twelve doubled-scale `ℤ[√5]` vertices, sent to `ℝ` by `√5 ↦ Real.sqrt 5`
and divided by `2`, form exactly the official `ℝ` vertex set `icosahedronVertexSet`. -/
theorem halveToReal_image_icosahedronVerticesZsqrt5 :
    halveToReal '' {v | v ∈ icosahedronVerticesZsqrt5} = icosahedronVertexSet := by
  ext p
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨v, hv, rfl⟩
    show ∃ a b : ℝ, _
    simp only [icosahedronVerticesZsqrt5, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨1, 1, by norm_num, by norm_num, Or.inl (by vtx_tac)⟩
    · exact ⟨1, -1, by norm_num, by norm_num, Or.inl (by vtx_tac)⟩
    · exact ⟨-1, 1, by norm_num, by norm_num, Or.inl (by vtx_tac)⟩
    · exact ⟨-1, -1, by norm_num, by norm_num, Or.inl (by vtx_tac)⟩
    · exact ⟨1, 1, by norm_num, by norm_num, Or.inr (Or.inl (by vtx_tac))⟩
    · exact ⟨-1, 1, by norm_num, by norm_num, Or.inr (Or.inl (by vtx_tac))⟩
    · exact ⟨1, -1, by norm_num, by norm_num, Or.inr (Or.inl (by vtx_tac))⟩
    · exact ⟨-1, -1, by norm_num, by norm_num, Or.inr (Or.inl (by vtx_tac))⟩
    · exact ⟨1, 1, by norm_num, by norm_num, Or.inr (Or.inr (by vtx_tac))⟩
    · exact ⟨1, -1, by norm_num, by norm_num, Or.inr (Or.inr (by vtx_tac))⟩
    · exact ⟨-1, 1, by norm_num, by norm_num, Or.inr (Or.inr (by vtx_tac))⟩
    · exact ⟨-1, -1, by norm_num, by norm_num, Or.inr (Or.inr (by vtx_tac))⟩
  · rintro ⟨a, b, ha, hb, hp⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hp with rfl | rfl | rfl
    · exact ⟨![0, twoZsqrt5, oneAddSqrt5], by simp [icosahedronVerticesZsqrt5], by vtx_tac⟩
    · exact ⟨![oneAddSqrt5, 0, twoZsqrt5], by simp [icosahedronVerticesZsqrt5], by vtx_tac⟩
    · exact ⟨![twoZsqrt5, oneAddSqrt5, 0], by simp [icosahedronVerticesZsqrt5], by vtx_tac⟩
    · exact ⟨![0, twoZsqrt5, -oneAddSqrt5], by simp [icosahedronVerticesZsqrt5], by vtx_tac⟩
    · exact ⟨![-oneAddSqrt5, 0, twoZsqrt5], by simp [icosahedronVerticesZsqrt5], by vtx_tac⟩
    · exact ⟨![twoZsqrt5, -oneAddSqrt5, 0], by simp [icosahedronVerticesZsqrt5], by vtx_tac⟩
    · exact ⟨![0, -twoZsqrt5, oneAddSqrt5], by simp [icosahedronVerticesZsqrt5], by vtx_tac⟩
    · exact ⟨![oneAddSqrt5, 0, -twoZsqrt5], by simp [icosahedronVerticesZsqrt5], by vtx_tac⟩
    · exact ⟨![-twoZsqrt5, oneAddSqrt5, 0], by simp [icosahedronVerticesZsqrt5], by vtx_tac⟩
    · exact ⟨![0, -twoZsqrt5, -oneAddSqrt5], by simp [icosahedronVerticesZsqrt5], by vtx_tac⟩
    · exact ⟨![-oneAddSqrt5, 0, -twoZsqrt5], by simp [icosahedronVerticesZsqrt5], by vtx_tac⟩
    · exact ⟨![-twoZsqrt5, -oneAddSqrt5, 0], by simp [icosahedronVerticesZsqrt5], by vtx_tac⟩

/-! ### `ℤ[√5]` has no zero divisors -/

theorem five_ne_sq (n : ℤ) : (5 : ℤ) ≠ n * n := by
  intro h
  have h1 : n ≤ 2 := by nlinarith
  have h2 : -2 ≤ n := by nlinarith
  interval_cases n <;> omega

instance : NoZeroDivisors Zsqrt5 where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} h := by
    have hn : a.norm * b.norm = 0 := by rw [← Zsqrtd.norm_mul, h]; rfl
    rcases mul_eq_zero.mp hn with ha | hb
    · exact Or.inl ((Zsqrtd.norm_eq_zero five_ne_sq a).mp ha)
    · exact Or.inr ((Zsqrtd.norm_eq_zero five_ne_sq b).mp hb)

instance : IsDomain Zsqrt5 := NoZeroDivisors.to_isDomain _

/-! ### Concrete 3 × 3 matrices (row major), with decidable equality -/

/-- A 3 × 3 matrix over `ℤ[√5]`, stored row major. -/
structure M3 where
  a00 : Zsqrt5
  a01 : Zsqrt5
  a02 : Zsqrt5
  a10 : Zsqrt5
  a11 : Zsqrt5
  a12 : Zsqrt5
  a20 : Zsqrt5
  a21 : Zsqrt5
  a22 : Zsqrt5
  deriving DecidableEq

namespace M3

/-- The Mathlib matrix with these entries. -/
def toMatrix (A : M3) : Matrix (Fin 3) (Fin 3) Zsqrt5 :=
  !![A.a00, A.a01, A.a02; A.a10, A.a11, A.a12; A.a20, A.a21, A.a22]

/-- Matrix product, written out. -/
def mul (A B : M3) : M3 :=
  ⟨A.a00 * B.a00 + A.a01 * B.a10 + A.a02 * B.a20,
   A.a00 * B.a01 + A.a01 * B.a11 + A.a02 * B.a21,
   A.a00 * B.a02 + A.a01 * B.a12 + A.a02 * B.a22,
   A.a10 * B.a00 + A.a11 * B.a10 + A.a12 * B.a20,
   A.a10 * B.a01 + A.a11 * B.a11 + A.a12 * B.a21,
   A.a10 * B.a02 + A.a11 * B.a12 + A.a12 * B.a22,
   A.a20 * B.a00 + A.a21 * B.a10 + A.a22 * B.a20,
   A.a20 * B.a01 + A.a21 * B.a11 + A.a22 * B.a21,
   A.a20 * B.a02 + A.a21 * B.a12 + A.a22 * B.a22⟩

/-- Transpose, written out. -/
def transpose (A : M3) : M3 :=
  ⟨A.a00, A.a10, A.a20, A.a01, A.a11, A.a21, A.a02, A.a12, A.a22⟩

/-- Entrywise scalar multiple. -/
def smul (c : Zsqrt5) (A : M3) : M3 :=
  ⟨c * A.a00, c * A.a01, c * A.a02, c * A.a10, c * A.a11, c * A.a12,
   c * A.a20, c * A.a21, c * A.a22⟩

/-- The scalar matrix `c • 1`. -/
def scal (c : Zsqrt5) : M3 := ⟨c, 0, 0, 0, c, 0, 0, 0, c⟩

/-- Determinant, written out as in `Matrix.det_fin_three`. -/
def det3 (A : M3) : Zsqrt5 :=
  A.a00 * A.a11 * A.a22 - A.a00 * A.a12 * A.a21 - A.a01 * A.a10 * A.a22 +
    A.a01 * A.a12 * A.a20 + A.a02 * A.a10 * A.a21 - A.a02 * A.a11 * A.a20

/-- Matrix–vector product, written out. -/
def mulVec (A : M3) (v : Fin 3 → Zsqrt5) : Fin 3 → Zsqrt5 :=
  ![A.a00 * v 0 + A.a01 * v 1 + A.a02 * v 2,
    A.a10 * v 0 + A.a11 * v 1 + A.a12 * v 2,
    A.a20 * v 0 + A.a21 * v 1 + A.a22 * v 2]

theorem toMatrix_injective : Function.Injective toMatrix := by
  intro A B h
  have e : ∀ i j, A.toMatrix i j = B.toMatrix i j := fun i j => by rw [h]
  cases A; cases B
  have := e 0 0; have := e 0 1; have := e 0 2
  have := e 1 0; have := e 1 1; have := e 1 2
  have := e 2 0; have := e 2 1; have := e 2 2
  simp_all [toMatrix]

theorem toMatrix_mul (A B : M3) : (A.mul B).toMatrix = A.toMatrix * B.toMatrix := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [toMatrix, mul, Matrix.mul_apply, Fin.sum_univ_three]

theorem toMatrix_transpose (A : M3) : A.transpose.toMatrix = A.toMatrixᵀ := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [toMatrix, transpose]

theorem toMatrix_smul (c : Zsqrt5) (A : M3) : (A.smul c).toMatrix = c • A.toMatrix := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [toMatrix, smul]

theorem toMatrix_scal (c : Zsqrt5) : (scal c).toMatrix = c • (1 : Matrix (Fin 3) (Fin 3) Zsqrt5) := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [toMatrix, scal]

theorem det_toMatrix (A : M3) : A.toMatrix.det = A.det3 := by
  simp [toMatrix, det3, Matrix.det_fin_three]

theorem toMatrix_mulVec (A : M3) (v : Fin 3 → Zsqrt5) : A.toMatrix *ᵥ v = A.mulVec v := by
  funext i
  fin_cases i <;> simp [toMatrix, mulVec, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

end M3

/-! ### The sixty scaled rotations -/

/-- Matrices 0–9 of the sixty. -/
def scaledRotationChunk0 : List M3 :=
  [ ⟨⟨4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨4, 0⟩⟩
  , ⟨⟨-4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨4, 0⟩⟩
  , ⟨⟨-4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-4, 0⟩⟩
  , ⟨⟨-2, 0⟩, ⟨-1, 1⟩, ⟨-1, -1⟩, ⟨-1, 1⟩, ⟨-1, -1⟩, ⟨-2, 0⟩, ⟨-1, -1⟩, ⟨-2, 0⟩, ⟨-1, 1⟩⟩
  , ⟨⟨-2, 0⟩, ⟨-1, 1⟩, ⟨-1, -1⟩, ⟨1, -1⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨1, -1⟩⟩
  , ⟨⟨-2, 0⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-1, 1⟩, ⟨-1, -1⟩, ⟨2, 0⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨-1, 1⟩⟩
  , ⟨⟨-2, 0⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨1, -1⟩, ⟨1, 1⟩, ⟨-2, 0⟩, ⟨-1, -1⟩, ⟨-2, 0⟩, ⟨1, -1⟩⟩
  , ⟨⟨-2, 0⟩, ⟨1, -1⟩, ⟨-1, -1⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-2, 0⟩, ⟨1, 1⟩, ⟨-2, 0⟩, ⟨1, -1⟩⟩
  , ⟨⟨-2, 0⟩, ⟨1, -1⟩, ⟨-1, -1⟩, ⟨1, -1⟩, ⟨-1, -1⟩, ⟨2, 0⟩, ⟨-1, -1⟩, ⟨2, 0⟩, ⟨-1, 1⟩⟩
  , ⟨⟨-2, 0⟩, ⟨1, -1⟩, ⟨1, 1⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨-1, -1⟩, ⟨2, 0⟩, ⟨1, -1⟩⟩
  ]

/-- Matrices 10–19 of the sixty. -/
def scaledRotationChunk1 : List M3 :=
  [ ⟨⟨-2, 0⟩, ⟨1, -1⟩, ⟨1, 1⟩, ⟨1, -1⟩, ⟨-1, -1⟩, ⟨-2, 0⟩, ⟨1, 1⟩, ⟨-2, 0⟩, ⟨-1, 1⟩⟩
  , ⟨⟨-1, -1⟩, ⟨-2, 0⟩, ⟨-1, 1⟩, ⟨-2, 0⟩, ⟨-1, 1⟩, ⟨-1, -1⟩, ⟨-1, 1⟩, ⟨-1, -1⟩, ⟨-2, 0⟩⟩
  , ⟨⟨-1, -1⟩, ⟨-2, 0⟩, ⟨-1, 1⟩, ⟨2, 0⟩, ⟨1, -1⟩, ⟨1, 1⟩, ⟨1, -1⟩, ⟨1, 1⟩, ⟨2, 0⟩⟩
  , ⟨⟨-1, -1⟩, ⟨-2, 0⟩, ⟨1, -1⟩, ⟨-2, 0⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨1, -1⟩, ⟨1, 1⟩, ⟨-2, 0⟩⟩
  , ⟨⟨-1, -1⟩, ⟨-2, 0⟩, ⟨1, -1⟩, ⟨2, 0⟩, ⟨1, -1⟩, ⟨-1, -1⟩, ⟨-1, 1⟩, ⟨-1, -1⟩, ⟨2, 0⟩⟩
  , ⟨⟨-1, -1⟩, ⟨2, 0⟩, ⟨-1, 1⟩, ⟨-2, 0⟩, ⟨1, -1⟩, ⟨-1, -1⟩, ⟨1, -1⟩, ⟨-1, -1⟩, ⟨2, 0⟩⟩
  , ⟨⟨-1, -1⟩, ⟨2, 0⟩, ⟨-1, 1⟩, ⟨2, 0⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-2, 0⟩⟩
  , ⟨⟨-1, -1⟩, ⟨2, 0⟩, ⟨1, -1⟩, ⟨-2, 0⟩, ⟨1, -1⟩, ⟨1, 1⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨2, 0⟩⟩
  , ⟨⟨-1, -1⟩, ⟨2, 0⟩, ⟨1, -1⟩, ⟨2, 0⟩, ⟨-1, 1⟩, ⟨-1, -1⟩, ⟨1, -1⟩, ⟨-1, -1⟩, ⟨-2, 0⟩⟩
  , ⟨⟨-1, 1⟩, ⟨-1, -1⟩, ⟨-2, 0⟩, ⟨-1, -1⟩, ⟨-2, 0⟩, ⟨-1, 1⟩, ⟨-2, 0⟩, ⟨-1, 1⟩, ⟨-1, -1⟩⟩
  ]

/-- Matrices 20–29 of the sixty. -/
def scaledRotationChunk2 : List M3 :=
  [ ⟨⟨-1, 1⟩, ⟨-1, -1⟩, ⟨-2, 0⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨1, -1⟩, ⟨2, 0⟩, ⟨1, -1⟩, ⟨1, 1⟩⟩
  , ⟨⟨-1, 1⟩, ⟨-1, -1⟩, ⟨2, 0⟩, ⟨-1, -1⟩, ⟨-2, 0⟩, ⟨1, -1⟩, ⟨2, 0⟩, ⟨1, -1⟩, ⟨-1, -1⟩⟩
  , ⟨⟨-1, 1⟩, ⟨-1, -1⟩, ⟨2, 0⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨-1, 1⟩, ⟨-2, 0⟩, ⟨-1, 1⟩, ⟨1, 1⟩⟩
  , ⟨⟨-1, 1⟩, ⟨1, 1⟩, ⟨-2, 0⟩, ⟨-1, -1⟩, ⟨2, 0⟩, ⟨-1, 1⟩, ⟨2, 0⟩, ⟨-1, 1⟩, ⟨1, 1⟩⟩
  , ⟨⟨-1, 1⟩, ⟨1, 1⟩, ⟨-2, 0⟩, ⟨1, 1⟩, ⟨-2, 0⟩, ⟨1, -1⟩, ⟨-2, 0⟩, ⟨1, -1⟩, ⟨-1, -1⟩⟩
  , ⟨⟨-1, 1⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨-1, -1⟩, ⟨2, 0⟩, ⟨1, -1⟩, ⟨-2, 0⟩, ⟨1, -1⟩, ⟨1, 1⟩⟩
  , ⟨⟨-1, 1⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨1, 1⟩, ⟨-2, 0⟩, ⟨-1, 1⟩, ⟨2, 0⟩, ⟨-1, 1⟩, ⟨-1, -1⟩⟩
  , ⟨⟨0, 0⟩, ⟨-4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-4, 0⟩, ⟨4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩
  , ⟨⟨0, 0⟩, ⟨-4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨4, 0⟩, ⟨-4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩
  , ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨-4, 0⟩, ⟨-4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨4, 0⟩, ⟨0, 0⟩⟩
  ]

/-- Matrices 30–39 of the sixty. -/
def scaledRotationChunk3 : List M3 :=
  [ ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨-4, 0⟩, ⟨4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-4, 0⟩, ⟨0, 0⟩⟩
  , ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨4, 0⟩, ⟨-4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-4, 0⟩, ⟨0, 0⟩⟩
  , ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨4, 0⟩, ⟨4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨4, 0⟩, ⟨0, 0⟩⟩
  , ⟨⟨0, 0⟩, ⟨4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-4, 0⟩, ⟨-4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩
  , ⟨⟨0, 0⟩, ⟨4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨4, 0⟩, ⟨4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩
  , ⟨⟨1, -1⟩, ⟨-1, -1⟩, ⟨-2, 0⟩, ⟨-1, -1⟩, ⟨2, 0⟩, ⟨1, -1⟩, ⟨2, 0⟩, ⟨-1, 1⟩, ⟨-1, -1⟩⟩
  , ⟨⟨1, -1⟩, ⟨-1, -1⟩, ⟨-2, 0⟩, ⟨1, 1⟩, ⟨-2, 0⟩, ⟨-1, 1⟩, ⟨-2, 0⟩, ⟨1, -1⟩, ⟨1, 1⟩⟩
  , ⟨⟨1, -1⟩, ⟨-1, -1⟩, ⟨2, 0⟩, ⟨-1, -1⟩, ⟨2, 0⟩, ⟨-1, 1⟩, ⟨-2, 0⟩, ⟨1, -1⟩, ⟨-1, -1⟩⟩
  , ⟨⟨1, -1⟩, ⟨-1, -1⟩, ⟨2, 0⟩, ⟨1, 1⟩, ⟨-2, 0⟩, ⟨1, -1⟩, ⟨2, 0⟩, ⟨-1, 1⟩, ⟨1, 1⟩⟩
  , ⟨⟨1, -1⟩, ⟨1, 1⟩, ⟨-2, 0⟩, ⟨-1, -1⟩, ⟨-2, 0⟩, ⟨1, -1⟩, ⟨-2, 0⟩, ⟨-1, 1⟩, ⟨1, 1⟩⟩
  ]

/-- Matrices 40–49 of the sixty. -/
def scaledRotationChunk4 : List M3 :=
  [ ⟨⟨1, -1⟩, ⟨1, 1⟩, ⟨-2, 0⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨-1, 1⟩, ⟨2, 0⟩, ⟨1, -1⟩, ⟨-1, -1⟩⟩
  , ⟨⟨1, -1⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨-1, -1⟩, ⟨-2, 0⟩, ⟨-1, 1⟩, ⟨2, 0⟩, ⟨1, -1⟩, ⟨1, 1⟩⟩
  , ⟨⟨1, -1⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨1, -1⟩, ⟨-2, 0⟩, ⟨-1, 1⟩, ⟨-1, -1⟩⟩
  , ⟨⟨1, 1⟩, ⟨-2, 0⟩, ⟨-1, 1⟩, ⟨-2, 0⟩, ⟨1, -1⟩, ⟨1, 1⟩, ⟨1, -1⟩, ⟨-1, -1⟩, ⟨-2, 0⟩⟩
  , ⟨⟨1, 1⟩, ⟨-2, 0⟩, ⟨-1, 1⟩, ⟨2, 0⟩, ⟨-1, 1⟩, ⟨-1, -1⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨2, 0⟩⟩
  , ⟨⟨1, 1⟩, ⟨-2, 0⟩, ⟨1, -1⟩, ⟨-2, 0⟩, ⟨1, -1⟩, ⟨-1, -1⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-2, 0⟩⟩
  , ⟨⟨1, 1⟩, ⟨-2, 0⟩, ⟨1, -1⟩, ⟨2, 0⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨1, -1⟩, ⟨-1, -1⟩, ⟨2, 0⟩⟩
  , ⟨⟨1, 1⟩, ⟨2, 0⟩, ⟨-1, 1⟩, ⟨-2, 0⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-1, 1⟩, ⟨-1, -1⟩, ⟨2, 0⟩⟩
  , ⟨⟨1, 1⟩, ⟨2, 0⟩, ⟨-1, 1⟩, ⟨2, 0⟩, ⟨1, -1⟩, ⟨-1, -1⟩, ⟨1, -1⟩, ⟨1, 1⟩, ⟨-2, 0⟩⟩
  , ⟨⟨1, 1⟩, ⟨2, 0⟩, ⟨1, -1⟩, ⟨-2, 0⟩, ⟨-1, 1⟩, ⟨-1, -1⟩, ⟨1, -1⟩, ⟨1, 1⟩, ⟨2, 0⟩⟩
  ]

/-- Matrices 50–59 of the sixty. -/
def scaledRotationChunk5 : List M3 :=
  [ ⟨⟨1, 1⟩, ⟨2, 0⟩, ⟨1, -1⟩, ⟨2, 0⟩, ⟨1, -1⟩, ⟨1, 1⟩, ⟨-1, 1⟩, ⟨-1, -1⟩, ⟨-2, 0⟩⟩
  , ⟨⟨2, 0⟩, ⟨-1, 1⟩, ⟨-1, -1⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨1, 1⟩, ⟨-2, 0⟩, ⟨-1, 1⟩⟩
  , ⟨⟨2, 0⟩, ⟨-1, 1⟩, ⟨-1, -1⟩, ⟨1, -1⟩, ⟨-1, -1⟩, ⟨-2, 0⟩, ⟨-1, -1⟩, ⟨2, 0⟩, ⟨1, -1⟩⟩
  , ⟨⟨2, 0⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-2, 0⟩, ⟨-1, -1⟩, ⟨2, 0⟩, ⟨-1, 1⟩⟩
  , ⟨⟨2, 0⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨1, -1⟩, ⟨-1, -1⟩, ⟨2, 0⟩, ⟨1, 1⟩, ⟨-2, 0⟩, ⟨1, -1⟩⟩
  , ⟨⟨2, 0⟩, ⟨1, -1⟩, ⟨-1, -1⟩, ⟨-1, 1⟩, ⟨-1, -1⟩, ⟨2, 0⟩, ⟨-1, -1⟩, ⟨-2, 0⟩, ⟨1, -1⟩⟩
  , ⟨⟨2, 0⟩, ⟨1, -1⟩, ⟨-1, -1⟩, ⟨1, -1⟩, ⟨1, 1⟩, ⟨-2, 0⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨-1, 1⟩⟩
  , ⟨⟨2, 0⟩, ⟨1, -1⟩, ⟨1, 1⟩, ⟨-1, 1⟩, ⟨-1, -1⟩, ⟨-2, 0⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨1, -1⟩⟩
  , ⟨⟨2, 0⟩, ⟨1, -1⟩, ⟨1, 1⟩, ⟨1, -1⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨-1, -1⟩, ⟨-2, 0⟩, ⟨-1, 1⟩⟩
  , ⟨⟨4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-4, 0⟩⟩
  ]

/-- Sixty explicit matrices `4R` over `ℤ[√5]` (source: ToE `a5_exact_qsqrt5_v2.py`;
re-checked below). The first entry is `4 • 1`. -/
def scaledRotationList : List M3 :=
  scaledRotationChunk0 ++ scaledRotationChunk1 ++ scaledRotationChunk2 ++
    scaledRotationChunk3 ++ scaledRotationChunk4 ++ scaledRotationChunk5

/-- The twelve listed vertices, scaled by `4`. -/
def vtxScaled4 (w : Fin 3 → Zsqrt5) : Fin 3 → Zsqrt5 := (4 : Zsqrt5) • w

theorem scaledRotationList_length : scaledRotationList.length = 60 := rfl

theorem scaledRotationList_nodup : scaledRotationList.Nodup := by decide +kernel

theorem scaledRotationList_transpose_mul :
    ∀ A ∈ scaledRotationList, A.transpose.mul A = M3.scal 16 := by decide +kernel

theorem scaledRotationList_det3 : ∀ A ∈ scaledRotationList, A.det3 = 64 := by decide +kernel

theorem scaledRotationList_mapsTo :
    ∀ A ∈ scaledRotationList, ∀ v ∈ icosahedronVerticesZsqrt5,
      ∃ w ∈ icosahedronVerticesZsqrt5, A.mulVec v = (4 : Zsqrt5) • w := by decide +kernel

theorem scaledRotationChunk0_closed_mul :
    ∀ A ∈ scaledRotationChunk0, ∀ B ∈ scaledRotationList,
      ∃ C ∈ scaledRotationList, A.mul B = C.smul 4 := by decide +kernel

theorem scaledRotationChunk1_closed_mul :
    ∀ A ∈ scaledRotationChunk1, ∀ B ∈ scaledRotationList,
      ∃ C ∈ scaledRotationList, A.mul B = C.smul 4 := by decide +kernel

theorem scaledRotationChunk2_closed_mul :
    ∀ A ∈ scaledRotationChunk2, ∀ B ∈ scaledRotationList,
      ∃ C ∈ scaledRotationList, A.mul B = C.smul 4 := by decide +kernel

theorem scaledRotationChunk3_closed_mul :
    ∀ A ∈ scaledRotationChunk3, ∀ B ∈ scaledRotationList,
      ∃ C ∈ scaledRotationList, A.mul B = C.smul 4 := by decide +kernel

theorem scaledRotationChunk4_closed_mul :
    ∀ A ∈ scaledRotationChunk4, ∀ B ∈ scaledRotationList,
      ∃ C ∈ scaledRotationList, A.mul B = C.smul 4 := by decide +kernel

theorem scaledRotationChunk5_closed_mul :
    ∀ A ∈ scaledRotationChunk5, ∀ B ∈ scaledRotationList,
      ∃ C ∈ scaledRotationList, A.mul B = C.smul 4 := by decide +kernel

theorem scaledRotationList_closed_mul :
    ∀ A ∈ scaledRotationList, ∀ B ∈ scaledRotationList,
      ∃ C ∈ scaledRotationList, A.mul B = C.smul 4 := by
  intro A hA
  simp only [scaledRotationList, List.mem_append] at hA
  rcases hA with ((((h | h) | h) | h) | h) | h
  exacts [scaledRotationChunk0_closed_mul A h, scaledRotationChunk1_closed_mul A h,
    scaledRotationChunk2_closed_mul A h, scaledRotationChunk3_closed_mul A h,
    scaledRotationChunk4_closed_mul A h, scaledRotationChunk5_closed_mul A h]

theorem scaledRotationList_mapsOnto :
    ∀ A ∈ scaledRotationList, ∀ w ∈ icosahedronVerticesZsqrt5,
      ∃ v ∈ icosahedronVerticesZsqrt5, A.mulVec v = (4 : Zsqrt5) • w := by decide +kernel

theorem scaledRotationList_transpose_mem :
    ∀ A ∈ scaledRotationList, A.transpose ∈ scaledRotationList := by decide +kernel

/-! ### Completeness checker: three vertices determine the matrix -/

/-- Dot product, written out. -/
def dot3 (a b : Fin 3 → Zsqrt5) : Zsqrt5 := a 0 * b 0 + a 1 * b 1 + a 2 * b 2

/-- The matrix whose columns are `a`, `b`, `c`. -/
def colsMat (a b c : Fin 3 → Zsqrt5) : Matrix (Fin 3) (Fin 3) Zsqrt5 :=
  Matrix.of fun k j => (![a, b, c] : Fin 3 → Fin 3 → Zsqrt5) j k

/-- `det (colsMat a b c)`, written out. -/
def tripleDet (a b c : Fin 3 → Zsqrt5) : Zsqrt5 :=
  a 0 * b 1 * c 2 - a 0 * c 1 * b 2 - b 0 * a 1 * c 2 +
    b 0 * c 1 * a 2 + c 0 * a 1 * b 2 - c 0 * b 1 * a 2

theorem dot3_eq (a b : Fin 3 → Zsqrt5) : dot3 a b = a ⬝ᵥ b := by
  simp [dot3, dotProduct, Fin.sum_univ_three]

theorem det_colsMat (a b c : Fin 3 → Zsqrt5) : (colsMat a b c).det = tripleDet a b c := by
  simp [colsMat, tripleDet, Matrix.det_fin_three]

/-- Three of the listed vertices (entries 0, 4 and 8 of the list). -/
def vtxA : Fin 3 → Zsqrt5 := ![0, twoZsqrt5, oneAddSqrt5]
def vtxB : Fin 3 → Zsqrt5 := ![oneAddSqrt5, 0, twoZsqrt5]
def vtxC : Fin 3 → Zsqrt5 := ![twoZsqrt5, oneAddSqrt5, 0]

theorem vtxA_mem : vtxA ∈ icosahedronVerticesZsqrt5 := by decide
theorem vtxB_mem : vtxB ∈ icosahedronVerticesZsqrt5 := by decide
theorem vtxC_mem : vtxC ∈ icosahedronVerticesZsqrt5 := by decide

theorem tripleDet_vtx_ne_zero : tripleDet vtxA vtxB vtxC ≠ 0 := by decide

/-- Finite check: every triple of listed vertices with the same pairwise dot products
and the same triple determinant as `(vtxA, vtxB, vtxC)` is the image, scaled by 4,
of `(vtxA, vtxB, vtxC)` under one of the sixty matrices. -/
theorem triple_check :
    ∀ a ∈ icosahedronVerticesZsqrt5, ∀ b ∈ icosahedronVerticesZsqrt5,
      ∀ c ∈ icosahedronVerticesZsqrt5,
        dot3 a b = dot3 vtxA vtxB → dot3 a c = dot3 vtxA vtxC →
        dot3 b c = dot3 vtxB vtxC → tripleDet a b c = tripleDet vtxA vtxB vtxC →
        ∃ C ∈ scaledRotationList, C.mulVec vtxA = (4 : Zsqrt5) • a ∧
          C.mulVec vtxB = (4 : Zsqrt5) • b ∧ C.mulVec vtxC = (4 : Zsqrt5) • c := by
  decide +kernel

/-! ### Statements about Mathlib matrices -/

/-- The sixty scaled matrices as a `Finset` of Mathlib matrices over `ℤ[√5]`. -/
def scaledIcosahedralRotations : Finset (Matrix (Fin 3) (Fin 3) Zsqrt5) :=
  (scaledRotationList.map M3.toMatrix).toFinset

theorem mem_scaledIcosahedralRotations {S : Matrix (Fin 3) (Fin 3) Zsqrt5} :
    S ∈ scaledIcosahedralRotations ↔ ∃ A ∈ scaledRotationList, A.toMatrix = S := by
  simp [scaledIcosahedralRotations]

/-- (1) There are exactly sixty pairwise distinct scaled matrices. -/
theorem scaledIcosahedralRotations_card : scaledIcosahedralRotations.card = 60 := by
  rw [scaledIcosahedralRotations,
    List.toFinset_card_of_nodup (scaledRotationList_nodup.map M3.toMatrix_injective),
    List.length_map, scaledRotationList_length]

/-- (2a) Each is a scaled rotation: `Sᵀ S = 16 • 1` and `det S = 64`
(i.e. `S / 4 ∈ SO(3)` over `ℚ(√5)`). -/
theorem scaledIcosahedralRotations_isScaledRotation :
    ∀ S ∈ scaledIcosahedralRotations,
      Sᵀ * S = (16 : Zsqrt5) • (1 : Matrix (Fin 3) (Fin 3) Zsqrt5) ∧ S.det = 64 := by
  intro S hS
  obtain ⟨A, hA, rfl⟩ := mem_scaledIcosahedralRotations.mp hS
  refine ⟨?_, ?_⟩
  · rw [← M3.toMatrix_transpose, ← M3.toMatrix_mul, scaledRotationList_transpose_mul A hA,
      M3.toMatrix_scal]
  · rw [M3.det_toMatrix, scaledRotationList_det3 A hA]

/-- (2b) Each maps every listed vertex to `4 •` a listed vertex, and every listed
vertex, scaled by `4`, is hit. -/
theorem scaledIcosahedralRotations_permutes_vertices :
    ∀ S ∈ scaledIcosahedralRotations,
      (∀ v ∈ icosahedronVerticesZsqrt5, ∃ w ∈ icosahedronVerticesZsqrt5,
        S *ᵥ v = (4 : Zsqrt5) • w) ∧
      (∀ w ∈ icosahedronVerticesZsqrt5, ∃ v ∈ icosahedronVerticesZsqrt5,
        S *ᵥ v = (4 : Zsqrt5) • w) := by
  intro S hS
  obtain ⟨A, hA, rfl⟩ := mem_scaledIcosahedralRotations.mp hS
  refine ⟨fun v hv => ?_, fun w hw => ?_⟩
  · obtain ⟨w, hw, h⟩ := scaledRotationList_mapsTo A hA v hv
    exact ⟨w, hw, by rw [M3.toMatrix_mulVec, h]⟩
  · obtain ⟨v, hv, h⟩ := scaledRotationList_mapsOnto A hA w hw
    exact ⟨v, hv, by rw [M3.toMatrix_mulVec, h]⟩

/-- (3a) Contains `4 • 1` (the scaled identity). -/
theorem scaledIcosahedralRotations_scaled_one_mem :
    (4 : Zsqrt5) • (1 : Matrix (Fin 3) (Fin 3) Zsqrt5) ∈ scaledIcosahedralRotations := by
  rw [mem_scaledIcosahedralRotations]
  exact ⟨M3.scal 4, by decide, M3.toMatrix_scal 4⟩

/-- (3b) Closed under the scaled product: `A * B = 4 • C` with `C` in the set. -/
theorem scaledIcosahedralRotations_mul_mem :
    ∀ A ∈ scaledIcosahedralRotations, ∀ B ∈ scaledIcosahedralRotations,
      ∃ C ∈ scaledIcosahedralRotations, A * B = (4 : Zsqrt5) • C := by
  intro A hA B hB
  obtain ⟨A', hA', rfl⟩ := mem_scaledIcosahedralRotations.mp hA
  obtain ⟨B', hB', rfl⟩ := mem_scaledIcosahedralRotations.mp hB
  obtain ⟨C', hC', h⟩ := scaledRotationList_closed_mul A' hA' B' hB'
  refine ⟨C'.toMatrix, mem_scaledIcosahedralRotations.mpr ⟨C', hC', rfl⟩, ?_⟩
  rw [← M3.toMatrix_mul, h, M3.toMatrix_smul]

/-- (3c) Closed under transpose (the inverse, up to the factor `16`). -/
theorem scaledIcosahedralRotations_transpose_mem :
    ∀ S ∈ scaledIcosahedralRotations, Sᵀ ∈ scaledIcosahedralRotations := by
  intro S hS
  obtain ⟨A, hA, rfl⟩ := mem_scaledIcosahedralRotations.mp hS
  exact mem_scaledIcosahedralRotations.mpr
    ⟨A.transpose, scaledRotationList_transpose_mem A hA, M3.toMatrix_transpose A⟩

/-! ### Completeness over `ℤ[√5]` -/

theorem dotProduct_mulVec_of_scaledOrthogonal (S : Matrix (Fin 3) (Fin 3) Zsqrt5)
    (hS : Sᵀ * S = (16 : Zsqrt5) • (1 : Matrix (Fin 3) (Fin 3) Zsqrt5))
    (v w : Fin 3 → Zsqrt5) : (S *ᵥ v) ⬝ᵥ (S *ᵥ w) = 16 * (v ⬝ᵥ w) := by
  rw [← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hS,
    Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]

theorem dot3_of_images (S : Matrix (Fin 3) (Fin 3) Zsqrt5)
    (hS : Sᵀ * S = (16 : Zsqrt5) • (1 : Matrix (Fin 3) (Fin 3) Zsqrt5))
    {v w a b : Fin 3 → Zsqrt5} (ha : S *ᵥ v = (4 : Zsqrt5) • a)
    (hb : S *ᵥ w = (4 : Zsqrt5) • b) : dot3 a b = dot3 v w := by
  have h := dotProduct_mulVec_of_scaledOrthogonal S hS v w
  rw [ha, hb, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul, ← mul_assoc] at h
  have h16 : (16 : Zsqrt5) ≠ 0 := by decide
  rw [dot3_eq, dot3_eq]
  exact mul_left_cancel₀ h16 (by rw [← h]; norm_num)

theorem colsMat_mul (S : Matrix (Fin 3) (Fin 3) Zsqrt5) (a b c : Fin 3 → Zsqrt5) :
    S * colsMat a b c = colsMat (S *ᵥ a) (S *ᵥ b) (S *ᵥ c) := by
  refine Matrix.ext fun i j => ?_
  fin_cases j <;> rfl

theorem colsMat_smul (r : Zsqrt5) (a b c : Fin 3 → Zsqrt5) :
    colsMat (r • a) (r • b) (r • c) = r • colsMat a b c := by
  refine Matrix.ext fun i j => ?_
  fin_cases j <;> rfl

/-- (3d) Completeness over `ℤ[√5]`: a scaled rotation (`Sᵀ S = 16 • 1`, `det S = 64`)
that maps each listed vertex to `4 •` a listed vertex is one of the sixty. -/
theorem mem_scaledIcosahedralRotations_of_preserves_vertices
    (S : Matrix (Fin 3) (Fin 3) Zsqrt5)
    (hS : Sᵀ * S = (16 : Zsqrt5) • (1 : Matrix (Fin 3) (Fin 3) Zsqrt5))
    (hdet : S.det = 64)
    (hV : ∀ v ∈ icosahedronVerticesZsqrt5, ∃ w ∈ icosahedronVerticesZsqrt5,
      S *ᵥ v = (4 : Zsqrt5) • w) :
    S ∈ scaledIcosahedralRotations := by
  obtain ⟨a, ha, hSa⟩ := hV vtxA vtxA_mem
  obtain ⟨b, hb, hSb⟩ := hV vtxB vtxB_mem
  obtain ⟨c, hc, hSc⟩ := hV vtxC vtxC_mem
  have hdetabc : tripleDet a b c = tripleDet vtxA vtxB vtxC := by
    have h := congrArg Matrix.det (colsMat_mul S vtxA vtxB vtxC)
    rw [Matrix.det_mul, hdet, hSa, hSb, hSc, colsMat_smul, Matrix.det_smul,
      det_colsMat, det_colsMat] at h
    have h64 : (64 : Zsqrt5) ≠ 0 := by decide
    refine mul_left_cancel₀ h64 ?_
    rw [h]; simp; norm_num
  obtain ⟨C, hC, hCa, hCb, hCc⟩ := triple_check a ha b hb c hc
    (dot3_of_images S hS hSa hSb) (dot3_of_images S hS hSa hSc)
    (dot3_of_images S hS hSb hSc) hdetabc
  refine mem_scaledIcosahedralRotations.mpr ⟨C, hC, ?_⟩
  -- `C.toMatrix` and `S` agree on the three columns of an invertible matrix.
  have hcols : C.toMatrix * colsMat vtxA vtxB vtxC = S * colsMat vtxA vtxB vtxC := by
    rw [colsMat_mul, colsMat_mul, M3.toMatrix_mulVec, M3.toMatrix_mulVec,
      M3.toMatrix_mulVec, hCa, hCb, hCc, hSa, hSb, hSc]
  have h2 := congrArg (· * (colsMat vtxA vtxB vtxC).adjugate) hcols
  simp only [Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one,
    det_colsMat] at h2
  refine Matrix.ext fun i j => ?_
  have := congrFun (congrFun h2 i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  exact mul_left_cancel₀ tripleDet_vtx_ne_zero this

/-- (3e) The sixty are exactly the scaled rotations over `ℤ[√5]` that map each
listed vertex to `4 •` a listed vertex. -/
theorem mem_scaledIcosahedralRotations_iff (S : Matrix (Fin 3) (Fin 3) Zsqrt5) :
    S ∈ scaledIcosahedralRotations ↔
      (Sᵀ * S = (16 : Zsqrt5) • (1 : Matrix (Fin 3) (Fin 3) Zsqrt5) ∧ S.det = 64 ∧
        ∀ v ∈ icosahedronVerticesZsqrt5, ∃ w ∈ icosahedronVerticesZsqrt5,
          S *ᵥ v = (4 : Zsqrt5) • w) := by
  constructor
  · intro hS
    exact ⟨(scaledIcosahedralRotations_isScaledRotation S hS).1,
      (scaledIcosahedralRotations_isScaledRotation S hS).2,
      (scaledIcosahedralRotations_permutes_vertices S hS).1⟩
  · rintro ⟨h1, h2, h3⟩
    exact mem_scaledIcosahedralRotations_of_preserves_vertices S h1 h2 h3

/-- (3f) The scaled vertex stabilizer over `ℤ[√5]` (scaled rotations mapping each listed
vertex to `4 •` a listed vertex) has exactly sixty elements. -/
theorem scaledVertexStabilizerZsqrt5_ncard :
    {S : Matrix (Fin 3) (Fin 3) Zsqrt5 |
      Sᵀ * S = (16 : Zsqrt5) • (1 : Matrix (Fin 3) (Fin 3) Zsqrt5) ∧ S.det = 64 ∧
        ∀ v ∈ icosahedronVerticesZsqrt5, ∃ w ∈ icosahedronVerticesZsqrt5,
          S *ᵥ v = (4 : Zsqrt5) • w}.ncard = 60 := by
  have h : {S : Matrix (Fin 3) (Fin 3) Zsqrt5 |
      Sᵀ * S = (16 : Zsqrt5) • (1 : Matrix (Fin 3) (Fin 3) Zsqrt5) ∧ S.det = 64 ∧
        ∀ v ∈ icosahedronVerticesZsqrt5, ∃ w ∈ icosahedronVerticesZsqrt5,
          S *ᵥ v = (4 : Zsqrt5) • w} = (scaledIcosahedralRotations : Set _) := by
    ext S
    simp only [Set.mem_ofPred_eq, Finset.mem_coe]
    exact (mem_scaledIcosahedralRotations_iff S).symm
  rw [h, Set.ncard_coe_finset, scaledIcosahedralRotations_card]


/-! ### Transfer to the official `SO(3, ℝ)` stabilizer -/

theorem zsqrt5ToReal_injective : Function.Injective zsqrt5ToReal := by
  unfold zsqrt5ToReal
  exact Zsqrtd.lift_injective _ five_ne_sq

/-- Real normalisation of a scaled matrix: map the entries to `ℝ` and divide by `4`. -/
noncomputable def realQuarter (S : Matrix (Fin 3) (Fin 3) Zsqrt5) : Matrix (Fin 3) (Fin 3) ℝ :=
  (1 / 4 : ℝ) • S.map zsqrt5ToReal

theorem realQuarter_injective : Function.Injective realQuarter := by
  intro S T h
  refine Matrix.ext fun i j => ?_
  have := congrFun (congrFun h i) j
  simp only [realQuarter, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul] at this
  exact zsqrt5ToReal_injective (by linarith)

theorem halveToReal_eq (v : Fin 3 → Zsqrt5) :
    halveToReal v = (1 / 2 : ℝ) • (fun i => zsqrt5ToReal (v i)) := by
  funext i
  simp only [halveToReal, Pi.smul_apply, smul_eq_mul]
  ring

theorem map_mulVec_apply (S : Matrix (Fin 3) (Fin 3) Zsqrt5) (v : Fin 3 → Zsqrt5) (i : Fin 3) :
    (S.map zsqrt5ToReal *ᵥ (fun k => zsqrt5ToReal (v k))) i = zsqrt5ToReal ((S *ᵥ v) i) := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem realQuarter_mulVec_halveToReal (S : Matrix (Fin 3) (Fin 3) Zsqrt5)
    {v w : Fin 3 → Zsqrt5} (h : S *ᵥ v = (4 : Zsqrt5) • w) :
    realQuarter S *ᵥ halveToReal v = halveToReal w := by
  funext i
  rw [halveToReal_eq, halveToReal_eq, realQuarter, Matrix.smul_mulVec, Matrix.mulVec_smul]
  simp only [Pi.smul_apply, smul_eq_mul, map_mulVec_apply, h]
  simp only [map_mul, map_ofNat]
  ring

theorem realQuarter_mem_specialOrthogonalGroup {S : Matrix (Fin 3) (Fin 3) Zsqrt5}
    (hS : Sᵀ * S = (16 : Zsqrt5) • (1 : Matrix (Fin 3) (Fin 3) Zsqrt5)) (hdet : S.det = 64) :
    realQuarter S ∈ specialOrthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff']
  have hmap : (S.map zsqrt5ToReal)ᵀ * S.map zsqrt5ToReal =
      (16 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
    rw [← Matrix.transpose_map, ← Matrix.map_mul, hS]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [map_ofNat]
  have hdetR : (S.map zsqrt5ToReal).det = 64 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet]
    exact map_ofNat zsqrt5ToReal 64
  refine ⟨?_, ?_⟩
  · rw [realQuarter, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, hmap, smul_smul,
      smul_smul]
    norm_num
  · rw [realQuarter, Matrix.det_smul, hdetR]
    norm_num

/-- The halved real image of a listed vertex lies in the official vertex set. -/
theorem halveToReal_mem_icosahedronVertexSet {v : Fin 3 → Zsqrt5}
    (hv : v ∈ icosahedronVerticesZsqrt5) : halveToReal v ∈ icosahedronVertexSet := by
  rw [← halveToReal_image_icosahedronVerticesZsqrt5]
  exact ⟨v, hv, rfl⟩

/-- Each of the sixty, normalised over `ℝ`, as an element of `SO(3, ℝ)`. -/
noncomputable def toSpecialOrthogonal (S : scaledIcosahedralRotations) :
    specialOrthogonalGroup (Fin 3) ℝ :=
  ⟨realQuarter S, realQuarter_mem_specialOrthogonalGroup
    (scaledIcosahedralRotations_isScaledRotation S S.2).1
    (scaledIcosahedralRotations_isScaledRotation S S.2).2⟩

theorem toSpecialOrthogonal_mem (S : scaledIcosahedralRotations) :
    toSpecialOrthogonal S ∈ icosahedralRotationGroup := by
  rw [mem_icosahedralRotationGroup_iff]
  unfold mem_icosahedralRotationGroup
  change (fun v => realQuarter S *ᵥ v) '' icosahedronVertexSet = icosahedronVertexSet
  have hp := scaledIcosahedralRotations_permutes_vertices S S.2
  rw [← halveToReal_image_icosahedronVerticesZsqrt5, Set.image_image]
  ext p
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨w, hw, h⟩ := hp.1 v hv
    exact ⟨w, hw, (realQuarter_mulVec_halveToReal S h).symm⟩
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨v, hv, h⟩ := hp.2 w hw
    exact ⟨v, hv, realQuarter_mulVec_halveToReal S h⟩

/-- The map from the sixty scaled matrices to the official stabilizer. -/
noncomputable def toIcosahedralRotationGroup (S : scaledIcosahedralRotations) :
    icosahedralRotationGroup :=
  ⟨toSpecialOrthogonal S, toSpecialOrthogonal_mem S⟩

theorem toIcosahedralRotationGroup_injective : Function.Injective toIcosahedralRotationGroup := by
  intro S T h
  have h1 := congrArg (fun A : icosahedralRotationGroup =>
    ((A : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ)) h
  exact Subtype.ext (realQuarter_injective h1)

theorem dotProduct_halveToReal (a b : Fin 3 → Zsqrt5) :
    halveToReal a ⬝ᵥ halveToReal b = zsqrt5ToReal (dot3 a b) / 4 := by
  simp [halveToReal, dot3, dotProduct, Fin.sum_univ_three]
  ring

theorem colsMat_halveToReal (a b c : Fin 3 → Zsqrt5) :
    (Matrix.of fun k j => (![halveToReal a, halveToReal b, halveToReal c] :
      Fin 3 → Fin 3 → ℝ) j k).det = zsqrt5ToReal (tripleDet a b c) / 8 := by
  simp [Matrix.det_fin_three, halveToReal, tripleDet]
  ring

/-- Real column matrix. -/
noncomputable def colsMatR (a b c : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun k j => (![a, b, c] : Fin 3 → Fin 3 → ℝ) j k

theorem colsMatR_mul (A : Matrix (Fin 3) (Fin 3) ℝ) (a b c : Fin 3 → ℝ) :
    A * colsMatR a b c = colsMatR (A *ᵥ a) (A *ᵥ b) (A *ᵥ c) := by
  refine Matrix.ext fun i j => ?_
  fin_cases j <;> rfl

/-- Every element of the official stabilizer is one of the sixty, normalised over `ℝ`. -/
theorem toIcosahedralRotationGroup_surjective :
    Function.Surjective toIcosahedralRotationGroup := by
  rintro ⟨A, hA⟩
  rw [mem_icosahedralRotationGroup_iff] at hA
  unfold mem_icosahedralRotationGroup at hA
  set M : Matrix (Fin 3) (Fin 3) ℝ := (A : Matrix (Fin 3) (Fin 3) ℝ) with hM
  have hO : Mᵀ * M = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp (Matrix.mem_specialOrthogonalGroup_iff.mp A.2).1
  have hdet : M.det = 1 := (Matrix.mem_specialOrthogonalGroup_iff.mp A.2).2
  -- images of the three chosen vertices
  have himg : ∀ v ∈ icosahedronVerticesZsqrt5, ∃ w ∈ icosahedronVerticesZsqrt5,
      M *ᵥ halveToReal v = halveToReal w := by
    intro v hv
    have hx : M *ᵥ halveToReal v ∈ icosahedronVertexSet := by
      rw [← hA]; exact ⟨_, halveToReal_mem_icosahedronVertexSet hv, rfl⟩
    rw [← halveToReal_image_icosahedronVerticesZsqrt5] at hx
    obtain ⟨w, hw, h⟩ := hx
    exact ⟨w, hw, h.symm⟩
  obtain ⟨a, ha, hMa⟩ := himg vtxA vtxA_mem
  obtain ⟨b, hb, hMb⟩ := himg vtxB vtxB_mem
  obtain ⟨c, hc, hMc⟩ := himg vtxC vtxC_mem
  have hdot : ∀ x y : Fin 3 → ℝ, (M *ᵥ x) ⬝ᵥ (M *ᵥ y) = x ⬝ᵥ y := by
    intro x y
    rw [← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hO,
      Matrix.one_mulVec]
  have hd : ∀ {v w a b : Fin 3 → Zsqrt5}, M *ᵥ halveToReal v = halveToReal a →
      M *ᵥ halveToReal w = halveToReal b → dot3 a b = dot3 v w := by
    intro v w a b h1 h2
    have := hdot (halveToReal v) (halveToReal w)
    rw [h1, h2, dotProduct_halveToReal, dotProduct_halveToReal] at this
    exact zsqrt5ToReal_injective (by linarith)
  have htd : tripleDet a b c = tripleDet vtxA vtxB vtxC := by
    have h := congrArg Matrix.det (colsMatR_mul M (halveToReal vtxA) (halveToReal vtxB)
      (halveToReal vtxC))
    rw [Matrix.det_mul, hdet, hMa, hMb, hMc] at h
    unfold colsMatR at h
    rw [colsMat_halveToReal, colsMat_halveToReal] at h
    exact zsqrt5ToReal_injective (by linarith)
  obtain ⟨C, hC, hCa, hCb, hCc⟩ := triple_check a ha b hb c hc
    (hd hMa hMb) (hd hMa hMc) (hd hMb hMc) htd
  have hCmem : C.toMatrix ∈ scaledIcosahedralRotations :=
    mem_scaledIcosahedralRotations.mpr ⟨C, hC, rfl⟩
  refine ⟨⟨C.toMatrix, hCmem⟩, ?_⟩
  -- `realQuarter C` and `M` agree on three independent vectors.
  have hCa' := realQuarter_mulVec_halveToReal C.toMatrix (by rw [M3.toMatrix_mulVec]; exact hCa)
  have hCb' := realQuarter_mulVec_halveToReal C.toMatrix (by rw [M3.toMatrix_mulVec]; exact hCb)
  have hCc' := realQuarter_mulVec_halveToReal C.toMatrix (by rw [M3.toMatrix_mulVec]; exact hCc)
  set V := colsMatR (halveToReal vtxA) (halveToReal vtxB) (halveToReal vtxC) with hV
  have hVdet : V.det ≠ 0 := by
    rw [hV]; unfold colsMatR
    rw [colsMat_halveToReal]
    have : zsqrt5ToReal (tripleDet vtxA vtxB vtxC) ≠ 0 := by
      intro h0
      exact tripleDet_vtx_ne_zero (zsqrt5ToReal_injective (by rw [h0, map_zero]))
    exact div_ne_zero this (by norm_num)
  have hcols : realQuarter C.toMatrix * V = M * V := by
    rw [hV, colsMatR_mul, colsMatR_mul, hCa', hCb', hCc', hMa, hMb, hMc]
  have h2 := congrArg (· * V.adjugate) hcols
  simp only [Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one] at h2
  have heq : realQuarter C.toMatrix = M := by
    refine Matrix.ext fun i j => ?_
    have := congrFun (congrFun h2 i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at this
    exact mul_left_cancel₀ hVdet this
  apply Subtype.ext
  apply Subtype.ext
  exact heq

/-- (b′) The official `SO(3, ℝ)` stabilizer `icosahedralRotationGroup` of
`icosahedronVertexSet` has exactly sixty elements. -/
theorem icosahedralRotationGroup_natCard : Nat.card icosahedralRotationGroup = 60 := by
  rw [← Nat.card_eq_of_bijective toIcosahedralRotationGroup
    ⟨toIcosahedralRotationGroup_injective, toIcosahedralRotationGroup_surjective⟩,
    Nat.card_eq_fintype_card, Fintype.card_coe, scaledIcosahedralRotations_card]

/-! ### Multiplicativity -/

theorem realQuarter_mul_of_eq_smul {A B C : Matrix (Fin 3) (Fin 3) Zsqrt5}
    (h : A * B = (4 : Zsqrt5) • C) : realQuarter A * realQuarter B = realQuarter C := by
  have hm : A.map zsqrt5ToReal * B.map zsqrt5ToReal = (4 : ℝ) • C.map zsqrt5ToReal := by
    rw [← Matrix.map_mul, h]
    refine Matrix.ext fun i j => ?_
    simp [map_ofNat]
  rw [realQuarter, realQuarter, realQuarter, Matrix.smul_mul, Matrix.mul_smul, hm, smul_smul,
    smul_smul]
  norm_num

/-- Hom compatibility: if `S * T = 4 • U` then the images multiply to the image of `U`. -/
theorem toIcosahedralRotationGroup_mul_of_eq_smul (S T U : scaledIcosahedralRotations)
    (h : (S : Matrix (Fin 3) (Fin 3) Zsqrt5) * T = (4 : Zsqrt5) • (U : Matrix (Fin 3) (Fin 3) Zsqrt5)) :
    toIcosahedralRotationGroup S * toIcosahedralRotationGroup T = toIcosahedralRotationGroup U := by
  apply Subtype.ext
  apply Subtype.ext
  exact realQuarter_mul_of_eq_smul h

theorem smul_four_cancel {C D : Matrix (Fin 3) (Fin 3) Zsqrt5}
    (h : (4 : Zsqrt5) • C = (4 : Zsqrt5) • D) : C = D := by
  refine Matrix.ext fun i j => ?_
  have := congrFun (congrFun h i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  exact mul_left_cancel₀ (by decide) this

/-- The scaled product on the sixty: the unique `U` in the set with `S * T = 4 • U`. -/
noncomputable def scaledMul (S T : scaledIcosahedralRotations) : scaledIcosahedralRotations :=
  ⟨Classical.choose (scaledIcosahedralRotations_mul_mem S S.2 T T.2),
    (Classical.choose_spec (scaledIcosahedralRotations_mul_mem S S.2 T T.2)).1⟩

theorem scaledMul_spec (S T : scaledIcosahedralRotations) :
    (S : Matrix (Fin 3) (Fin 3) Zsqrt5) * T =
      (4 : Zsqrt5) • (scaledMul S T : Matrix (Fin 3) (Fin 3) Zsqrt5) :=
  (Classical.choose_spec (scaledIcosahedralRotations_mul_mem S S.2 T T.2)).2

theorem scaledMul_eq_iff (S T U : scaledIcosahedralRotations) :
    scaledMul S T = U ↔
      (S : Matrix (Fin 3) (Fin 3) Zsqrt5) * T = (4 : Zsqrt5) • (U : Matrix (Fin 3) (Fin 3) Zsqrt5) := by
  constructor
  · rintro rfl; exact scaledMul_spec S T
  · intro h; exact Subtype.ext (smul_four_cancel ((scaledMul_spec S T).symm.trans h))

noncomputable instance : Mul scaledIcosahedralRotations := ⟨scaledMul⟩

theorem scaledIcosahedralRotations_mul_def (S T : scaledIcosahedralRotations) :
    S * T = scaledMul S T := rfl

theorem toIcosahedralRotationGroup_map_mul (S T : scaledIcosahedralRotations) :
    toIcosahedralRotationGroup (S * T) =
      toIcosahedralRotationGroup S * toIcosahedralRotationGroup T :=
  (toIcosahedralRotationGroup_mul_of_eq_smul S T _ (scaledMul_spec S T)).symm

/-- The sixty scaled matrices, with the scaled product, are multiplicatively isomorphic to
the official `icosahedralRotationGroup`. -/
noncomputable def scaledIcosahedralMulEquiv :
    scaledIcosahedralRotations ≃* icosahedralRotationGroup :=
  MulEquiv.mk' (Equiv.ofBijective toIcosahedralRotationGroup
    ⟨toIcosahedralRotationGroup_injective, toIcosahedralRotationGroup_surjective⟩)
    toIcosahedralRotationGroup_map_mul

theorem scaledIcosahedralMulEquiv_apply (S : scaledIcosahedralRotations) :
    scaledIcosahedralMulEquiv S = toIcosahedralRotationGroup S := rfl

noncomputable instance : One scaledIcosahedralRotations := ⟨scaledIcosahedralMulEquiv.symm 1⟩

noncomputable instance : Inv scaledIcosahedralRotations :=
  ⟨fun S => scaledIcosahedralMulEquiv.symm (scaledIcosahedralMulEquiv S)⁻¹⟩

/-- The sixty scaled matrices form a group under the scaled product `scaledMul`
(identity and inverse transported along `scaledIcosahedralMulEquiv`). -/
noncomputable instance scaledIcosahedralGroup : Group scaledIcosahedralRotations :=
  Group.ofLeftAxioms
    (fun a b c => scaledIcosahedralMulEquiv.injective (by simp [map_mul, mul_assoc]))
    (fun a => scaledIcosahedralMulEquiv.injective (by
      rw [map_mul]; change scaledIcosahedralMulEquiv (scaledIcosahedralMulEquiv.symm 1) * _ = _
      simp))
    (fun a => scaledIcosahedralMulEquiv.injective (by
      rw [map_mul]
      change scaledIcosahedralMulEquiv
        (scaledIcosahedralMulEquiv.symm (scaledIcosahedralMulEquiv a)⁻¹) * _ =
        scaledIcosahedralMulEquiv (scaledIcosahedralMulEquiv.symm 1)
      simp))

/-- The identity of that group is the scaled identity `4 • 1`. -/
theorem scaledIcosahedralGroup_one_coe :
    ((1 : scaledIcosahedralRotations) : Matrix (Fin 3) (Fin 3) Zsqrt5) =
      (4 : Zsqrt5) • (1 : Matrix (Fin 3) (Fin 3) Zsqrt5) := by
  have h1 : (⟨(4 : Zsqrt5) • 1, scaledIcosahedralRotations_scaled_one_mem⟩ :
      scaledIcosahedralRotations) = 1 := by
    apply scaledIcosahedralMulEquiv.injective
    rw [map_one, scaledIcosahedralMulEquiv_apply]
    apply Subtype.ext; apply Subtype.ext
    change realQuarter ((4 : Zsqrt5) • 1) = 1
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [realQuarter, map_ofNat]
  rw [← h1]

#print axioms icosahedralRotationGroup_natCard
#print axioms toIcosahedralRotationGroup_mul_of_eq_smul
#print axioms toIcosahedralRotationGroup_map_mul
#print axioms scaledIcosahedralMulEquiv
#print axioms scaledIcosahedralGroup
#print axioms scaledIcosahedralGroup_one_coe
