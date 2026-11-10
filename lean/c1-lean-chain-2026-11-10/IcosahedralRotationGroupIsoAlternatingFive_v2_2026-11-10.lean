/-
Scratch file, dated 2026-11-10. Table-driven wording (comments and
docstrings only; declarations unchanged from the first version of
this module). Not a Lake target. Not peer reviewed.

This file imports `IcosahedralRotationGroupImportedMulEquiv_2026-11-10`,
which in turn imports the official 2026-11-09 module
`IcosahedralRotationGroup_2026-11-09`. The name
`icosahedralRotationGroup` below is the imported official constant.
It also imports Mathlib's `alternatingGroup`.

Route (table-driven): the map is defined by a checked table of sixty
permutations of `Fin 5`, one per scaled matrix. The table was computed
by the exact script `a5_exact_qsqrt5_v2.py` from the action on the five
orthonormal triples of 2-fold axes; that geometric action is not defined
or proved in Lean. Here `decide +kernel` checks that the table is
multiplicative over all 60 × 60 products (in chunks), that every entry
is even, and that only the identity maps to `1`. The resulting
injective hom to `alternatingGroup (Fin 5)` is then bijective by counting
(60 = 60).
-/

import «IcosahedralRotationGroupImportedMulEquiv_2026-11-10»
import Mathlib.GroupTheory.SpecificGroups.Alternating

open Equiv

/-! ### The permutation table (table-driven; checked by `decide +kernel`) -/

/-- Sixty permutations of `Fin 5`, listed in the same order as `scaledRotationList`.
Entry `i` is the table entry for matrix `i`. The table was computed by
`a5_exact_qsqrt5_v2.py` from the frame action; Lean does not define
that geometric action. Every property used below is re-checked here by `decide +kernel`. -/
def framePermList : List (Perm (Fin 5)) :=
  [ ⟨![0, 1, 2, 3, 4], ![0, 1, 2, 3, 4], by decide, by decide⟩
  , ⟨![1, 0, 4, 3, 2], ![1, 0, 4, 3, 2], by decide, by decide⟩
  , ⟨![4, 2, 1, 3, 0], ![4, 2, 1, 3, 0], by decide, by decide⟩
  , ⟨![2, 1, 0, 4, 3], ![2, 1, 0, 4, 3], by decide, by decide⟩
  , ⟨![0, 4, 2, 1, 3], ![0, 3, 2, 4, 1], by decide, by decide⟩
  , ⟨![0, 4, 3, 2, 1], ![0, 4, 3, 2, 1], by decide, by decide⟩
  , ⟨![2, 1, 3, 0, 4], ![3, 1, 0, 2, 4], by decide, by decide⟩
  , ⟨![3, 1, 0, 2, 4], ![2, 1, 3, 0, 4], by decide, by decide⟩
  , ⟨![3, 4, 2, 0, 1], ![3, 4, 2, 0, 1], by decide, by decide⟩
  , ⟨![0, 3, 2, 4, 1], ![0, 4, 2, 1, 3], by decide, by decide⟩
  , ⟨![2, 3, 0, 1, 4], ![2, 3, 0, 1, 4], by decide, by decide⟩
  , ⟨![1, 0, 2, 4, 3], ![1, 0, 2, 4, 3], by decide, by decide⟩
  , ⟨![4, 2, 0, 1, 3], ![2, 3, 1, 4, 0], by decide, by decide⟩
  , ⟨![1, 0, 3, 2, 4], ![1, 0, 3, 2, 4], by decide, by decide⟩
  , ⟨![4, 2, 3, 0, 1], ![3, 4, 1, 2, 0], by decide, by decide⟩
  , ⟨![3, 4, 1, 2, 0], ![4, 2, 3, 0, 1], by decide, by decide⟩
  , ⟨![3, 1, 4, 0, 2], ![3, 1, 4, 0, 2], by decide, by decide⟩
  , ⟨![2, 3, 1, 4, 0], ![4, 2, 0, 1, 3], by decide, by decide⟩
  , ⟨![0, 3, 4, 1, 2], ![0, 3, 4, 1, 2], by decide, by decide⟩
  , ⟨![0, 2, 1, 4, 3], ![0, 2, 1, 4, 3], by decide, by decide⟩
  , ⟨![2, 0, 4, 1, 3], ![1, 3, 0, 4, 2], by decide, by decide⟩
  , ⟨![4, 1, 3, 2, 0], ![4, 1, 3, 2, 0], by decide, by decide⟩
  , ⟨![1, 4, 3, 0, 2], ![3, 0, 4, 2, 1], by decide, by decide⟩
  , ⟨![3, 0, 4, 2, 1], ![1, 4, 3, 0, 2], by decide, by decide⟩
  , ⟨![3, 2, 1, 0, 4], ![3, 2, 1, 0, 4], by decide, by decide⟩
  , ⟨![1, 3, 0, 4, 2], ![2, 0, 4, 1, 3], by decide, by decide⟩
  , ⟨![4, 3, 2, 1, 0], ![4, 3, 2, 1, 0], by decide, by decide⟩
  , ⟨![0, 4, 1, 3, 2], ![0, 2, 4, 3, 1], by decide, by decide⟩
  , ⟨![2, 1, 4, 3, 0], ![4, 1, 0, 3, 2], by decide, by decide⟩
  , ⟨![4, 1, 0, 3, 2], ![2, 1, 4, 3, 0], by decide, by decide⟩
  , ⟨![1, 4, 2, 3, 0], ![4, 0, 2, 3, 1], by decide, by decide⟩
  , ⟨![0, 2, 4, 3, 1], ![0, 4, 1, 3, 2], by decide, by decide⟩
  , ⟨![2, 0, 1, 3, 4], ![1, 2, 0, 3, 4], by decide, by decide⟩
  , ⟨![4, 0, 2, 3, 1], ![1, 4, 2, 3, 0], by decide, by decide⟩
  , ⟨![1, 2, 0, 3, 4], ![2, 0, 1, 3, 4], by decide, by decide⟩
  , ⟨![2, 3, 4, 0, 1], ![3, 4, 0, 1, 2], by decide, by decide⟩
  , ⟨![0, 3, 1, 2, 4], ![0, 2, 3, 1, 4], by decide, by decide⟩
  , ⟨![3, 4, 0, 1, 2], ![2, 3, 4, 0, 1], by decide, by decide⟩
  , ⟨![3, 1, 2, 4, 0], ![4, 1, 2, 0, 3], by decide, by decide⟩
  , ⟨![0, 2, 3, 1, 4], ![0, 3, 1, 2, 4], by decide, by decide⟩
  , ⟨![2, 0, 3, 4, 1], ![1, 4, 0, 2, 3], by decide, by decide⟩
  , ⟨![4, 1, 2, 0, 3], ![3, 1, 2, 4, 0], by decide, by decide⟩
  , ⟨![1, 4, 0, 2, 3], ![2, 0, 3, 4, 1], by decide, by decide⟩
  , ⟨![1, 3, 2, 0, 4], ![3, 0, 2, 1, 4], by decide, by decide⟩
  , ⟨![4, 3, 0, 2, 1], ![2, 4, 3, 1, 0], by decide, by decide⟩
  , ⟨![3, 0, 2, 1, 4], ![1, 3, 2, 0, 4], by decide, by decide⟩
  , ⟨![3, 2, 0, 4, 1], ![2, 4, 1, 0, 3], by decide, by decide⟩
  , ⟨![2, 4, 3, 1, 0], ![4, 3, 0, 2, 1], by decide, by decide⟩
  , ⟨![0, 1, 3, 4, 2], ![0, 1, 4, 2, 3], by decide, by decide⟩
  , ⟨![2, 4, 1, 0, 3], ![3, 2, 0, 4, 1], by decide, by decide⟩
  , ⟨![0, 1, 4, 2, 3], ![0, 1, 3, 4, 2], by decide, by decide⟩
  , ⟨![4, 3, 1, 0, 2], ![3, 2, 4, 1, 0], by decide, by decide⟩
  , ⟨![1, 3, 4, 2, 0], ![4, 0, 3, 1, 2], by decide, by decide⟩
  , ⟨![3, 2, 4, 1, 0], ![4, 3, 1, 0, 2], by decide, by decide⟩
  , ⟨![3, 0, 1, 4, 2], ![1, 2, 4, 0, 3], by decide, by decide⟩
  , ⟨![4, 0, 3, 1, 2], ![1, 3, 4, 2, 0], by decide, by decide⟩
  , ⟨![1, 2, 3, 4, 0], ![4, 0, 1, 2, 3], by decide, by decide⟩
  , ⟨![1, 2, 4, 0, 3], ![3, 0, 1, 4, 2], by decide, by decide⟩
  , ⟨![4, 0, 1, 2, 3], ![1, 2, 3, 4, 0], by decide, by decide⟩
  , ⟨![2, 4, 0, 3, 1], ![2, 4, 0, 3, 1], by decide, by decide⟩
  ]

theorem framePermList_length : framePermList.length = 60 := rfl

/-- The table permutation of an `M3`, looked up by its position in `scaledRotationList`
(and `1` for matrices outside the list). -/
def framePermM3 (A : M3) : Perm (Fin 5) :=
  (List.lookup A (scaledRotationList.zip framePermList)).getD 1

theorem framePermM3_mul_chunk0 :
    ∀ A ∈ scaledRotationChunk0, ∀ B ∈ scaledRotationList, ∀ C ∈ scaledRotationList,
      A.mul B = C.smul 4 → framePermM3 C = framePermM3 A * framePermM3 B := by
  decide +kernel

theorem framePermM3_mul_chunk1 :
    ∀ A ∈ scaledRotationChunk1, ∀ B ∈ scaledRotationList, ∀ C ∈ scaledRotationList,
      A.mul B = C.smul 4 → framePermM3 C = framePermM3 A * framePermM3 B := by
  decide +kernel

theorem framePermM3_mul_chunk2 :
    ∀ A ∈ scaledRotationChunk2, ∀ B ∈ scaledRotationList, ∀ C ∈ scaledRotationList,
      A.mul B = C.smul 4 → framePermM3 C = framePermM3 A * framePermM3 B := by
  decide +kernel

theorem framePermM3_mul_chunk3 :
    ∀ A ∈ scaledRotationChunk3, ∀ B ∈ scaledRotationList, ∀ C ∈ scaledRotationList,
      A.mul B = C.smul 4 → framePermM3 C = framePermM3 A * framePermM3 B := by
  decide +kernel

theorem framePermM3_mul_chunk4 :
    ∀ A ∈ scaledRotationChunk4, ∀ B ∈ scaledRotationList, ∀ C ∈ scaledRotationList,
      A.mul B = C.smul 4 → framePermM3 C = framePermM3 A * framePermM3 B := by
  decide +kernel

theorem framePermM3_mul_chunk5 :
    ∀ A ∈ scaledRotationChunk5, ∀ B ∈ scaledRotationList, ∀ C ∈ scaledRotationList,
      A.mul B = C.smul 4 → framePermM3 C = framePermM3 A * framePermM3 B := by
  decide +kernel


theorem framePermM3_mul :
    ∀ A ∈ scaledRotationList, ∀ B ∈ scaledRotationList, ∀ C ∈ scaledRotationList,
      A.mul B = C.smul 4 → framePermM3 C = framePermM3 A * framePermM3 B := by
  intro A hA
  simp only [scaledRotationList, List.mem_append] at hA
  rcases hA with ((((h | h) | h) | h) | h) | h
  exacts [framePermM3_mul_chunk0 A h, framePermM3_mul_chunk1 A h,
    framePermM3_mul_chunk2 A h, framePermM3_mul_chunk3 A h,
    framePermM3_mul_chunk4 A h, framePermM3_mul_chunk5 A h]

theorem framePermM3_sign : ∀ A ∈ scaledRotationList, Perm.sign (framePermM3 A) = 1 := by
  decide +kernel

theorem framePermM3_eq_one : ∀ A ∈ scaledRotationList, framePermM3 A = 1 → A = M3.scal 4 := by
  decide +kernel

/-! ### The frame homomorphism on the sixty -/

/-- A chosen `M3` representative (in `scaledRotationList`) of an element of the sixty. -/
noncomputable def repM3 (S : scaledIcosahedralRotations) : M3 :=
  Classical.choose (mem_scaledIcosahedralRotations.mp S.2)

theorem repM3_mem (S : scaledIcosahedralRotations) : repM3 S ∈ scaledRotationList :=
  (Classical.choose_spec (mem_scaledIcosahedralRotations.mp S.2)).1

theorem repM3_toMatrix (S : scaledIcosahedralRotations) :
    (repM3 S).toMatrix = (S : Matrix (Fin 3) (Fin 3) Zsqrt5) :=
  (Classical.choose_spec (mem_scaledIcosahedralRotations.mp S.2)).2

/-- The table permutation of an element of the sixty (looked up via its `M3` representative). -/
noncomputable def framePerm (S : scaledIcosahedralRotations) : Perm (Fin 5) :=
  framePermM3 (repM3 S)

theorem framePerm_mul (S T : scaledIcosahedralRotations) :
    framePerm (S * T) = framePerm S * framePerm T := by
  have hspec := scaledMul_spec S T
  have hST : S * T = scaledMul S T := rfl
  have key : (repM3 S).mul (repM3 T) = (repM3 (S * T)).smul 4 := by
    apply M3.toMatrix_injective
    rw [M3.toMatrix_mul, M3.toMatrix_smul, repM3_toMatrix, repM3_toMatrix, repM3_toMatrix, hST]
    exact hspec
  exact framePermM3_mul _ (repM3_mem S) _ (repM3_mem T) _ (repM3_mem (S * T)) key

/-- The table-driven group homomorphism from the sixty to `Perm (Fin 5)`. -/
noncomputable def frameHom : scaledIcosahedralRotations →* Perm (Fin 5) :=
  MonoidHom.mk' framePerm framePerm_mul

theorem frameHom_mem_alternatingGroup (S : scaledIcosahedralRotations) :
    frameHom S ∈ alternatingGroup (Fin 5) :=
  Equiv.Perm.mem_alternatingGroup.mpr (framePermM3_sign _ (repM3_mem S))

theorem frameHom_injective : Function.Injective frameHom := by
  rw [injective_iff_map_eq_one]
  intro S hS
  have h1 : repM3 S = M3.scal 4 := framePermM3_eq_one _ (repM3_mem S) hS
  apply Subtype.ext
  rw [scaledIcosahedralGroup_one_coe, ← repM3_toMatrix, h1, M3.toMatrix_scal]

/-- The frame homomorphism, with codomain `alternatingGroup (Fin 5)`. -/
noncomputable def frameHomA5 : scaledIcosahedralRotations →* alternatingGroup (Fin 5) :=
  frameHom.codRestrict (alternatingGroup (Fin 5)) frameHom_mem_alternatingGroup

/-! ### The official group -/

/-- The table-driven homomorphism on the imported official `icosahedralRotationGroup`. -/
noncomputable def icosahedralRotationGroupToAlternatingGroup :
    icosahedralRotationGroup →* alternatingGroup (Fin 5) :=
  frameHomA5.comp scaledIcosahedralMulEquiv.symm.toMonoidHom

theorem icosahedralRotationGroupToAlternatingGroup_injective :
    Function.Injective icosahedralRotationGroupToAlternatingGroup := by
  intro x y h
  have h' : frameHom (scaledIcosahedralMulEquiv.symm x) =
      frameHom (scaledIcosahedralMulEquiv.symm y) :=
    congrArg Subtype.val h
  exact scaledIcosahedralMulEquiv.symm.injective (frameHom_injective h')

theorem nat_card_alternatingGroup_fin_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem icosahedralRotationGroupToAlternatingGroup_bijective :
    Function.Bijective icosahedralRotationGroupToAlternatingGroup :=
  icosahedralRotationGroupToAlternatingGroup_injective.bijective_of_nat_card_le
    (by rw [nat_card_alternatingGroup_fin_five, icosahedralRotationGroup_natCard])

/-- I ≅ A₅: the imported official icosahedral rotation group is isomorphic to
`alternatingGroup (Fin 5)`. -/
noncomputable def icosahedralRotationGroupMulEquivAlternatingGroup :
    icosahedralRotationGroup ≃* alternatingGroup (Fin 5) :=
  MulEquiv.ofBijective icosahedralRotationGroupToAlternatingGroup
    icosahedralRotationGroupToAlternatingGroup_bijective

/-- I ≅ A₅ as a `Nonempty` statement. -/
theorem icosahedralRotationGroup_iso_alternatingGroup_fin_five :
    Nonempty (icosahedralRotationGroup ≃* alternatingGroup (Fin 5)) :=
  ⟨icosahedralRotationGroupMulEquivAlternatingGroup⟩

#print axioms framePermM3_mul
#print axioms framePermM3_sign
#print axioms framePermM3_eq_one
#print axioms frameHom_injective
#print axioms icosahedralRotationGroupToAlternatingGroup_injective
#print axioms icosahedralRotationGroupToAlternatingGroup_bijective
#print axioms icosahedralRotationGroupMulEquivAlternatingGroup
#print axioms icosahedralRotationGroup_iso_alternatingGroup_fin_five
