/-
Scratch file, dated 2026-11-10. Not a Lake target. Not peer reviewed.

Order-2 converse and the count of 15 edge sign-pairs.

Imports `IcosahedralFramesReal_2026-11-10` (src 2e84adfe…). No text is copied.

* `scaledInvolution_fixes_edgeSum` (decide): every listed scaled matrix `A ≠ 4·I` with
  `A·A = 16·I` fixes (up to the factor 4) some edge sum; `scaledInvolutions_length`: there
  are exactly 15 such matrices.
* `icosahedralRotationGroup_involution_fixes_edgeVector`: every `g ≠ 1` with `g * g = 1`
  in the imported official group fixes some official edge vector. Together with
  `officialEdgeVectors_fixed_by_involution` this gives both directions.
* The sign-pairs `{p, -p}` of official edge vectors `p` (edge vectors up to sign): there
  are exactly 15 of them; over ℤ[√5], a list of one sign representative per pair `±x` has
  length 15.
identifier names are historical; no geometric line/axis claim is made

Cube point-sets are not touched here.
-/

import «IcosahedralFramesReal_2026-11-10»

open Equiv Matrix

/-! ### Involutions among the sixty (ℤ[√5] model) -/

/-- The listed scaled matrices of order 2 (up to scale): `A ≠ 4·I`, `A·A = 16·I`. -/
def scaledInvolutions : List M3 :=
  scaledRotationList.filter fun A => decide (A ≠ M3.scal 4 ∧ A.mul A = M3.scal 16)

theorem scaledInvolutions_length : scaledInvolutions.length = 15 := by decide +kernel

/-- Each such matrix fixes, up to the factor 4, some edge sum. -/
theorem scaledInvolution_fixes_edgeSum :
    ∀ A ∈ scaledRotationList, A ≠ M3.scal 4 → A.mul A = M3.scal 16 →
      ∃ x ∈ edgeSums, A.mulVec x = (4 : Zsqrt5) • x := by
  decide +kernel

/-! ### Order-2 converse over ℝ -/

/-- Every non-identity `g` with `g * g = 1` in the imported official group fixes some
official edge vector. -/
theorem icosahedralRotationGroup_involution_fixes_edgeVector (g : icosahedralRotationGroup)
    (hg1 : g ≠ 1) (hg2 : g * g = 1) :
    ∃ p ∈ officialEdgeVectors,
      ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ p = p := by
  have hmat : ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) =
      realQuarter (repM3 (scaledIcosahedralMulEquiv.symm g)).toMatrix := by
    rw [repM3_toMatrix]
    conv_lhs => rw [← scaledIcosahedralMulEquiv.apply_symm_apply g]
    rfl
  have hS2 : scaledIcosahedralMulEquiv.symm g * scaledIcosahedralMulEquiv.symm g = 1 := by
    rw [← map_mul, hg2, map_one]
  have hS1 : scaledIcosahedralMulEquiv.symm g ≠ 1 := by
    intro h
    apply hg1
    rw [← scaledIcosahedralMulEquiv.apply_symm_apply g, h, map_one]
  rw [hmat]
  generalize scaledIcosahedralMulEquiv.symm g = S at hS1 hS2
  have hA := repM3_mem S
  have hsq : (repM3 S).mul (repM3 S) = M3.scal 16 := by
    apply M3.toMatrix_injective
    rw [M3.toMatrix_mul, repM3_toMatrix, M3.toMatrix_scal]
    have h := (scaledMul_eq_iff S S 1).mp (by rw [← scaledIcosahedralRotations_mul_def]; exact hS2)
    rw [h, scaledIcosahedralGroup_one_coe, smul_smul]
    norm_num
  have hne : repM3 S ≠ M3.scal 4 := by
    intro h
    apply hS1
    apply Subtype.ext
    rw [scaledIcosahedralGroup_one_coe, ← repM3_toMatrix, h, M3.toMatrix_scal]
  obtain ⟨x, hx, hfix⟩ := scaledInvolution_fixes_edgeSum _ hA hne hsq
  refine ⟨halveToReal x, (officialEdgeVectors_eq_image ▸ ⟨x, hx, rfl⟩ :
    halveToReal x ∈ officialEdgeVectors), ?_⟩
  exact realQuarter_mulVec_halveToReal _ (by rw [M3.toMatrix_mulVec]; exact hfix)

/-! ### The count of 15 sign-pairs -/

/-- One representative of each pair `±x` of edge sums: the one listed first. -/
def edgeAxisReps : List (Fin 3 → Zsqrt5) :=
  edgeSums.filter fun x => decide (edgeSums.idxOf x < edgeSums.idxOf (-x))

theorem edgeAxisReps_length : edgeAxisReps.length = 15 := by decide +kernel

theorem edgeAxisReps_cover : ∀ x ∈ edgeSums, x ∈ edgeAxisReps ∨ -x ∈ edgeAxisReps := by
  decide +kernel

theorem edgeAxisReps_neg_not_mem : ∀ x ∈ edgeAxisReps, -x ∉ edgeAxisReps := by
  decide +kernel

theorem edgeAxisReps_subset : ∀ x ∈ edgeAxisReps, x ∈ edgeSums := by
  intro x hx
  simp only [edgeAxisReps, List.mem_filter] at hx
  exact hx.1

theorem edgeAxisReps_nodup : edgeAxisReps.Nodup := by
  unfold edgeAxisReps edgeSums
  exact (List.nodup_dedup _).filter _

/-- The official edge vectors up to sign: the sets `{p, -p}`. -/
def officialEdgeLines : Set (Set (Fin 3 → ℝ)) :=
  (fun p => ({p, -p} : Set (Fin 3 → ℝ))) '' officialEdgeVectors

theorem officialEdgeLines_eq :
    officialEdgeLines =
      (fun p => ({p, -p} : Set (Fin 3 → ℝ))) '' (halveToReal '' {x | x ∈ edgeAxisReps}) := by
  ext L
  simp only [officialEdgeLines, officialEdgeVectors_eq_image, Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨p, ⟨x, hx, rfl⟩, rfl⟩
    rcases edgeAxisReps_cover x hx with h | h
    · exact ⟨halveToReal x, ⟨x, h, rfl⟩, rfl⟩
    · refine ⟨halveToReal (-x), ⟨-x, h, rfl⟩, ?_⟩
      rw [halveToReal_neg, neg_neg, Set.pair_comm]
  · rintro ⟨p, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨halveToReal x, ⟨x, edgeAxisReps_subset x hx, rfl⟩, rfl⟩

/-- There are exactly 15 official edge sign-pairs `{p, -p}`. -/
theorem officialEdgeLines_ncard : officialEdgeLines.ncard = 15 := by
  have hinj : Set.InjOn (fun p => ({p, -p} : Set (Fin 3 → ℝ)))
      (halveToReal '' {x | x ∈ edgeAxisReps}) := by
    rintro a ⟨x, hx, rfl⟩ b ⟨y, hy, rfl⟩ hab
    have hb : halveToReal y ∈ ({halveToReal x, -halveToReal x} : Set (Fin 3 → ℝ)) := by
      rw [show ({halveToReal x, -halveToReal x} : Set (Fin 3 → ℝ)) =
        {halveToReal y, -halveToReal y} from hab]
      exact Set.mem_insert _ _
    rcases hb with h | h
    · exact h.symm
    · rw [← halveToReal_neg] at h
      have := halveToReal_injective h
      exact absurd (this ▸ hy) (edgeAxisReps_neg_not_mem x hx)
  rw [officialEdgeLines_eq, hinj.ncard_image, ncard_image_list edgeAxisReps_nodup,
    edgeAxisReps_length]

#print axioms scaledInvolutions_length
#print axioms scaledInvolution_fixes_edgeSum
#print axioms icosahedralRotationGroup_involution_fixes_edgeVector
#print axioms edgeAxisReps_length
#print axioms officialEdgeLines_ncard
