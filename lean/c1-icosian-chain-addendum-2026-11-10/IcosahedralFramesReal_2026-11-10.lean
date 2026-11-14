/-
Scratch file, dated 2026-11-10. Not a Lake target. Not peer reviewed.

Real frames on the official vertex set.

Imports the frames v2 module `IcosahedralFramesGeometric_v2_2026-11-10`. No text is copied.

Definitions are stated over ℝ on the official `icosahedronVertexSet`:
* `officialEdgeVectors`: `u + w` for official vertices `u, w` with `(u - w) ⬝ᵥ (u - w) = 4`
  (squared edge length 4; `officialEdge_sq_dist_min` shows 4 is the least nonzero squared
  distance between official vertices).
* `officialFrameOf m`: the official edge vectors `p` with `p ⬝ᵥ m = 0` or `p ×₃ m = 0`.
* `officialFrame i := officialFrameOf (officialFrameRep i)`, with `officialFrameRep i` an
  explicit real vector in `φ = Real.goldenRatio` (a label only).

The ℝ properties are proved by a transfer from the ℤ[√5] model (bridge lemma + the
injective map `halveToReal`), without `framePermM3`. Only the group-action statement
mentions the table's permutation, via the existing isomorphism (not redefined).

`officialEdgeVectors_fixed_by_involution`: each official edge vector is fixed by a
non-identity element of order 2 of the official group. No classical-solid claim about the
frames is made here.
-/

import «IcosahedralFramesGeometric_v2_2026-11-10»
import Mathlib.LinearAlgebra.CrossProduct

open Equiv Matrix

/-! ### Definitions over ℝ -/

/-- Edge vectors of the official icosahedron: `u + w` for official vertices at squared
distance `4` (twice the edge midpoints). -/
def officialEdgeVectors : Set (Fin 3 → ℝ) :=
  {p | ∃ u ∈ icosahedronVertexSet, ∃ w ∈ icosahedronVertexSet,
    (u - w) ⬝ᵥ (u - w) = 4 ∧ p = u + w}

/-- The real frame through `m`: the official edge vectors orthogonal or parallel to `m`. -/
def officialFrameOf (m : Fin 3 → ℝ) : Set (Fin 3 → ℝ) :=
  {p | p ∈ officialEdgeVectors ∧ (p ⬝ᵥ m = 0 ∨ crossProduct p m = 0)}

/-- Explicit real representatives (labels only), in terms of the golden ratio. -/
noncomputable def officialFrameRep : Fin 5 → (Fin 3 → ℝ) :=
  ![![Real.goldenRatio, 1, Real.goldenRatio + 1],
    ![1, Real.goldenRatio + 1, Real.goldenRatio],
    ![-Real.goldenRatio, 1, Real.goldenRatio + 1],
    ![0, 0, 2 * Real.goldenRatio],
    ![-1, Real.goldenRatio + 1, Real.goldenRatio]]

/-- The five real frames on the official vertex set. -/
noncomputable def officialFrame (i : Fin 5) : Set (Fin 3 → ℝ) := officialFrameOf (officialFrameRep i)

/-! ### Finite checks in the ℤ[√5] model (no table) -/

theorem edgeVAdd_mem_edgeSums :
    ∀ u ∈ icosahedronVerticesZsqrt5, ∀ w ∈ icosahedronVerticesZsqrt5,
      dot3 (edgeVSub u w) (edgeVSub u w) = 16 → edgeVAdd u w ∈ edgeSums := by
  decide +kernel

theorem edgeSums_mem_edge :
    ∀ x ∈ edgeSums, ∃ u ∈ icosahedronVerticesZsqrt5, ∃ w ∈ icosahedronVerticesZsqrt5,
      dot3 (edgeVSub u w) (edgeVSub u w) = 16 ∧ x = edgeVAdd u w := by
  decide +kernel

/-- Squared distances between listed vertices are `0`, `16`, `24 + 8√5` or `40 + 8√5`. -/
theorem vertex_sq_dist_cases :
    ∀ u ∈ icosahedronVerticesZsqrt5, ∀ w ∈ icosahedronVerticesZsqrt5,
      dot3 (edgeVSub u w) (edgeVSub u w) = 0 ∨ dot3 (edgeVSub u w) (edgeVSub u w) = 16 ∨
      dot3 (edgeVSub u w) (edgeVSub u w) = ⟨24, 8⟩ ∨
      dot3 (edgeVSub u w) (edgeVSub u w) = ⟨40, 8⟩ := by
  decide +kernel

theorem vertex_sq_dist_zero :
    ∀ u ∈ icosahedronVerticesZsqrt5, ∀ w ∈ icosahedronVerticesZsqrt5,
      dot3 (edgeVSub u w) (edgeVSub u w) = 0 → u = w := by
  decide +kernel

theorem zero_not_mem_edgeSums : (0 : Fin 3 → Zsqrt5) ∉ edgeSums := by decide +kernel

theorem frame_neg_mem : ∀ i : Fin 5, ∀ x ∈ frame i, -x ∈ frame i := by decide +kernel

theorem frame_disjoint :
    ∀ i j : Fin 5, i ≠ j → ∀ x ∈ frame i, x ∉ frame j := by decide +kernel

theorem edgeSums_mem_some_frame : ∀ x ∈ edgeSums, ∃ i : Fin 5, x ∈ frame i := by
  decide +kernel

/-- Each edge sum is fixed by a scaled matrix `A ≠ 4·I` with `A·A = 16·I`. -/
theorem edgeSums_fixed_by_involution :
    ∀ x ∈ edgeSums, ∃ A ∈ scaledRotationList,
      A ≠ M3.scal 4 ∧ A.mul A = M3.scal 16 ∧ A.mulVec x = (4 : Zsqrt5) • x := by
  decide +kernel

/-! ### Transfer lemmas -/

theorem halveToReal_zero : halveToReal 0 = 0 := by
  funext k; simp [halveToReal]

theorem halveToReal_eq_zero_iff (x : Fin 3 → Zsqrt5) : halveToReal x = 0 ↔ x = 0 := by
  rw [← halveToReal_zero]; exact halveToReal_injective.eq_iff

theorem halveToReal_neg (x : Fin 3 → Zsqrt5) : halveToReal (-x) = -halveToReal x := by
  funext k; simp [halveToReal, neg_div]

theorem halveToReal_edgeVSub (u w : Fin 3 → Zsqrt5) :
    halveToReal (edgeVSub u w) = halveToReal u - halveToReal w := by
  funext k; fin_cases k <;> simp [halveToReal, edgeVSub, map_sub] <;> ring

theorem halveToReal_edgeVAdd (u w : Fin 3 → Zsqrt5) :
    halveToReal (edgeVAdd u w) = halveToReal u + halveToReal w := by
  funext k; fin_cases k <;> simp [halveToReal, edgeVAdd, map_add] <;> ring

theorem zsqrt5ToReal_eq_zero_iff (z : Zsqrt5) : zsqrt5ToReal z = 0 ↔ z = 0 := by
  rw [← map_zero zsqrt5ToReal]; exact zsqrt5ToReal_injective.eq_iff

theorem halveToReal_dot_eq_zero_iff (a b : Fin 3 → Zsqrt5) :
    halveToReal a ⬝ᵥ halveToReal b = 0 ↔ dot3 a b = 0 := by
  rw [dotProduct_halveToReal, div_eq_zero_iff, zsqrt5ToReal_eq_zero_iff]
  norm_num

theorem crossProduct_halveToReal (a b : Fin 3 → Zsqrt5) :
    crossProduct (halveToReal a) (halveToReal b) = (1 / 2 : ℝ) • halveToReal (cross3 a b) := by
  funext k
  fin_cases k <;> simp [cross_apply, halveToReal, cross3, map_sub, map_mul] <;> ring

theorem halveToReal_cross_eq_zero_iff (a b : Fin 3 → Zsqrt5) :
    crossProduct (halveToReal a) (halveToReal b) = 0 ↔ cross3 a b = 0 := by
  rw [crossProduct_halveToReal, smul_eq_zero, halveToReal_eq_zero_iff]
  norm_num

theorem officialFrameRep_eq (i : Fin 5) : officialFrameRep i = halveToReal (frameRep i) := by
  have h5 : Real.goldenRatio = (1 + Real.sqrt 5) / 2 := rfl
  fin_cases i <;> funext k <;> fin_cases k <;>
    simp [officialFrameRep, frameRep, halveToReal, zsqrt5ToReal_apply, h5] <;> ring

/-- The real edge vectors are the halved real images of the ℤ[√5] edge sums. -/
theorem officialEdgeVectors_eq_image :
    officialEdgeVectors = halveToReal '' {x | x ∈ edgeSums} := by
  ext p
  constructor
  · rintro ⟨u, hu, w, hw, hd, rfl⟩
    rw [← halveToReal_image_icosahedronVerticesZsqrt5] at hu hw
    obtain ⟨u', hu', rfl⟩ := hu
    obtain ⟨w', hw', rfl⟩ := hw
    have h16 : dot3 (edgeVSub u' w') (edgeVSub u' w') = 16 := by
      rw [← halveToReal_edgeVSub, dotProduct_halveToReal] at hd
      apply zsqrt5ToReal_injective
      rw [map_ofNat]
      linarith
    exact ⟨edgeVAdd u' w', edgeVAdd_mem_edgeSums u' hu' w' hw' h16, halveToReal_edgeVAdd u' w'⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨u, hu, w, hw, hd, rfl⟩ := edgeSums_mem_edge x hx
    refine ⟨halveToReal u, halveToReal_mem_icosahedronVertexSet hu,
      halveToReal w, halveToReal_mem_icosahedronVertexSet hw, ?_, halveToReal_edgeVAdd u w⟩
    rw [← halveToReal_edgeVSub, dotProduct_halveToReal, hd]
    norm_num [map_ofNat]

/-- The real frames on the official vertex set equal the images of the ℤ[√5] frames. -/
theorem officialFrame_eq_realFrame (i : Fin 5) : officialFrame i = realFrame i := by
  ext p
  simp only [officialFrame, officialFrameOf, realFrame, officialEdgeVectors_eq_image,
    Set.mem_ofPred_eq, Set.mem_image, officialFrameRep_eq]
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, h⟩
    refine ⟨x, ?_, rfl⟩
    simp only [frame, frameOf, List.mem_filter, decide_eq_true_eq]
    rw [halveToReal_dot_eq_zero_iff, halveToReal_cross_eq_zero_iff] at h
    exact ⟨hx, h⟩
  · rintro ⟨x, hx, rfl⟩
    simp only [frame, frameOf, List.mem_filter, decide_eq_true_eq] at hx
    refine ⟨⟨x, hx.1, rfl⟩, ?_⟩
    rw [halveToReal_dot_eq_zero_iff, halveToReal_cross_eq_zero_iff]
    exact hx.2

theorem mem_officialFrame_iff (i : Fin 5) (p : Fin 3 → ℝ) :
    p ∈ officialFrame i ↔ ∃ x ∈ frame i, halveToReal x = p := by
  rw [officialFrame_eq_realFrame]; rfl

theorem frame_subset_edgeSums (i : Fin 5) : ∀ x ∈ frame i, x ∈ edgeSums := by
  intro x hx
  simp only [frame, frameOf, List.mem_filter] at hx
  exact hx.1

/-! ### Properties over ℝ -/

theorem ncard_image_list {l : List (Fin 3 → Zsqrt5)} (hl : l.Nodup) :
    (halveToReal '' {x | x ∈ l}).ncard = l.length := by
  have : {x | x ∈ l} = ((l.toFinset : Finset _) : Set (Fin 3 → Zsqrt5)) := by
    ext x; simp
  rw [Set.ncard_image_of_injective _ halveToReal_injective, this, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup hl]

/-- There are 30 official edge vectors. -/
theorem officialEdgeVectors_ncard : officialEdgeVectors.ncard = 30 := by
  rw [officialEdgeVectors_eq_image,
    ncard_image_list (l := edgeSums) (by unfold edgeSums; exact List.nodup_dedup _),
    edgeSums_length]

theorem officialEdgeVectors_ne_zero : ∀ p ∈ officialEdgeVectors, p ≠ 0 := by
  rw [officialEdgeVectors_eq_image]
  rintro p ⟨x, hx, rfl⟩ h
  rw [halveToReal_eq_zero_iff] at h
  exact zero_not_mem_edgeSums (h ▸ hx)

theorem officialEdgeVectors_neg_mem : ∀ p ∈ officialEdgeVectors, -p ∈ officialEdgeVectors := by
  rw [officialEdgeVectors_eq_image]
  rintro p ⟨x, hx, rfl⟩
  exact ⟨-x, edgeSums_neg_mem x hx, halveToReal_neg x⟩

/-- `4` is the least nonzero squared distance between official vertices. -/
theorem officialEdge_sq_dist_min :
    ∀ u ∈ icosahedronVertexSet, ∀ w ∈ icosahedronVertexSet, u ≠ w → 4 ≤ (u - w) ⬝ᵥ (u - w) := by
  intro u hu w hw hne
  rw [← halveToReal_image_icosahedronVerticesZsqrt5] at hu hw
  obtain ⟨u', hu', rfl⟩ := hu
  obtain ⟨w', hw', rfl⟩ := hw
  rw [← halveToReal_edgeVSub, dotProduct_halveToReal]
  have h5 : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  rcases vertex_sq_dist_cases u' hu' w' hw' with h | h | h | h
  · exact absurd (by rw [vertex_sq_dist_zero u' hu' w' hw' h]) hne
  all_goals
    rw [h, zsqrt5ToReal_apply]
    norm_num
    try nlinarith

theorem officialFrame_subset (i : Fin 5) : officialFrame i ⊆ officialEdgeVectors :=
  fun _ hp => hp.1

/-- Each real frame has 6 elements. -/
theorem officialFrame_ncard (i : Fin 5) : (officialFrame i).ncard = 6 := by
  rw [officialFrame_eq_realFrame, realFrame,
    ncard_image_list (l := frame i)
      (by unfold frame frameOf edgeSums; exact (List.nodup_dedup _).filter _),
    frame_length]

/-- Within a real frame, any two vectors are orthogonal or parallel. -/
theorem officialFrame_orthogonal_or_parallel (i : Fin 5) :
    ∀ p ∈ officialFrame i, ∀ q ∈ officialFrame i, p ⬝ᵥ q = 0 ∨ crossProduct p q = 0 := by
  intro p hp q hq
  rw [mem_officialFrame_iff] at hp hq
  obtain ⟨x, hx, rfl⟩ := hp
  obtain ⟨y, hy, rfl⟩ := hq
  rw [halveToReal_dot_eq_zero_iff, halveToReal_cross_eq_zero_iff]
  exact frame_orthogonal_or_parallel i x hx y hy

/-- Each real frame is a union of sign-pairs `{p, -p}`. -/
theorem officialFrame_neg_mem (i : Fin 5) : ∀ p ∈ officialFrame i, -p ∈ officialFrame i := by
  intro p hp
  rw [mem_officialFrame_iff] at hp ⊢
  obtain ⟨x, hx, rfl⟩ := hp
  exact ⟨-x, frame_neg_mem i x hx, halveToReal_neg x⟩

/-- Distinct real frames are disjoint. -/
theorem officialFrame_disjoint {i j : Fin 5} (hij : i ≠ j) :
    Disjoint (officialFrame i) (officialFrame j) := by
  rw [Set.disjoint_left]
  intro p hpi hpj
  rw [mem_officialFrame_iff] at hpi hpj
  obtain ⟨x, hx, rfl⟩ := hpi
  obtain ⟨y, hy, hxy⟩ := hpj
  have : y = x := halveToReal_injective hxy
  subst this
  exact frame_disjoint i j hij y hx hy

theorem officialFrameRep_mem (i : Fin 5) : officialFrameRep i ∈ officialFrame i := by
  rw [mem_officialFrame_iff, officialFrameRep_eq]
  exact ⟨frameRep i, frameRep_mem_frame i, rfl⟩

/-- The five real frames are distinct. -/
theorem officialFrame_injective : Function.Injective officialFrame := by
  intro i j h
  by_contra hij
  have hi := officialFrameRep_mem i
  rw [h] at hi
  exact Set.disjoint_left.mp (officialFrame_disjoint hij) (officialFrameRep_mem i) hi

/-- Partition: every official edge vector lies in exactly one real frame. -/
theorem officialEdgeVectors_mem_unique_frame :
    ∀ p ∈ officialEdgeVectors, ∃! i : Fin 5, p ∈ officialFrame i := by
  intro p hp
  rw [officialEdgeVectors_eq_image] at hp
  obtain ⟨x, hx, rfl⟩ := hp
  obtain ⟨i, hi⟩ := edgeSums_mem_some_frame x hx
  refine ⟨i, (mem_officialFrame_iff i _).mpr ⟨x, hi, rfl⟩, fun j hj => ?_⟩
  by_contra hji
  exact Set.disjoint_left.mp (officialFrame_disjoint hji) hj
    ((mem_officialFrame_iff i _).mpr ⟨x, hi, rfl⟩)

theorem officialEdgeVectors_eq_iUnion : officialEdgeVectors = ⋃ i, officialFrame i := by
  ext p
  simp only [Set.mem_iUnion]
  constructor
  · intro hp
    obtain ⟨i, hi, -⟩ := officialEdgeVectors_mem_unique_frame p hp
    exact ⟨i, hi⟩
  · rintro ⟨i, hi⟩
    exact officialFrame_subset i hi

/-- No other orthogonal pairs: two orthogonal official edge vectors share a real frame. -/
theorem officialEdgeVectors_orthogonal_same_frame :
    ∀ p ∈ officialEdgeVectors, ∀ q ∈ officialEdgeVectors, p ⬝ᵥ q = 0 →
      ∃ i : Fin 5, p ∈ officialFrame i ∧ q ∈ officialFrame i := by
  intro p hp q hq hpq
  rw [officialEdgeVectors_eq_image] at hp hq
  obtain ⟨x, hx, rfl⟩ := hp
  obtain ⟨y, hy, rfl⟩ := hq
  rw [halveToReal_dot_eq_zero_iff] at hpq
  obtain ⟨i, hxi, hyi⟩ := orthogonal_edgeSums_same_frame x hx y hy hpq
  exact ⟨i, (mem_officialFrame_iff i _).mpr ⟨x, hxi, rfl⟩,
    (mem_officialFrame_iff i _).mpr ⟨y, hyi, rfl⟩⟩

/-- No other orthogonal triples: three pairwise orthogonal official edge vectors lie in one
real frame. -/
theorem officialEdgeVectors_orthogonal_triple_same_frame :
    ∀ p ∈ officialEdgeVectors, ∀ q ∈ officialEdgeVectors, ∀ r ∈ officialEdgeVectors,
      p ⬝ᵥ q = 0 → p ⬝ᵥ r = 0 → q ⬝ᵥ r = 0 →
        ∃ i : Fin 5, p ∈ officialFrame i ∧ q ∈ officialFrame i ∧ r ∈ officialFrame i := by
  intro p hp q hq r hr hpq hpr _
  obtain ⟨i, hpi, hqi⟩ := officialEdgeVectors_orthogonal_same_frame p hp q hq hpq
  obtain ⟨j, hpj, hrj⟩ := officialEdgeVectors_orthogonal_same_frame p hp r hr hpr
  have hij : i = j := by
    by_contra h
    exact Set.disjoint_left.mp (officialFrame_disjoint h) hpi hpj
  subst hij
  exact ⟨i, hpi, hqi, hrj⟩

/-- Each official edge vector is fixed by a non-identity element of order 2 of the
imported official group. -/
theorem officialEdgeVectors_fixed_by_involution :
    ∀ p ∈ officialEdgeVectors, ∃ g : icosahedralRotationGroup, g ≠ 1 ∧ g * g = 1 ∧
      ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ p = p := by
  intro p hp
  rw [officialEdgeVectors_eq_image] at hp
  obtain ⟨x, hx, rfl⟩ := hp
  obtain ⟨A, hA, hne, hsq, hfix⟩ := edgeSums_fixed_by_involution x hx
  let S : scaledIcosahedralRotations :=
    ⟨A.toMatrix, mem_scaledIcosahedralRotations.mpr ⟨A, hA, rfl⟩⟩
  have hSS : S * S = 1 := by
    rw [scaledIcosahedralRotations_mul_def, scaledMul_eq_iff, scaledIcosahedralGroup_one_coe,
      smul_smul]
    change A.toMatrix * A.toMatrix = _
    rw [← M3.toMatrix_mul, hsq, M3.toMatrix_scal]
    norm_num
  have hS1 : S ≠ 1 := by
    intro h
    apply hne
    apply M3.toMatrix_injective
    have := congrArg (fun T : scaledIcosahedralRotations =>
      (T : Matrix (Fin 3) (Fin 3) Zsqrt5)) h
    simp only [scaledIcosahedralGroup_one_coe] at this
    rw [M3.toMatrix_scal]
    exact this
  refine ⟨scaledIcosahedralMulEquiv S, ?_, ?_, ?_⟩
  · intro h
    exact hS1 (scaledIcosahedralMulEquiv.injective (h.trans (map_one _).symm))
  · rw [← map_mul, hSS, map_one]
  · change realQuarter A.toMatrix *ᵥ halveToReal x = halveToReal x
    exact realQuarter_mulVec_halveToReal _ (by rw [M3.toMatrix_mulVec]; exact hfix)

/-! ### The official group acts on the real frames by the table's permutation -/

/-- Every `g` in the imported official group maps real frame `i` onto real frame `σ(g) i`,
with `σ = icosahedralRotationGroupMulEquivAlternatingGroup` (unchanged). -/
theorem icosahedralRotationGroup_maps_officialFrame (g : icosahedralRotationGroup) (i : Fin 5) :
    (fun v => ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v) ''
        officialFrame i =
      officialFrame (((icosahedralRotationGroupMulEquivAlternatingGroup g :
        alternatingGroup (Fin 5)) : Perm (Fin 5)) i) := by
  rw [officialFrame_eq_realFrame, officialFrame_eq_realFrame]
  exact icosahedralRotationGroup_maps_realFrame g i

/-- ... and `σ(g) i` is the only real frame that `g` maps real frame `i` into. -/
theorem icosahedralRotationGroup_officialFrame_target_unique (g : icosahedralRotationGroup)
    (i j : Fin 5)
    (h : (fun v => ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v) ''
        officialFrame i ⊆ officialFrame j) :
    j = ((icosahedralRotationGroupMulEquivAlternatingGroup g :
        alternatingGroup (Fin 5)) : Perm (Fin 5)) i := by
  by_contra hj
  have hmem : ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ
      officialFrameRep i ∈
      (fun v => ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v) ''
        officialFrame i := ⟨_, officialFrameRep_mem i, rfl⟩
  have h2 := hmem
  rw [icosahedralRotationGroup_maps_officialFrame] at h2
  exact Set.disjoint_left.mp (officialFrame_disjoint hj) (h hmem) h2

#print axioms officialEdgeVectors_eq_image
#print axioms officialFrame_eq_realFrame
#print axioms officialEdgeVectors_ncard
#print axioms officialEdgeVectors_ne_zero
#print axioms officialEdgeVectors_neg_mem
#print axioms officialEdge_sq_dist_min
#print axioms officialFrame_ncard
#print axioms officialFrame_orthogonal_or_parallel
#print axioms officialFrame_neg_mem
#print axioms officialFrame_disjoint
#print axioms officialFrame_injective
#print axioms officialEdgeVectors_mem_unique_frame
#print axioms officialEdgeVectors_eq_iUnion
#print axioms officialEdgeVectors_orthogonal_same_frame
#print axioms officialEdgeVectors_orthogonal_triple_same_frame
#print axioms officialEdgeVectors_fixed_by_involution
#print axioms icosahedralRotationGroup_maps_officialFrame
#print axioms icosahedralRotationGroup_officialFrame_target_unique
