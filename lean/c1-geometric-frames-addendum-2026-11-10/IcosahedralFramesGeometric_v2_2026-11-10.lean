/-
Scratch file, dated 2026-11-10. Not a Lake target. Not peer reviewed.

Geometric frames for the I ≅ A₅ table, version 2. Version 2 changes versus
version 1 (src e08489350fb4b112b23f9054245f20d481147d3ece43613d07d65ba1f6f80f4d):
comments and docstrings softened ('2-fold axis' marked as a name only; the frame
numbering's agreement with an outside script marked as an outside comparison;
no classical solid claimed), plus the lemmas `halveToReal_injective`,
`frameRep_mem_frame_eq` and `realFrame_injective` (and the new `#print axioms`
line for `realFrame_injective`).

Caveat on names: '2-fold axis' below is only a name for the line of an edge sum.
No theorem in this file proves that such a line is the axis of an order-2 rotation.
Likewise nothing here proves that a frame is the vertex set of a classical solid.

Imports the module `IcosahedralRotationGroupIsoAlternatingFive_v2_2026-11-10`
(original src 6b7cce0c46ffbed065977f4d3fe517437648c138002c2b2a268461136461b573),
with no text copied.

Geometry (doubled-scale ℤ[√5] model built from the listed vertices; the bridge lemma
`halveToReal_image_icosahedronVerticesZsqrt5` identifies it with the official vertex set):
* `edgeSums`: the vectors `u + w` for listed vertices `u, w` at squared distance 16
  (the edges). There are 30, closed under negation, hence 15 sign-pairs ±x.
* `frameOf m`: the edge sums parallel or orthogonal to `m`.
* `frame i := frameOf (frameRep i)`, `frameRep i` a chosen edge sum (a label only).
  Each frame has 6 vectors, closed under negation,
  pairwise orthogonal or parallel. The five frames partition the edge sums, and two orthogonal
  edge sums always share a frame, so there are no other orthogonal triples.
* `frame_mapsTo` / `frame_mapsOnto` / `frame_target_unique`: each of the 60 scaled
  matrices `A` maps frame `i` onto frame `framePermM3 A i`, and onto no other frame.
  The table `framePermM3` is the geometric frame action, not just a lookup.
* `icosahedralRotationGroup_maps_realFrame`: the same over ℝ for the imported official
  group, with the permutation given by `icosahedralRotationGroupMulEquivAlternatingGroup`.
-/

import «IcosahedralRotationGroupIsoAlternatingFive_v2_2026-11-10»

open Equiv Matrix

/-! ### Edges and edge-sum vectors of the doubled-scale icosahedron over `ℤ[√5]` -/

/-- Coordinatewise difference. -/
def edgeVSub (u w : Fin 3 → Zsqrt5) : Fin 3 → Zsqrt5 := ![u 0 - w 0, u 1 - w 1, u 2 - w 2]

/-- Coordinatewise sum. -/
def edgeVAdd (u w : Fin 3 → Zsqrt5) : Fin 3 → Zsqrt5 := ![u 0 + w 0, u 1 + w 1, u 2 + w 2]

/-- Cross product (zero iff the vectors are parallel, for nonzero vectors). -/
def cross3 (u w : Fin 3 → Zsqrt5) : Fin 3 → Zsqrt5 :=
  ![u 1 * w 2 - u 2 * w 1, u 2 * w 0 - u 0 * w 2, u 0 * w 1 - u 1 * w 0]

/-- Edge sums: `u + w` for listed vertices `u, w` at squared distance `16` (the edge length
of the doubled-scale icosahedron is `4`), without repeats. Each is `4` times an edge
midpoint of the unit-scale icosahedron; its line is called a '2-fold axis' here as a
name only (no order-2 rotation statement is proved). -/
def edgeSums : List (Fin 3 → Zsqrt5) :=
  (icosahedronVerticesZsqrt5.flatMap fun u => icosahedronVerticesZsqrt5.filterMap fun w =>
    if dot3 (edgeVSub u w) (edgeVSub u w) = 16 then some (edgeVAdd u w) else none).dedup

/-- The frame through an edge sum `m`: all edge sums parallel or orthogonal to `m`. -/
def frameOf (m : Fin 3 → Zsqrt5) : List (Fin 3 → Zsqrt5) :=
  edgeSums.filter fun x => decide (dot3 x m = 0 ∨ cross3 x m = 0)

/-- One representative edge sum for each frame. These are labels only: frame `i` is
`frameOf (frameRep i)`. The Lean fact tying the numbering to `framePermList` is
`framePermM3_eq_iff_maps` below. That this numbering also agrees with the script order
is an outside comparison, not a Lean fact. -/
def frameRep : Fin 5 → (Fin 3 → Zsqrt5) :=
  ![![⟨1, 1⟩, ⟨2, 0⟩, ⟨3, 1⟩],
    ![⟨2, 0⟩, ⟨3, 1⟩, ⟨1, 1⟩],
    ![⟨-1, -1⟩, ⟨2, 0⟩, ⟨3, 1⟩],
    ![⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 2⟩],
    ![⟨-2, 0⟩, ⟨3, 1⟩, ⟨1, 1⟩]]

/-- The five frames: each is 6 vectors, closed under negation,
pairwise orthogonal or parallel: the edge sums `±m₁, ±m₂, ±m₃`. (A classical solid correspondence is not stated or proved in Lean.) -/
def frame (i : Fin 5) : List (Fin 3 → Zsqrt5) := frameOf (frameRep i)

/-! ### Geometric facts about edges and frames -/

theorem edgeSums_length : edgeSums.length = 30 := by decide +kernel

theorem edgeSums_neg_mem : ∀ x ∈ edgeSums, -x ∈ edgeSums := by decide +kernel

theorem frameRep_mem : ∀ i : Fin 5, frameRep i ∈ edgeSums := by decide +kernel

/-- Each edge sum is orthogonal to exactly four edge sums (two sign-pairs ±x). -/
theorem edgeSums_orthogonal_count :
    ∀ x ∈ edgeSums, (edgeSums.filter fun y => decide (dot3 x y = 0)).length = 4 := by
  decide +kernel

theorem frame_length : ∀ i : Fin 5, (frame i).length = 6 := by decide +kernel

/-- Within a frame, any two vectors are orthogonal or parallel. -/
theorem frame_orthogonal_or_parallel :
    ∀ i : Fin 5, ∀ x ∈ frame i, ∀ y ∈ frame i, dot3 x y = 0 ∨ cross3 x y = 0 := by
  decide +kernel

/-- Every edge sum lies in exactly one of the five frames. -/
theorem edgeSums_mem_unique_frame :
    ∀ x ∈ edgeSums, ((List.finRange 5).filter fun i => decide (x ∈ frame i)).length = 1 := by
  decide +kernel

/-- Exhaustiveness: two orthogonal edge sums always lie in a common frame, so every
pairwise orthogonal triple of edge sums lies in one of the five frames. -/
theorem orthogonal_edgeSums_same_frame :
    ∀ x ∈ edgeSums, ∀ y ∈ edgeSums, dot3 x y = 0 → ∃ i : Fin 5, x ∈ frame i ∧ y ∈ frame i := by
  decide +kernel

theorem frameRep_mem_frame : ∀ i : Fin 5, frameRep i ∈ frame i := by decide +kernel

/-- The five frames are distinct. -/
theorem frame_injective : ∀ i j : Fin 5, frame i = frame j → i = j := by decide +kernel

/-! ### The table is the frame action -/

theorem frame_mapsTo_chunk0 :
    ∀ A ∈ scaledRotationChunk0, ∀ i : Fin 5, ∀ x ∈ frame i,
      ∃ y ∈ frame (framePermM3 A i), A.mulVec x = (4 : Zsqrt5) • y := by
  decide +kernel

theorem frame_mapsOnto_chunk0 :
    ∀ A ∈ scaledRotationChunk0, ∀ i : Fin 5, ∀ y ∈ frame (framePermM3 A i),
      ∃ x ∈ frame i, A.mulVec x = (4 : Zsqrt5) • y := by
  decide +kernel

theorem frame_target_unique_chunk0 :
    ∀ A ∈ scaledRotationChunk0, ∀ i j : Fin 5,
      (∀ x ∈ frame i, ∃ y ∈ frame j, A.mulVec x = (4 : Zsqrt5) • y) →
        j = framePermM3 A i := by
  decide +kernel

theorem frame_mapsTo_chunk1 :
    ∀ A ∈ scaledRotationChunk1, ∀ i : Fin 5, ∀ x ∈ frame i,
      ∃ y ∈ frame (framePermM3 A i), A.mulVec x = (4 : Zsqrt5) • y := by
  decide +kernel

theorem frame_mapsOnto_chunk1 :
    ∀ A ∈ scaledRotationChunk1, ∀ i : Fin 5, ∀ y ∈ frame (framePermM3 A i),
      ∃ x ∈ frame i, A.mulVec x = (4 : Zsqrt5) • y := by
  decide +kernel

theorem frame_target_unique_chunk1 :
    ∀ A ∈ scaledRotationChunk1, ∀ i j : Fin 5,
      (∀ x ∈ frame i, ∃ y ∈ frame j, A.mulVec x = (4 : Zsqrt5) • y) →
        j = framePermM3 A i := by
  decide +kernel

theorem frame_mapsTo_chunk2 :
    ∀ A ∈ scaledRotationChunk2, ∀ i : Fin 5, ∀ x ∈ frame i,
      ∃ y ∈ frame (framePermM3 A i), A.mulVec x = (4 : Zsqrt5) • y := by
  decide +kernel

theorem frame_mapsOnto_chunk2 :
    ∀ A ∈ scaledRotationChunk2, ∀ i : Fin 5, ∀ y ∈ frame (framePermM3 A i),
      ∃ x ∈ frame i, A.mulVec x = (4 : Zsqrt5) • y := by
  decide +kernel

theorem frame_target_unique_chunk2 :
    ∀ A ∈ scaledRotationChunk2, ∀ i j : Fin 5,
      (∀ x ∈ frame i, ∃ y ∈ frame j, A.mulVec x = (4 : Zsqrt5) • y) →
        j = framePermM3 A i := by
  decide +kernel

theorem frame_mapsTo_chunk3 :
    ∀ A ∈ scaledRotationChunk3, ∀ i : Fin 5, ∀ x ∈ frame i,
      ∃ y ∈ frame (framePermM3 A i), A.mulVec x = (4 : Zsqrt5) • y := by
  decide +kernel

theorem frame_mapsOnto_chunk3 :
    ∀ A ∈ scaledRotationChunk3, ∀ i : Fin 5, ∀ y ∈ frame (framePermM3 A i),
      ∃ x ∈ frame i, A.mulVec x = (4 : Zsqrt5) • y := by
  decide +kernel

theorem frame_target_unique_chunk3 :
    ∀ A ∈ scaledRotationChunk3, ∀ i j : Fin 5,
      (∀ x ∈ frame i, ∃ y ∈ frame j, A.mulVec x = (4 : Zsqrt5) • y) →
        j = framePermM3 A i := by
  decide +kernel

theorem frame_mapsTo_chunk4 :
    ∀ A ∈ scaledRotationChunk4, ∀ i : Fin 5, ∀ x ∈ frame i,
      ∃ y ∈ frame (framePermM3 A i), A.mulVec x = (4 : Zsqrt5) • y := by
  decide +kernel

theorem frame_mapsOnto_chunk4 :
    ∀ A ∈ scaledRotationChunk4, ∀ i : Fin 5, ∀ y ∈ frame (framePermM3 A i),
      ∃ x ∈ frame i, A.mulVec x = (4 : Zsqrt5) • y := by
  decide +kernel

theorem frame_target_unique_chunk4 :
    ∀ A ∈ scaledRotationChunk4, ∀ i j : Fin 5,
      (∀ x ∈ frame i, ∃ y ∈ frame j, A.mulVec x = (4 : Zsqrt5) • y) →
        j = framePermM3 A i := by
  decide +kernel

theorem frame_mapsTo_chunk5 :
    ∀ A ∈ scaledRotationChunk5, ∀ i : Fin 5, ∀ x ∈ frame i,
      ∃ y ∈ frame (framePermM3 A i), A.mulVec x = (4 : Zsqrt5) • y := by
  decide +kernel

theorem frame_mapsOnto_chunk5 :
    ∀ A ∈ scaledRotationChunk5, ∀ i : Fin 5, ∀ y ∈ frame (framePermM3 A i),
      ∃ x ∈ frame i, A.mulVec x = (4 : Zsqrt5) • y := by
  decide +kernel

theorem frame_target_unique_chunk5 :
    ∀ A ∈ scaledRotationChunk5, ∀ i j : Fin 5,
      (∀ x ∈ frame i, ∃ y ∈ frame j, A.mulVec x = (4 : Zsqrt5) • y) →
        j = framePermM3 A i := by
  decide +kernel

theorem frame_mapsTo :
    ∀ A ∈ scaledRotationList, ∀ i : Fin 5, ∀ x ∈ frame i,
      ∃ y ∈ frame (framePermM3 A i), A.mulVec x = (4 : Zsqrt5) • y := by
  intro A hA
  simp only [scaledRotationList, List.mem_append] at hA
  rcases hA with ((((h | h) | h) | h) | h) | h
  exacts [frame_mapsTo_chunk0 A h, frame_mapsTo_chunk1 A h, frame_mapsTo_chunk2 A h,
    frame_mapsTo_chunk3 A h, frame_mapsTo_chunk4 A h, frame_mapsTo_chunk5 A h]

theorem frame_mapsOnto :
    ∀ A ∈ scaledRotationList, ∀ i : Fin 5, ∀ y ∈ frame (framePermM3 A i),
      ∃ x ∈ frame i, A.mulVec x = (4 : Zsqrt5) • y := by
  intro A hA
  simp only [scaledRotationList, List.mem_append] at hA
  rcases hA with ((((h | h) | h) | h) | h) | h
  exacts [frame_mapsOnto_chunk0 A h, frame_mapsOnto_chunk1 A h, frame_mapsOnto_chunk2 A h,
    frame_mapsOnto_chunk3 A h, frame_mapsOnto_chunk4 A h, frame_mapsOnto_chunk5 A h]

theorem frame_target_unique :
    ∀ A ∈ scaledRotationList, ∀ i j : Fin 5,
      (∀ x ∈ frame i, ∃ y ∈ frame j, A.mulVec x = (4 : Zsqrt5) • y) →
        j = framePermM3 A i := by
  intro A hA
  simp only [scaledRotationList, List.mem_append] at hA
  rcases hA with ((((h | h) | h) | h) | h) | h
  exacts [frame_target_unique_chunk0 A h, frame_target_unique_chunk1 A h, frame_target_unique_chunk2 A h,
    frame_target_unique_chunk3 A h, frame_target_unique_chunk4 A h, frame_target_unique_chunk5 A h]

/-- The table entry, characterised geometrically: `framePermM3 A i` is the unique frame
that `A` (divided by 4) carries frame `i` into. -/
theorem framePermM3_eq_iff_maps (A : M3) (hA : A ∈ scaledRotationList) (i j : Fin 5) :
    framePermM3 A i = j ↔ ∀ x ∈ frame i, ∃ y ∈ frame j, A.mulVec x = (4 : Zsqrt5) • y := by
  constructor
  · rintro rfl; exact frame_mapsTo A hA i
  · intro h; exact (frame_target_unique A hA i j h).symm

/-- Every frame vector is an edge sum `u + w` of two listed vertices at squared distance 16. -/
theorem frame_mem_edge :
    ∀ i : Fin 5, ∀ x ∈ frame i, ∃ u ∈ icosahedronVerticesZsqrt5, ∃ w ∈ icosahedronVerticesZsqrt5,
      dot3 (edgeVSub u w) (edgeVSub u w) = 16 ∧ x = edgeVAdd u w := by
  decide +kernel

/-! ### Transport to the imported official real group -/

/-- Real frame `i`: the halved real images of the edge sums in frame `i`. -/
noncomputable def realFrame (i : Fin 5) : Set (Fin 3 → ℝ) :=
  halveToReal '' {x | x ∈ frame i}

/-- Each real frame vector is `u + w` for official vertices `u, w` at distance `2`
(an edge of the unit-scale icosahedron), i.e. twice an edge midpoint. -/
theorem realFrame_mem_edge (i : Fin 5) :
    ∀ p ∈ realFrame i, ∃ u ∈ icosahedronVertexSet, ∃ w ∈ icosahedronVertexSet,
      (u - w) ⬝ᵥ (u - w) = 4 ∧ p = u + w := by
  rintro p ⟨x, hx, rfl⟩
  obtain ⟨u, hu, w, hw, hd, rfl⟩ := frame_mem_edge i x hx
  have hsub : halveToReal (edgeVSub u w) = halveToReal u - halveToReal w := by
    funext k; fin_cases k <;> simp [halveToReal, edgeVSub, map_sub] <;> ring
  have hadd : halveToReal (edgeVAdd u w) = halveToReal u + halveToReal w := by
    funext k; fin_cases k <;> simp [halveToReal, edgeVAdd, map_add] <;> ring
  refine ⟨halveToReal u, halveToReal_mem_icosahedronVertexSet hu,
    halveToReal w, halveToReal_mem_icosahedronVertexSet hw, ?_, hadd⟩
  rw [← hsub, dotProduct_halveToReal, hd]
  norm_num [map_ofNat]

/-- Every element `g` of the imported official `icosahedralRotationGroup` maps real frame `i`
onto real frame `σ(g) i`, where `σ = icosahedralRotationGroupMulEquivAlternatingGroup`. -/
theorem icosahedralRotationGroup_maps_realFrame (g : icosahedralRotationGroup) (i : Fin 5) :
    (fun v => ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v) ''
        realFrame i =
      realFrame (((icosahedralRotationGroupMulEquivAlternatingGroup g :
        alternatingGroup (Fin 5)) : Perm (Fin 5)) i) := by
  have hperm : ((icosahedralRotationGroupMulEquivAlternatingGroup g :
      alternatingGroup (Fin 5)) : Perm (Fin 5)) =
        framePermM3 (repM3 (scaledIcosahedralMulEquiv.symm g)) := rfl
  have hmat : ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) =
      realQuarter (repM3 (scaledIcosahedralMulEquiv.symm g)).toMatrix := by
    rw [repM3_toMatrix]
    conv_lhs => rw [← scaledIcosahedralMulEquiv.apply_symm_apply g]
    rfl
  rw [hperm, hmat]
  generalize scaledIcosahedralMulEquiv.symm g = S
  have hA := repM3_mem S
  ext p
  simp only [realFrame, Set.image_image, Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨y, hy, h⟩ := frame_mapsTo _ hA i x hx
    exact ⟨y, hy, (realQuarter_mulVec_halveToReal _ (by rw [M3.toMatrix_mulVec]; exact h)).symm⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨x, hx, h⟩ := frame_mapsOnto _ hA i y hy
    exact ⟨x, hx, realQuarter_mulVec_halveToReal _ (by rw [M3.toMatrix_mulVec]; exact h)⟩

theorem halveToReal_injective : Function.Injective halveToReal := by
  intro a b h
  funext k
  have hk := congrFun h k
  simp only [halveToReal] at hk
  exact zsqrt5ToReal_injective (by linarith)

theorem frameRep_mem_frame_eq : ∀ i j : Fin 5, frameRep i ∈ frame j → i = j := by
  decide +kernel

/-- The five real frames are distinct. -/
theorem realFrame_injective : Function.Injective realFrame := by
  intro i j h
  have hi : halveToReal (frameRep i) ∈ realFrame j := h ▸ ⟨frameRep i, frameRep_mem_frame i, rfl⟩
  obtain ⟨x, hx, hxe⟩ := hi
  have : x = frameRep i := halveToReal_injective hxe
  subst this
  exact frameRep_mem_frame_eq i j hx

#print axioms edgeSums_length
#print axioms edgeSums_orthogonal_count
#print axioms frame_length
#print axioms frame_orthogonal_or_parallel
#print axioms edgeSums_mem_unique_frame
#print axioms orthogonal_edgeSums_same_frame
#print axioms frame_mem_edge
#print axioms frame_mapsTo
#print axioms frame_mapsOnto
#print axioms frame_target_unique
#print axioms frame_injective
#print axioms framePermM3_eq_iff_maps
#print axioms realFrame_mem_edge
#print axioms icosahedralRotationGroup_maps_realFrame
#print axioms realFrame_injective
