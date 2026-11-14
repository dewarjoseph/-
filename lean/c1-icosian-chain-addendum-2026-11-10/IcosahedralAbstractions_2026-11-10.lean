/-
Scratch file, dated 2026-11-10. Not a Lake target. Not peer reviewed.

C1 abstractions. Statement text was frozen before proving.

Imports `IcosahedralCubeCompletion_2026-11-10` (src 8d46d6cb…) unchanged. No existing file is
edited and no text is copied.

Part A (generic, no icosahedral data): orthogonal matrices preserve dot products and squared
distances; an orthogonal `A` with `A '' S = S` maps the pair-sum set `pairSums d S` and the
triple-sum set `tripleSums d S` onto themselves; an injective self-map of a finite set that
maps it into itself maps it onto itself; for a ring hom `f : R →+* ℝ`, dot products, `mulVec`,
and scaled-orthogonality `Mᵀ M = c • 1` commute with `f`, and if `f` is injective then vector
equality, dot-product equations and `ncard` of the image of a duplicate-free list transfer;
transitivity from one base point for any group hom `G →* Function.End X`; and a counting
lemma turning `Nat.card {g // P (e g)}` into the length of a filtered list when `e` is a
bijection onto a duplicate-free list.

Part B (official group, official sets): the official group maps `officialEdgeVectors` and
`officialFaceSums` onto themselves (via Part A, since these are `pairSums 4` and `tripleSums 4`
of the official vertex set); it acts transitively on the official vertex set (stabilizer
order 5), on `officialEdgeVectors` (stabilizer order 2), on `officialFaceSums` (stabilizer
order 3), on the five `officialCube k` (stabilizer order 12) and on the five `officialFrame k`
(stabilizer order 12); the elements fixing a sign-pair `{p, -p}` (`g p = p ∨ g p = -p`) of
an official edge vector number 4; every conjugacy class has 1, 12, 15 or 20 elements, and the
numbers of group elements whose class has 1, 12, 15, 20 elements are 1, 24, 15, 20.
Counts are `decide +kernel` checks in the ℤ[√5] model (`scaledRotationList`) or on the table
`framePermList` (via σ), transferred by the bijections `toM3` and `toPerm`.

Not proved here: any isomorphism of a stabilizer with A4; `Nat.card (ConjClasses _)`; anything
about subspaces spanned by `p`; anything about 2I, SU(2) or other projects.
-/

import «IcosahedralCubeCompletion_2026-11-10»
open Equiv Matrix

/-! ## Part A: generic lemmas (no icosahedral data) -/

theorem orthogonal_dotProduct {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A ∈ Matrix.orthogonalGroup n ℝ) (v w : n → ℝ) :
    (A *ᵥ v) ⬝ᵥ (A *ᵥ w) = v ⬝ᵥ w := by
  have h : Aᵀ * A = 1 := (Matrix.mem_orthogonalGroup_iff' n ℝ).mp hA
  rw [dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, h, one_mulVec]

theorem orthogonal_sqDist {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A ∈ Matrix.orthogonalGroup n ℝ) (u w : n → ℝ) :
    (A *ᵥ u - A *ᵥ w) ⬝ᵥ (A *ᵥ u - A *ᵥ w) = (u - w) ⬝ᵥ (u - w) := by
  rw [← mulVec_sub, orthogonal_dotProduct hA]

def pairSums {n : Type*} [Fintype n] (d : ℝ) (S : Set (n → ℝ)) : Set (n → ℝ) :=
  {p | ∃ u ∈ S, ∃ w ∈ S, (u - w) ⬝ᵥ (u - w) = d ∧ p = u + w}

def tripleSums {n : Type*} [Fintype n] (d : ℝ) (S : Set (n → ℝ)) : Set (n → ℝ) :=
  {p | ∃ u ∈ S, ∃ v ∈ S, ∃ w ∈ S, (u - v) ⬝ᵥ (u - v) = d ∧ (v - w) ⬝ᵥ (v - w) = d ∧
    (u - w) ⬝ᵥ (u - w) = d ∧ p = u + v + w}

theorem orthogonal_image_pairSums {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A ∈ Matrix.orthogonalGroup n ℝ) {S : Set (n → ℝ)} (hS : (A *ᵥ ·) '' S = S) (d : ℝ) :
    (A *ᵥ ·) '' pairSums d S = pairSums d S := by
  have hmem : ∀ u ∈ S, A *ᵥ u ∈ S := fun u hu => by rw [← hS]; exact ⟨u, hu, rfl⟩
  ext p
  constructor
  · rintro ⟨q, ⟨u, hu, w, hw, hd, rfl⟩, rfl⟩
    refine ⟨A *ᵥ u, hmem u hu, A *ᵥ w, hmem w hw, ?_, mulVec_add A u w⟩
    rw [orthogonal_sqDist hA, hd]
  · rintro ⟨u, hu, w, hw, hd, rfl⟩
    rw [← hS] at hu hw
    obtain ⟨u', hu', rfl⟩ := hu
    obtain ⟨w', hw', rfl⟩ := hw
    refine ⟨u' + w', ⟨u', hu', w', hw', ?_, rfl⟩, mulVec_add A u' w'⟩
    rwa [orthogonal_sqDist hA] at hd

theorem orthogonal_image_tripleSums {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A ∈ Matrix.orthogonalGroup n ℝ) {S : Set (n → ℝ)} (hS : (A *ᵥ ·) '' S = S) (d : ℝ) :
    (A *ᵥ ·) '' tripleSums d S = tripleSums d S := by
  have hmem : ∀ u ∈ S, A *ᵥ u ∈ S := fun u hu => by rw [← hS]; exact ⟨u, hu, rfl⟩
  ext p
  constructor
  · rintro ⟨q, ⟨u, hu, v, hv, w, hw, h1, h2, h3, rfl⟩, rfl⟩
    refine ⟨A *ᵥ u, hmem u hu, A *ᵥ v, hmem v hv, A *ᵥ w, hmem w hw, ?_, ?_, ?_, ?_⟩
    · rw [orthogonal_sqDist hA, h1]
    · rw [orthogonal_sqDist hA, h2]
    · rw [orthogonal_sqDist hA, h3]
    · show A *ᵥ (u + v + w) = _
      rw [mulVec_add, mulVec_add]
  · rintro ⟨u, hu, v, hv, w, hw, h1, h2, h3, rfl⟩
    rw [← hS] at hu hv hw
    obtain ⟨u', hu', rfl⟩ := hu
    obtain ⟨v', hv', rfl⟩ := hv
    obtain ⟨w', hw', rfl⟩ := hw
    rw [orthogonal_sqDist hA] at h1 h2 h3
    exact ⟨u' + v' + w', ⟨u', hu', v', hv', w', hw', h1, h2, h3, rfl⟩, by
      show A *ᵥ (u' + v' + w') = _
      rw [mulVec_add, mulVec_add]⟩

theorem image_eq_of_mapsTo_of_injective {α : Type*} {S : Set α} (hS : S.Finite) {f : α → α}
    (hf : Function.Injective f) (h : Set.MapsTo f S S) : f '' S = S :=
  ((Set.Finite.injOn_iff_bijOn_of_mapsTo hS h).mp hf.injOn).image_eq

theorem transfer_dotProduct {n R : Type*} [Fintype n] [CommRing R] (f : R →+* ℝ) (a b : n → R) :
    (fun i => f (a i)) ⬝ᵥ (fun i => f (b i)) = f (a ⬝ᵥ b) := by
  simp [dotProduct, map_sum, map_mul]

theorem transfer_mulVec {n R : Type*} [Fintype n] [CommRing R] (f : R →+* ℝ) (M : Matrix n n R)
    (v : n → R) : M.map f *ᵥ (fun i => f (v i)) = fun i => f ((M *ᵥ v) i) := by
  funext i
  simp [mulVec, dotProduct, map_sum, map_mul]

theorem transfer_vec_injective {n R : Type*} [CommRing R] {f : R →+* ℝ}
    (hf : Function.Injective f) : Function.Injective (fun (x : n → R) (i : n) => f (x i)) :=
  fun _ _ h => funext fun i => hf (congrFun h i)

theorem transfer_dotProduct_eq_iff {n R : Type*} [Fintype n] [CommRing R] {f : R →+* ℝ}
    (hf : Function.Injective f) (a b : n → R) (c : R) :
    (fun i => f (a i)) ⬝ᵥ (fun i => f (b i)) = f c ↔ a ⬝ᵥ b = c := by
  rw [transfer_dotProduct]
  exact hf.eq_iff

theorem transfer_ncard_list {n R : Type*} [CommRing R] {f : R →+* ℝ}
    (hf : Function.Injective f) {L : List (n → R)} (hL : L.Nodup) :
    ((fun (x : n → R) (i : n) => f (x i)) '' {x | x ∈ L}).ncard = L.length := by
  classical
  rw [Set.ncard_image_of_injective _ (transfer_vec_injective hf)]
  have h : {x | x ∈ L} = ((L.toFinset : Finset (n → R)) : Set (n → R)) := by ext; simp
  rw [h, Set.ncard_coe_finset, List.toFinset_card_of_nodup hL]

theorem transfer_scaledOrthogonal {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    (f : R →+* ℝ) (M : Matrix n n R) (c : R) (h : Mᵀ * M = c • (1 : Matrix n n R)) :
    (M.map f)ᵀ * M.map f = f c • (1 : Matrix n n ℝ) := by
  rw [← Matrix.transpose_map, ← Matrix.map_mul, h]
  ext i j
  by_cases hij : i = j <;> simp [hij]

theorem transitive_of_base {G X : Type*} [Group G] (ρ : G →* Function.End X) (S : Set X) (b : X)
    (h : ∀ y ∈ S, ∃ g : G, ρ g b = y) : ∀ x ∈ S, ∀ y ∈ S, ∃ g : G, ρ g x = y := by
  intro x hx y hy
  obtain ⟨g, rfl⟩ := h x hx
  obtain ⟨k, rfl⟩ := h y hy
  refine ⟨k * g⁻¹, ?_⟩
  have h1 : (ρ g⁻¹ * ρ g) b = b := by rw [← map_mul, inv_mul_cancel, map_one]; rfl
  rw [map_mul]
  change ρ k ((ρ g⁻¹ * ρ g) b) = ρ k b
  rw [h1]

theorem natCard_filter_of_bijOn_list {G α : Type*} [DecidableEq α] (e : G → α) (L : List α)
    (hL : L.Nodup) (hmem : ∀ g, e g ∈ L) (hinj : Function.Injective e)
    (hsurj : ∀ a ∈ L, ∃ g, e g = a) (P : α → Prop) [DecidablePred P] :
    Nat.card {g : G // P (e g)} = (L.filter (fun a => decide (P a))).length := by
  let φ : {g : G // P (e g)} → {a // a ∈ L.filter (fun a => decide (P a))} :=
    fun g => ⟨e g.1, List.mem_filter.mpr ⟨hmem g.1, decide_eq_true g.2⟩⟩
  have hφ : Function.Bijective φ := by
    constructor
    · intro x y hxy
      exact Subtype.ext (hinj (congrArg Subtype.val hxy))
    · rintro ⟨a, ha⟩
      obtain ⟨haL, hPa⟩ := List.mem_filter.mp ha
      obtain ⟨g, rfl⟩ := hsurj a haL
      exact ⟨⟨g, of_decide_eq_true hPa⟩, rfl⟩
  rw [Nat.card_eq_of_bijective φ hφ, natCard_mem_list _ (hL.filter _)]

/-! ## Part B: icosahedral applications -/

theorem zsqrt5ToReal_vec_injective :
    Function.Injective (fun (x : Fin 3 → Zsqrt5) (i : Fin 3) => zsqrt5ToReal (x i)) :=
  transfer_vec_injective zsqrt5ToReal_injective

noncomputable def icoAct : icosahedralRotationGroup →* Function.End (Fin 3 → ℝ) where
  toFun g := fun v => ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v
  map_one' := funext fun v => one_mulVec v
  map_mul' := fun g h => funext fun v => coe_mul_mulVec g h v

theorem officialEdgeVectors_eq_pairSums : officialEdgeVectors = pairSums 4 icosahedronVertexSet :=
  rfl

theorem officialFaceSums_eq_tripleSums : officialFaceSums = tripleSums 4 icosahedronVertexSet :=
  rfl

theorem icosahedralRotationGroup_mem_orthogonalGroup (g : icosahedralRotationGroup) :
    ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) ∈
      Matrix.orthogonalGroup (Fin 3) ℝ :=
  (Matrix.mem_specialOrthogonalGroup_iff.mp (g : specialOrthogonalGroup (Fin 3) ℝ).2).1

theorem icosahedralRotationGroup_image_vertexSet (g : icosahedralRotationGroup) :
    (fun v => ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v) ''
      icosahedronVertexSet = icosahedronVertexSet :=
  (mem_icosahedralRotationGroup_iff _).mp g.2

theorem icosahedralRotationGroup_image_officialEdgeVectors (g : icosahedralRotationGroup) :
    (fun v => ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v) ''
      officialEdgeVectors = officialEdgeVectors := by
  rw [officialEdgeVectors_eq_pairSums]
  exact orthogonal_image_pairSums (icosahedralRotationGroup_mem_orthogonalGroup g)
    (icosahedralRotationGroup_image_vertexSet g) 4

theorem icosahedralRotationGroup_image_officialFaceSums (g : icosahedralRotationGroup) :
    (fun v => ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v) ''
      officialFaceSums = officialFaceSums := by
  rw [officialFaceSums_eq_tripleSums]
  exact orthogonal_image_tripleSums (icosahedralRotationGroup_mem_orthogonalGroup g)
    (icosahedralRotationGroup_image_vertexSet g) 4

/-! ### Bijection of the official group with the 60 listed `M3` -/

noncomputable def toM3 (g : icosahedralRotationGroup) : M3 :=
  repM3 (scaledIcosahedralMulEquiv.symm g)

theorem toM3_mem (g : icosahedralRotationGroup) : toM3 g ∈ scaledRotationList := repM3_mem _

theorem toM3_injective : Function.Injective toM3 := by
  intro g h hgh
  have hS : scaledIcosahedralMulEquiv.symm g = scaledIcosahedralMulEquiv.symm h := by
    apply Subtype.ext
    rw [← repM3_toMatrix, ← repM3_toMatrix]
    exact congrArg M3.toMatrix hgh
  exact scaledIcosahedralMulEquiv.symm.injective hS

theorem toM3_surj : ∀ A ∈ scaledRotationList, ∃ g, toM3 g = A := by
  intro A hA
  let S : scaledIcosahedralRotations :=
    ⟨A.toMatrix, mem_scaledIcosahedralRotations.mpr ⟨A, hA, rfl⟩⟩
  refine ⟨scaledIcosahedralMulEquiv S, ?_⟩
  apply M3.toMatrix_injective
  rw [toM3, MulEquiv.symm_apply_apply, repM3_toMatrix]

theorem mulVec_halveToReal_iff (g : icosahedralRotationGroup) (x y : Fin 3 → Zsqrt5) :
    ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ halveToReal x =
        halveToReal y ↔ (toM3 g).mulVec x = (4 : Zsqrt5) • y := by
  rw [coe_eq_realQuarter_repM3, realQuarter_mulVec_halveToReal_iff, M3.toMatrix_mulVec]; rfl

theorem transitive_of_scaledBase {S : Set (Fin 3 → ℝ)} {LZ : List (Fin 3 → Zsqrt5)}
    (hS : S = halveToReal '' {x | x ∈ LZ}) (b : Fin 3 → Zsqrt5)
    (h : ∀ y ∈ LZ, ∃ A ∈ scaledRotationList, A.mulVec b = (4 : Zsqrt5) • y) :
    ∀ p ∈ S, ∀ q ∈ S, ∃ g : icosahedralRotationGroup,
      ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ p = q := by
  refine transitive_of_base icoAct S (halveToReal b) ?_
  intro q hq
  rw [hS] at hq
  obtain ⟨y, hy, rfl⟩ := hq
  obtain ⟨A, hA, hAb⟩ := h y hy
  obtain ⟨g, rfl⟩ := toM3_surj A hA
  exact ⟨g, (mulVec_halveToReal_iff g b y).mpr hAb⟩

theorem stabilizer_card_of_scaled {S : Set (Fin 3 → ℝ)} {LZ : List (Fin 3 → Zsqrt5)}
    (hS : S = halveToReal '' {x | x ∈ LZ}) (n : ℕ)
    (h : ∀ x ∈ LZ, (scaledRotationList.filter
      (fun A => decide (A.mulVec x = (4 : Zsqrt5) • x))).length = n) :
    ∀ p ∈ S, Nat.card {g : icosahedralRotationGroup //
      ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ p = p} = n := by
  intro p hp
  rw [hS] at hp
  obtain ⟨x, hx, rfl⟩ := hp
  simp only [mulVec_halveToReal_iff]
  rw [natCard_filter_of_bijOn_list toM3 _ scaledRotationList_nodup toM3_mem toM3_injective
    toM3_surj (fun A => A.mulVec x = (4 : Zsqrt5) • x)]
  exact h x hx

/-! ### Finite checks in the ℤ[√5] model -/

theorem scaled_vertex_reach : ∀ y ∈ icosahedronVerticesZsqrt5,
    ∃ A ∈ scaledRotationList, A.mulVec vtxA = (4 : Zsqrt5) • y := by decide +kernel

theorem scaled_vertex_stab : ∀ x ∈ icosahedronVerticesZsqrt5, (scaledRotationList.filter
    (fun A => decide (A.mulVec x = (4 : Zsqrt5) • x))).length = 5 := by decide +kernel


theorem scaled_edge_reach : ∀ y ∈ edgeSums,
    ∃ A ∈ scaledRotationList, A.mulVec (frameRep 0) = (4 : Zsqrt5) • y := by decide +kernel

theorem scaled_edge_stab : ∀ x ∈ edgeSums, (scaledRotationList.filter
    (fun A => decide (A.mulVec x = (4 : Zsqrt5) • x))).length = 2 := by decide +kernel

theorem scaled_edgePair_stab : ∀ x ∈ edgeSums, (scaledRotationList.filter
    (fun A => decide (A.mulVec x = (4 : Zsqrt5) • x ∨ A.mulVec x = (4 : Zsqrt5) • -x))).length = 4 := by
  decide +kernel

theorem scaled_face_reach : ∀ y ∈ faceSums,
    ∃ A ∈ scaledRotationList, A.mulVec (faceSums.headD 0) = (4 : Zsqrt5) • y := by decide +kernel

theorem scaled_face_stab : ∀ x ∈ faceSums, (scaledRotationList.filter
    (fun A => decide (A.mulVec x = (4 : Zsqrt5) • x))).length = 3 := by decide +kernel

/-! ### Vertices, edge vectors, edge pairs `{p, -p}`, face sums -/

theorem vertex_transitive : ∀ u ∈ icosahedronVertexSet, ∀ w ∈ icosahedronVertexSet,
    ∃ g : icosahedralRotationGroup,
      ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ u = w :=
  transitive_of_scaledBase halveToReal_image_icosahedronVerticesZsqrt5.symm vtxA scaled_vertex_reach

theorem vertex_stabilizer_card : ∀ u ∈ icosahedronVertexSet,
    Nat.card {g : icosahedralRotationGroup //
      ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ u = u} = 5 :=
  stabilizer_card_of_scaled halveToReal_image_icosahedronVerticesZsqrt5.symm 5 scaled_vertex_stab

theorem edgeVector_transitive : ∀ p ∈ officialEdgeVectors, ∀ q ∈ officialEdgeVectors,
    ∃ g : icosahedralRotationGroup,
      ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ p = q :=
  transitive_of_scaledBase officialEdgeVectors_eq_image (frameRep 0) scaled_edge_reach

theorem edgeVector_stabilizer_card : ∀ p ∈ officialEdgeVectors,
    Nat.card {g : icosahedralRotationGroup //
      ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ p = p} = 2 :=
  stabilizer_card_of_scaled officialEdgeVectors_eq_image 2 scaled_edge_stab

theorem edgePair_stabilizer_card : ∀ p ∈ officialEdgeVectors,
    Nat.card {g : icosahedralRotationGroup //
      ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ p = p ∨
      ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ p = -p} = 4 := by
  intro p hp
  rw [officialEdgeVectors_eq_image] at hp
  obtain ⟨x, hx, rfl⟩ := hp
  simp only [← halveToReal_neg, mulVec_halveToReal_iff]
  rw [natCard_filter_of_bijOn_list toM3 _ scaledRotationList_nodup toM3_mem toM3_injective
    toM3_surj (fun A => A.mulVec x = (4 : Zsqrt5) • x ∨ A.mulVec x = (4 : Zsqrt5) • -x)]
  exact scaled_edgePair_stab x hx

theorem faceSum_transitive : ∀ p ∈ officialFaceSums, ∀ q ∈ officialFaceSums,
    ∃ g : icosahedralRotationGroup,
      ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ p = q :=
  transitive_of_scaledBase officialFaceSums_eq_image (faceSums.headD 0) scaled_face_reach

theorem faceSum_stabilizer_card : ∀ p ∈ officialFaceSums,
    Nat.card {g : icosahedralRotationGroup //
      ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ p = p} = 3 :=
  stabilizer_card_of_scaled officialFaceSums_eq_image 3 scaled_face_stab

/-! ### The table `framePermList` and σ -/

noncomputable def toPerm (g : icosahedralRotationGroup) : Perm (Fin 5) :=
  ((icosahedralRotationGroupMulEquivAlternatingGroup g : alternatingGroup (Fin 5)) : Perm (Fin 5))

theorem toPerm_eq (g : icosahedralRotationGroup) : toPerm g = framePermM3 (toM3 g) := rfl

theorem framePermM3_mem_table : ∀ A ∈ scaledRotationList, framePermM3 A ∈ framePermList := by
  decide +kernel

theorem framePermList_sign : ∀ q ∈ framePermList, Perm.sign q = 1 := by decide +kernel

theorem framePermList_nodup : framePermList.Nodup := by decide +kernel

theorem toPerm_mem (g : icosahedralRotationGroup) : toPerm g ∈ framePermList := by
  rw [toPerm_eq]; exact framePermM3_mem_table _ (toM3_mem g)

theorem toPerm_injective : Function.Injective toPerm := fun _ _ hgh =>
  icosahedralRotationGroupMulEquivAlternatingGroup.injective (Subtype.ext hgh)

theorem toPerm_surj : ∀ q ∈ framePermList, ∃ g, toPerm g = q := by
  intro q hq
  refine ⟨icosahedralRotationGroupMulEquivAlternatingGroup.symm
    ⟨q, Equiv.Perm.mem_alternatingGroup.mpr (framePermList_sign q hq)⟩, ?_⟩
  rw [toPerm, MulEquiv.apply_symm_apply]

theorem toPerm_mul (g h : icosahedralRotationGroup) : toPerm (g * h) = toPerm g * toPerm h := by
  rw [toPerm, toPerm, toPerm, map_mul]; rfl

theorem table_reach : ∀ j k : Fin 5, ∃ q ∈ framePermList, q k = j := by decide +kernel

theorem table_stab : ∀ k : Fin 5, (framePermList.filter (fun q => decide (q k = k))).length = 12 := by
  decide +kernel

theorem officialCube_image_eq_iff (g : icosahedralRotationGroup) (j k : Fin 5) :
    (fun v => ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v) ''
      officialCube k = officialCube j ↔ toPerm g k = j := by
  rw [officialCube_image]; exact officialCube_injective.eq_iff

theorem officialFrame_image_eq_iff (g : icosahedralRotationGroup) (j k : Fin 5) :
    (fun v => ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v) ''
      officialFrame k = officialFrame j ↔ toPerm g k = j := by
  rw [icosahedralRotationGroup_maps_officialFrame]; exact officialFrame_injective.eq_iff

theorem officialCube_transitive : ∀ j k : Fin 5, ∃ g : icosahedralRotationGroup,
    (fun v => ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v) ''
      officialCube k = officialCube j := by
  intro j k
  obtain ⟨q, hq, hqk⟩ := table_reach j k
  obtain ⟨g, rfl⟩ := toPerm_surj q hq
  exact ⟨g, (officialCube_image_eq_iff g j k).mpr hqk⟩

theorem officialCube_stabilizer_card : ∀ k : Fin 5,
    Nat.card {g : icosahedralRotationGroup //
      (fun v => ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v) ''
        officialCube k = officialCube k} = 12 := by
  intro k
  simp only [officialCube_image_eq_iff]
  rw [natCard_filter_of_bijOn_list toPerm _ framePermList_nodup toPerm_mem toPerm_injective
    toPerm_surj (fun q => q k = k)]
  exact table_stab k

theorem officialFrame_transitive : ∀ j k : Fin 5, ∃ g : icosahedralRotationGroup,
    (fun v => ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v) ''
      officialFrame k = officialFrame j := by
  intro j k
  obtain ⟨q, hq, hqk⟩ := table_reach j k
  obtain ⟨g, rfl⟩ := toPerm_surj q hq
  exact ⟨g, (officialFrame_image_eq_iff g j k).mpr hqk⟩

theorem officialFrame_stabilizer_card : ∀ k : Fin 5,
    Nat.card {g : icosahedralRotationGroup //
      (fun v => ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v) ''
        officialFrame k = officialFrame k} = 12 := by
  intro k
  simp only [officialFrame_image_eq_iff]
  rw [natCard_filter_of_bijOn_list toPerm _ framePermList_nodup toPerm_mem toPerm_injective
    toPerm_surj (fun q => q k = k)]
  exact table_stab k

/-! ### Conjugacy class sizes -/

def conjB (p r : Perm (Fin 5)) : Bool :=
  framePermList.any fun q => (List.finRange 5).all fun i => q (p i) == r (q i)

def classSize (p : Perm (Fin 5)) : ℕ :=
  (framePermList.filter (fun r => decide (conjB p r = true))).length

theorem conjB_iff (p r : Perm (Fin 5)) :
    conjB p r = true ↔ ∃ q ∈ framePermList, q * p = r * q := by
  simp only [conjB, List.any_eq_true, List.all_eq_true, List.mem_finRange, true_implies,
    beq_iff_eq, Equiv.ext_iff, Perm.mul_apply]

theorem isConj_iff_conjB (g h : icosahedralRotationGroup) :
    IsConj g h ↔ conjB (toPerm g) (toPerm h) = true := by
  rw [isConj_iff, conjB_iff]
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨toPerm c, toPerm_mem c, ?_⟩
    rw [← toPerm_mul, ← toPerm_mul, inv_mul_cancel_right]
  · rintro ⟨q, hq, hqe⟩
    obtain ⟨c, rfl⟩ := toPerm_surj q hq
    refine ⟨c, toPerm_injective ?_⟩
    rw [← toPerm_mul, ← toPerm_mul] at hqe
    rw [toPerm_injective hqe, mul_inv_cancel_right]

theorem natCard_conj (g : icosahedralRotationGroup) :
    Nat.card {h : icosahedralRotationGroup // IsConj g h} = classSize (toPerm g) := by
  simp only [isConj_iff_conjB]
  rw [natCard_filter_of_bijOn_list toPerm _ framePermList_nodup toPerm_mem toPerm_injective
    toPerm_surj (fun r => conjB (toPerm g) r = true)]
  rfl

def classSizeTable : List ℕ :=
  [1, 15, 15, 15, 20, 15, 20, 20, 15, 20, 15, 15, 12, 15, 12, 12, 15, 12, 15, 15, 12, 15, 12, 12,
    15, 12, 15, 20, 20, 20, 20, 20, 20, 20, 20, 12, 20, 12, 20, 20, 12, 20, 12, 20, 12, 20, 12, 12,
    20, 12, 20, 12, 12, 12, 12, 12, 12, 12, 12, 15]

theorem classSize_table : framePermList.map classSize = classSizeTable := by decide +kernel

theorem length_filter_eq_count_map {α : Type*} (L : List α) (f : α → ℕ) (n : ℕ) :
    (L.filter (fun a => decide (f a = n))).length = (L.map f).count n := by
  rw [List.count, List.countP_map, List.countP_eq_length_filter]
  congr 1

theorem conjClass_card_cases (g : icosahedralRotationGroup) :
    Nat.card {h : icosahedralRotationGroup // IsConj g h} = 1 ∨
    Nat.card {h : icosahedralRotationGroup // IsConj g h} = 12 ∨
    Nat.card {h : icosahedralRotationGroup // IsConj g h} = 15 ∨
    Nat.card {h : icosahedralRotationGroup // IsConj g h} = 20 := by
  have hm : classSize (toPerm g) ∈ classSizeTable := by
    rw [← classSize_table]; exact List.mem_map_of_mem (toPerm_mem g)
  have key : ∀ n ∈ classSizeTable, n = 1 ∨ n = 12 ∨ n = 15 ∨ n = 20 := by decide
  rw [natCard_conj]
  exact key _ hm

theorem natCard_classSize_eq (n : ℕ) :
    Nat.card {g : icosahedralRotationGroup //
      Nat.card {h : icosahedralRotationGroup // IsConj g h} = n} = classSizeTable.count n := by
  simp only [natCard_conj]
  rw [natCard_filter_of_bijOn_list toPerm _ framePermList_nodup toPerm_mem toPerm_injective
    toPerm_surj (fun q => classSize q = n), length_filter_eq_count_map, classSize_table]

theorem conjClass_card_counts :
    Nat.card {g : icosahedralRotationGroup //
      Nat.card {h : icosahedralRotationGroup // IsConj g h} = 1} = 1 ∧
    Nat.card {g : icosahedralRotationGroup //
      Nat.card {h : icosahedralRotationGroup // IsConj g h} = 12} = 24 ∧
    Nat.card {g : icosahedralRotationGroup //
      Nat.card {h : icosahedralRotationGroup // IsConj g h} = 15} = 15 ∧
    Nat.card {g : icosahedralRotationGroup //
      Nat.card {h : icosahedralRotationGroup // IsConj g h} = 20} = 20 := by
  simp only [natCard_classSize_eq]
  decide

#print axioms orthogonal_dotProduct
#print axioms orthogonal_sqDist
#print axioms orthogonal_image_pairSums
#print axioms orthogonal_image_tripleSums
#print axioms image_eq_of_mapsTo_of_injective
#print axioms transfer_dotProduct
#print axioms transfer_mulVec
#print axioms transfer_vec_injective
#print axioms transfer_dotProduct_eq_iff
#print axioms transfer_ncard_list
#print axioms transfer_scaledOrthogonal
#print axioms transitive_of_base
#print axioms natCard_filter_of_bijOn_list
#print axioms zsqrt5ToReal_vec_injective
#print axioms icoAct
#print axioms officialEdgeVectors_eq_pairSums
#print axioms officialFaceSums_eq_tripleSums
#print axioms icosahedralRotationGroup_image_officialEdgeVectors
#print axioms icosahedralRotationGroup_image_officialFaceSums
#print axioms vertex_transitive
#print axioms vertex_stabilizer_card
#print axioms edgeVector_transitive
#print axioms edgeVector_stabilizer_card
#print axioms edgePair_stabilizer_card
#print axioms faceSum_transitive
#print axioms faceSum_stabilizer_card
#print axioms officialCube_transitive
#print axioms officialCube_stabilizer_card
#print axioms officialFrame_transitive
#print axioms officialFrame_stabilizer_card
#print axioms conjClass_card_cases
#print axioms conjClass_card_counts
#print axioms classSize_table
