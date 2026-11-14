/-
Scratch file, dated 2026-11-10. Not a Lake target. Not peer reviewed.

Completion statements T1–T3 for the eight-point sets `officialCube k`.

Imports `IcosahedralCubesInvolutions_v2_2026-11-10` (src 340f8204…) unchanged. No text is
copied and no existing file is edited.

* T1 `officialCube_isCube`: for each `k`, `officialCube k` has 8 points and equals
  `{c + (s₁ • e₁ + s₂ • e₂ + s₃ • e₃) / 2 | sᵢ = ±1}` with `c = 0`, for pairwise orthogonal
  `e₁ e₂ e₃` with `eᵢ ⬝ᵥ eᵢ = (3 + √5)²`, each a real multiple (by `φ`) of a vector of
  `officialFrame k`. Proved in the ℤ[√5] model by `decide +kernel` (explicit vectors
  `cubeEdgeVecs`, `cubeFrameVecs`) and transferred by `halveToReal` and `officialCube_eq_image`.
* T2 `officialCube_image`: every `g` in the official group maps `officialCube k` onto
  `officialCube (σ g k)`, `σ = icosahedralRotationGroupMulEquivAlternatingGroup` (unchanged).
  Proved over ℝ: `g` permutes the official vertex set and preserves `⬝ᵥ`, so it preserves the
  official face sums; `icosahedralRotationGroup_maps_officialFrame` moves the frames.
* T3 `officialCubeHom_spec`: the map `officialCubeHom`, defined from the action on the sets
  `officialCube k` only (`officialCubeIndex`), is an injective group homomorphism into
  `Perm (Fin 5)` with range `alternatingGroup (Fin 5)`, equal to σ for every `g`.

Not proved here: anything about edges, faces or the graph of these sets beyond T1; that they
lie on any solid; anything about sign-pairs {p, −p} as subspaces.
-/

import «IcosahedralCubesInvolutions_v2_2026-11-10»
open Equiv Matrix

def cubeEdgeVecs : Fin 5 → Fin 3 → (Fin 3 → Zsqrt5) :=
  ![![![⟨3, 1⟩, ⟨1, 1⟩, ⟨4, 2⟩], ![⟨1, 1⟩, ⟨4, 2⟩, ⟨-3, -1⟩], ![⟨4, 2⟩, ⟨-3, -1⟩, ⟨-1, -1⟩]],
    ![![⟨1, 1⟩, ⟨4, 2⟩, ⟨3, 1⟩], ![⟨3, 1⟩, ⟨1, 1⟩, ⟨-4, -2⟩], ![⟨4, 2⟩, ⟨-3, -1⟩, ⟨1, 1⟩]],
    ![![⟨-3, -1⟩, ⟨1, 1⟩, ⟨4, 2⟩], ![⟨-1, -1⟩, ⟨4, 2⟩, ⟨-3, -1⟩], ![⟨4, 2⟩, ⟨3, 1⟩, ⟨1, 1⟩]],
    ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨6, 2⟩], ![⟨6, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨6, 2⟩, ⟨0, 0⟩]],
    ![![⟨-1, -1⟩, ⟨4, 2⟩, ⟨3, 1⟩], ![⟨-3, -1⟩, ⟨1, 1⟩, ⟨-4, -2⟩], ![⟨4, 2⟩, ⟨3, 1⟩, ⟨-1, -1⟩]]]

def cubeFrameVecs : Fin 5 → Fin 3 → (Fin 3 → Zsqrt5) :=
  ![![![⟨1, 1⟩, ⟨2, 0⟩, ⟨3, 1⟩], ![⟨2, 0⟩, ⟨3, 1⟩, ⟨-1, -1⟩], ![⟨3, 1⟩, ⟨-1, -1⟩, ⟨-2, 0⟩]],
    ![![⟨2, 0⟩, ⟨3, 1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨2, 0⟩, ⟨-3, -1⟩], ![⟨3, 1⟩, ⟨-1, -1⟩, ⟨2, 0⟩]],
    ![![⟨-1, -1⟩, ⟨2, 0⟩, ⟨3, 1⟩], ![⟨-2, 0⟩, ⟨3, 1⟩, ⟨-1, -1⟩], ![⟨3, 1⟩, ⟨1, 1⟩, ⟨2, 0⟩]],
    ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 2⟩], ![⟨2, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨2, 2⟩, ⟨0, 0⟩]],
    ![![⟨-2, 0⟩, ⟨3, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨2, 0⟩, ⟨-3, -1⟩], ![⟨3, 1⟩, ⟨1, 1⟩, ⟨-2, 0⟩]]]

def signZ (b : Bool) : Zsqrt5 := if b then 1 else -1

def cubeCombo (k : Fin 5) (b₁ b₂ b₃ : Bool) : Fin 3 → Zsqrt5 :=
  signZ b₁ • cubeEdgeVecs k 0 + signZ b₂ • cubeEdgeVecs k 1 + signZ b₃ • cubeEdgeVecs k 2

theorem cubeEdgeVecs_orth : ∀ k : Fin 5, dot3 (cubeEdgeVecs k 0) (cubeEdgeVecs k 1) = 0 ∧
    dot3 (cubeEdgeVecs k 0) (cubeEdgeVecs k 2) = 0 ∧ dot3 (cubeEdgeVecs k 1) (cubeEdgeVecs k 2) = 0 := by
  decide +kernel

theorem cubeEdgeVecs_sq : ∀ k : Fin 5, ∀ j : Fin 3,
    dot3 (cubeEdgeVecs k j) (cubeEdgeVecs k j) = cubeEdgeSq := by
  decide +kernel

theorem cubeFrameVecs_mem : ∀ k : Fin 5, ∀ j : Fin 3, cubeFrameVecs k j ∈ frame k := by
  decide +kernel

theorem cubeEdgeVecs_parallel : ∀ k : Fin 5, ∀ j : Fin 3,
    (2 : Zsqrt5) • cubeEdgeVecs k j = (⟨1, 1⟩ : Zsqrt5) • cubeFrameVecs k j := by
  decide +kernel

theorem cubeOfFrame_combo : ∀ k : Fin 5, ∀ x ∈ cubeOfFrame k,
    ∃ b₁ b₂ b₃ : Bool, (2 : Zsqrt5) • x = cubeCombo k b₁ b₂ b₃ := by
  decide +kernel

theorem combo_cubeOfFrame : ∀ k : Fin 5, ∀ b₁ b₂ b₃ : Bool,
    ∃ x ∈ cubeOfFrame k, (2 : Zsqrt5) • x = cubeCombo k b₁ b₂ b₃ := by
  decide +kernel

/-! ### Transfer lemmas -/

theorem halveToReal_add (x y : Fin 3 → Zsqrt5) :
    halveToReal (x + y) = halveToReal x + halveToReal y := by
  funext i; simp [halveToReal, map_add, add_div]

theorem halveToReal_smul (c : Zsqrt5) (x : Fin 3 → Zsqrt5) :
    halveToReal (c • x) = zsqrt5ToReal c • halveToReal x := by
  funext i; simp [halveToReal, map_mul, mul_div_assoc]

theorem halveToReal_two_smul (x : Fin 3 → Zsqrt5) :
    halveToReal ((2 : Zsqrt5) • x) = (2 : ℝ) • halveToReal x := by
  rw [halveToReal_smul, map_ofNat]

theorem zsqrt5ToReal_signZ (b : Bool) :
    zsqrt5ToReal (signZ b) = 1 ∨ zsqrt5ToReal (signZ b) = -1 := by
  cases b <;> simp [signZ]

theorem exists_signZ {s : ℝ} (hs : s = 1 ∨ s = -1) : ∃ b : Bool, zsqrt5ToReal (signZ b) = s := by
  rcases hs with rfl | rfl
  · exact ⟨true, by simp [signZ]⟩
  · exact ⟨false, by simp [signZ]⟩

theorem halveToReal_cubeCombo (k : Fin 5) (b₁ b₂ b₃ : Bool) :
    halveToReal (cubeCombo k b₁ b₂ b₃) =
      zsqrt5ToReal (signZ b₁) • halveToReal (cubeEdgeVecs k 0) +
        zsqrt5ToReal (signZ b₂) • halveToReal (cubeEdgeVecs k 1) +
          zsqrt5ToReal (signZ b₃) • halveToReal (cubeEdgeVecs k 2) := by
  rw [cubeCombo, halveToReal_add, halveToReal_add, halveToReal_smul, halveToReal_smul,
    halveToReal_smul]

theorem half_two_smul (v : Fin 3 → ℝ) : (1 / 2 : ℝ) • ((2 : ℝ) • v) = v := by
  rw [smul_smul]; norm_num

theorem halveToReal_dot_eq (a b : Fin 3 → Zsqrt5) :
    halveToReal a ⬝ᵥ halveToReal b = zsqrt5ToReal (dot3 a b) / 4 := dotProduct_halveToReal a b

/-! ### T1 -/

theorem officialCube_isCube (k : Fin 5) :
    (officialCube k).ncard = 8 ∧
    ∃ a : ℝ, 0 < a ∧ ∃ e₁ e₂ e₃ : Fin 3 → ℝ,
      e₁ ⬝ᵥ e₂ = 0 ∧ e₁ ⬝ᵥ e₃ = 0 ∧ e₂ ⬝ᵥ e₃ = 0 ∧
      e₁ ⬝ᵥ e₁ = a ^ 2 ∧ e₂ ⬝ᵥ e₂ = a ^ 2 ∧ e₃ ⬝ᵥ e₃ = a ^ 2 ∧
      (∃ m ∈ officialFrame k, ∃ t : ℝ, e₁ = t • m) ∧
      (∃ m ∈ officialFrame k, ∃ t : ℝ, e₂ = t • m) ∧
      (∃ m ∈ officialFrame k, ∃ t : ℝ, e₃ = t • m) ∧
      ∃ c : Fin 3 → ℝ, officialCube k =
        {p | ∃ s₁ s₂ s₃ : ℝ, (s₁ = 1 ∨ s₁ = -1) ∧ (s₂ = 1 ∨ s₂ = -1) ∧ (s₃ = 1 ∨ s₃ = -1) ∧
          p = c + (1 / 2 : ℝ) • (s₁ • e₁ + s₂ • e₂ + s₃ • e₃)} := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hsq : ∀ j : Fin 3, halveToReal (cubeEdgeVecs k j) ⬝ᵥ halveToReal (cubeEdgeVecs k j) =
      (3 + Real.sqrt 5) ^ 2 := by
    intro j
    rw [halveToReal_dot_eq, cubeEdgeVecs_sq k j, zsqrt5ToReal_cubeEdgeSq]
    rw [add_sq, h5]
    ring
  have hpar : ∀ j : Fin 3, ∃ m ∈ officialFrame k, ∃ t : ℝ,
      halveToReal (cubeEdgeVecs k j) = t • m := by
    intro j
    refine ⟨halveToReal (cubeFrameVecs k j),
      (mem_officialFrame_iff k _).mpr ⟨_, cubeFrameVecs_mem k j, rfl⟩,
      zsqrt5ToReal ⟨1, 1⟩ / 2, ?_⟩
    have h := congrArg halveToReal (cubeEdgeVecs_parallel k j)
    rw [halveToReal_two_smul, halveToReal_smul] at h
    rw [← half_two_smul (halveToReal (cubeEdgeVecs k j)), h, smul_smul]
    congr 1
    ring
  obtain ⟨o01, o02, o12⟩ := cubeEdgeVecs_orth k
  refine ⟨officialCube_ncard k, 3 + Real.sqrt 5, by positivity,
    halveToReal (cubeEdgeVecs k 0), halveToReal (cubeEdgeVecs k 1),
    halveToReal (cubeEdgeVecs k 2), ?_, ?_, ?_, hsq 0, hsq 1, hsq 2, hpar 0, hpar 1, hpar 2,
    0, ?_⟩
  · rw [halveToReal_dot_eq, o01, map_zero, zero_div]
  · rw [halveToReal_dot_eq, o02, map_zero, zero_div]
  · rw [halveToReal_dot_eq, o12, map_zero, zero_div]
  · rw [officialCube_eq_image]
    ext p
    simp only [Set.mem_image, Set.mem_ofPred_eq, zero_add]
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨b₁, b₂, b₃, h⟩ := cubeOfFrame_combo k x hx
      refine ⟨_, _, _, zsqrt5ToReal_signZ b₁, zsqrt5ToReal_signZ b₂, zsqrt5ToReal_signZ b₃, ?_⟩
      rw [← halveToReal_cubeCombo, ← h, halveToReal_two_smul, half_two_smul]
    · rintro ⟨s₁, s₂, s₃, hs₁, hs₂, hs₃, rfl⟩
      obtain ⟨b₁, rfl⟩ := exists_signZ hs₁
      obtain ⟨b₂, rfl⟩ := exists_signZ hs₂
      obtain ⟨b₃, rfl⟩ := exists_signZ hs₃
      obtain ⟨x, hx, h⟩ := combo_cubeOfFrame k b₁ b₂ b₃
      refine ⟨x, hx, ?_⟩
      rw [← halveToReal_cubeCombo, ← h, halveToReal_two_smul, half_two_smul]

/-! ### T2 -/

theorem icosahedralRotationGroup_dotProduct (g : icosahedralRotationGroup) (v w : Fin 3 → ℝ) :
    (((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v) ⬝ᵥ
        (((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ w) =
      v ⬝ᵥ w := by
  set A := ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ)
  have hA : Aᵀ * A = 1 := by
    have := ((g : specialOrthogonalGroup (Fin 3) ℝ)).prop.1
    exact this.1
  rw [dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, hA, one_mulVec]

theorem icosahedralRotationGroup_maps_vertex (g : icosahedralRotationGroup) {u : Fin 3 → ℝ}
    (hu : u ∈ icosahedronVertexSet) :
    ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ u ∈
      icosahedronVertexSet := by
  have hg : mem_icosahedralRotationGroup (g : specialOrthogonalGroup (Fin 3) ℝ) :=
    (mem_icosahedralRotationGroup_iff _).mp g.2
  rw [mem_icosahedralRotationGroup] at hg
  rw [← hg]
  exact ⟨u, hu, rfl⟩

theorem icosahedralRotationGroup_maps_faceSum (g : icosahedralRotationGroup) {p : Fin 3 → ℝ}
    (hp : p ∈ officialFaceSums) :
    ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ p ∈
      officialFaceSums := by
  obtain ⟨u, hu, v, hv, w, hw, h1, h2, h3, rfl⟩ := hp
  refine ⟨_, icosahedralRotationGroup_maps_vertex g hu, _, icosahedralRotationGroup_maps_vertex g hv,
    _, icosahedralRotationGroup_maps_vertex g hw, ?_, ?_, ?_, ?_⟩
  · rw [← mulVec_sub, icosahedralRotationGroup_dotProduct, h1]
  · rw [← mulVec_sub, icosahedralRotationGroup_dotProduct, h2]
  · rw [← mulVec_sub, icosahedralRotationGroup_dotProduct, h3]
  · rw [mulVec_add, mulVec_add]

theorem icosahedralRotationGroup_maps_officialCube_into (g : icosahedralRotationGroup) (k : Fin 5) :
    ∀ p ∈ officialCube k,
      ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ p ∈
        officialCube (((icosahedralRotationGroupMulEquivAlternatingGroup g :
          alternatingGroup (Fin 5)) : Perm (Fin 5)) k) := by
  rintro p ⟨hp, hsq⟩
  refine ⟨icosahedralRotationGroup_maps_faceSum g hp, fun m hm m' hm' => ?_⟩
  rw [← icosahedralRotationGroup_maps_officialFrame] at hm hm'
  obtain ⟨n, hn, rfl⟩ := hm
  obtain ⟨n', hn', rfl⟩ := hm'
  rw [icosahedralRotationGroup_dotProduct, icosahedralRotationGroup_dotProduct]
  exact hsq n hn n' hn'

theorem sigma_inv_apply_self (g : icosahedralRotationGroup) (k : Fin 5) :
    ((icosahedralRotationGroupMulEquivAlternatingGroup g⁻¹ : alternatingGroup (Fin 5)) :
        Perm (Fin 5))
      (((icosahedralRotationGroupMulEquivAlternatingGroup g : alternatingGroup (Fin 5)) :
        Perm (Fin 5)) k) = k := by
  rw [map_inv, Subgroup.coe_inv, Perm.inv_def, Equiv.symm_apply_apply]

theorem officialCube_image (g : icosahedralRotationGroup) (k : Fin 5) :
    (fun v => ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v) ''
        officialCube k =
      officialCube (((icosahedralRotationGroupMulEquivAlternatingGroup g :
        alternatingGroup (Fin 5)) : Perm (Fin 5)) k) := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact icosahedralRotationGroup_maps_officialCube_into g k p hp
  · intro hq
    have h := icosahedralRotationGroup_maps_officialCube_into g⁻¹ _ q hq
    rw [sigma_inv_apply_self] at h
    refine ⟨_, h, ?_⟩
    have := coe_inv_mul_mulVec ((g⁻¹ : icosahedralRotationGroup) : specialOrthogonalGroup (Fin 3) ℝ) q
    simpa using this

/-! ### T3 -/

open Classical in
noncomputable def officialCubeIndex (g : icosahedralRotationGroup) (k : Fin 5) : Fin 5 :=
  if h : ∃ j : Fin 5,
      (fun v => ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v) ''
        officialCube k = officialCube j then h.choose else k

theorem officialCubeIndex_eq (g : icosahedralRotationGroup) (k : Fin 5) :
    officialCubeIndex g k = ((icosahedralRotationGroupMulEquivAlternatingGroup g :
      alternatingGroup (Fin 5)) : Perm (Fin 5)) k := by
  have h : ∃ j : Fin 5,
      (fun v => ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v) ''
        officialCube k = officialCube j := ⟨_, officialCube_image g k⟩
  unfold officialCubeIndex
  split_ifs
  exact officialCube_injective ((Exists.choose_spec h).symm.trans (officialCube_image g k))

noncomputable def officialCubePerm (g : icosahedralRotationGroup) : Perm (Fin 5) where
  toFun := officialCubeIndex g
  invFun := officialCubeIndex g⁻¹
  left_inv := fun k => by
    rw [officialCubeIndex_eq, officialCubeIndex_eq, sigma_inv_apply_self]
  right_inv := fun k => by
    rw [officialCubeIndex_eq, officialCubeIndex_eq]
    have := sigma_inv_apply_self g⁻¹ k
    rwa [inv_inv] at this

theorem officialCubePerm_apply (g : icosahedralRotationGroup) :
    officialCubePerm g = ((icosahedralRotationGroupMulEquivAlternatingGroup g :
      alternatingGroup (Fin 5)) : Perm (Fin 5)) :=
  Equiv.ext fun k => officialCubeIndex_eq g k

noncomputable def officialCubeHom : icosahedralRotationGroup →* Perm (Fin 5) where
  toFun := officialCubePerm
  map_one' := by rw [officialCubePerm_apply, map_one]; rfl
  map_mul' := fun g h => by
    rw [officialCubePerm_apply, officialCubePerm_apply, officialCubePerm_apply, map_mul]; rfl

theorem officialCubeHom_spec :
    Function.Injective officialCubeHom ∧
    officialCubeHom.range = alternatingGroup (Fin 5) ∧
    (∀ g : icosahedralRotationGroup, officialCubeHom g =
      ((icosahedralRotationGroupMulEquivAlternatingGroup g : alternatingGroup (Fin 5)) :
        Perm (Fin 5))) ∧
    (∀ (g : icosahedralRotationGroup) (k : Fin 5),
      (fun v => ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v) ''
          officialCube k = officialCube (officialCubeHom g k)) := by
  have happ : ∀ g : icosahedralRotationGroup, officialCubeHom g =
      ((icosahedralRotationGroupMulEquivAlternatingGroup g : alternatingGroup (Fin 5)) :
        Perm (Fin 5)) := fun g => officialCubePerm_apply g
  refine ⟨fun g h hgh => ?_, ?_, happ, fun g k => by rw [happ]; exact officialCube_image g k⟩
  · rw [happ, happ] at hgh
    exact icosahedralRotationGroupMulEquivAlternatingGroup.injective (Subtype.ext hgh)
  · ext x
    rw [MonoidHom.mem_range]
    constructor
    · rintro ⟨g, rfl⟩
      rw [happ]
      exact (icosahedralRotationGroupMulEquivAlternatingGroup g).2
    · intro hx
      refine ⟨icosahedralRotationGroupMulEquivAlternatingGroup.symm ⟨x, hx⟩, ?_⟩
      rw [happ, MulEquiv.apply_symm_apply]

#print axioms officialCube_isCube
#print axioms officialCube_image
#print axioms officialCubeHom_spec
#print axioms officialCubeIndex_eq
#print axioms icosahedralRotationGroup_dotProduct
#print axioms icosahedralRotationGroup_maps_faceSum
#print axioms cubeOfFrame_combo
#print axioms combo_cubeOfFrame
