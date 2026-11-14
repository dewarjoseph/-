/-
Scratch file, dated 2026-11-10. Not a Lake target. Not peer reviewed.

Face-sum `{s, 2s, 3s}` sets (named 'cubes'; a name only) and the bijection between
involutions and edge sign-pairs `{p, -p}`. 'Cube' names only the `{s, 2s, 3s}` test: nothing
here proves these sets are geometric cubes, that they lie on any solid, or that the group
permutes them. 'Dual vertices' is a name only (no dodecahedron is defined). Some identifiers
keep earlier names; they refer to sign-pairs `{p, -p}` only.
identifier names are historical; no geometric line/axis claim is made

Imports `IcosahedralFramesInvolutions_2026-11-10` (src 70c3e9f0…). No text is copied.

Part 1 (cubes). `faceSums`: the 20 sums `u + v + w` over faces (pairwise squared distance 16)
of the doubled-scale ℤ[√5] icosahedron ('dual vertices' as a name only).
`cubeOfFrame i`: the face sums `f` whose squared projections `(f ⬝ m)²` agree for all `m` in
frame `i`. `IsCubeSet C`: 8 face sums with pairwise squared distances in `{s, 2s, 3s}` for
some `s`. Classification of these `{s, 2s, 3s}` 8-subsets of the 20 face sums: `isCubeSet_iff`
(`IsCubeSet C ↔ ∃ i, C = cubeOfFrame i`), `cubeSets_ncard` (= 5). In the ℤ[√5] model only:
points of `cubeOfFrame i` at squared distance `cubeEdgeSq` differ by a vector parallel to a
vector of frame `i`; every vector of frame `i` is parallel to such a difference; frame `i` is
the only frame with the first property; each face sum lies in exactly two `cubeOfFrame i`.
On the official vertex set, by a proved transfer from the ℤ[√5] model: `officialFaceSums`,
`officialCube`, `IsOfficialCube`, `isOfficialCube_iff`, `officialCubeSets_ncard`, and
`officialCube_edges_parallel_frame` (differences at squared distance `14 + 6√5` are parallel
to vectors of `officialFrame i`). The other ℤ[√5]-model facts above are not stated over ℝ.

Part 2 (involutions). For non-identity `g` with `g * g = 1` in the imported official group,
any two official edge vectors fixed by `g` agree up to sign; two such `g` fixing the same
official edge vector are equal; this is packaged as a bijection to the edge sign-pairs,
each `g` fixing both points of its pair; and
`natCard_involutions : Nat.card {g // g ≠ 1 ∧ g * g = 1} = 15`. Not proved: that `g` fixes
exactly the span of `p`, that the pairs are distinct one-dimensional subspaces, or anything
about `g` on `p⊥`.
-/

import «IcosahedralFramesInvolutions_2026-11-10»

open Equiv Matrix

/-! ## Part 1: face-sum `{s, 2s, 3s}` sets ('cubes', a name only; ℤ[√5] model) -/

/-- Squared distance. -/
def sqDist3 (x y : Fin 3 → Zsqrt5) : Zsqrt5 := dot3 (edgeVSub x y) (edgeVSub x y)

/-- Face sums `u + v + w` over faces (three listed vertices at pairwise squared distance 16):
the 20 face sums ('dual vertices' as a name only). -/
def faceSums : List (Fin 3 → Zsqrt5) :=
  (icosahedronVerticesZsqrt5.flatMap fun u => icosahedronVerticesZsqrt5.flatMap fun v =>
    icosahedronVerticesZsqrt5.filterMap fun w =>
      if sqDist3 u v = 16 ∧ sqDist3 v w = 16 ∧ sqDist3 u w = 16 then
        some (edgeVAdd (edgeVAdd u v) w) else none).dedup

theorem faceSums_length : faceSums.length = 20 := by decide +kernel

theorem faceSums_nodup : faceSums.Nodup := by
  unfold faceSums; exact List.nodup_dedup _

theorem faceSum_mem :
    ∀ u ∈ icosahedronVerticesZsqrt5, ∀ v ∈ icosahedronVerticesZsqrt5,
      ∀ w ∈ icosahedronVerticesZsqrt5, sqDist3 u v = 16 → sqDist3 v w = 16 → sqDist3 u w = 16 →
        edgeVAdd (edgeVAdd u v) w ∈ faceSums := by
  decide +kernel

theorem faceSums_mem_face :
    ∀ x ∈ faceSums, ∃ u ∈ icosahedronVerticesZsqrt5, ∃ v ∈ icosahedronVerticesZsqrt5,
      ∃ w ∈ icosahedronVerticesZsqrt5, sqDist3 u v = 16 ∧ sqDist3 v w = 16 ∧
        sqDist3 u w = 16 ∧ x = edgeVAdd (edgeVAdd u v) w := by
  decide +kernel

/-- The cube of frame `i`: face sums with equal squared projections onto all vectors of
frame `i` ('cube' is a name only). -/
def cubeOfFrame (i : Fin 5) : List (Fin 3 → Zsqrt5) :=
  faceSums.filter fun f => decide (∀ m ∈ frame i, ∀ m' ∈ frame i,
    dot3 f m * dot3 f m = dot3 f m' * dot3 f m')

/-- The squared distance named `cubeEdgeSq` (a name only) at this scale. -/
def cubeEdgeSq : Zsqrt5 := ⟨56, 24⟩

theorem cubeOfFrame_length : ∀ i : Fin 5, (cubeOfFrame i).length = 8 := by decide +kernel

theorem cubeOfFrame_nodup (i : Fin 5) : (cubeOfFrame i).Nodup := faceSums_nodup.filter _

theorem cubeOfFrame_subset (i : Fin 5) : ∀ x ∈ cubeOfFrame i, x ∈ faceSums := by
  intro x hx
  simp only [cubeOfFrame, List.mem_filter] at hx
  exact hx.1

theorem cubeOfFrame_sqDist : ∀ i : Fin 5, ∀ x ∈ cubeOfFrame i, ∀ y ∈ cubeOfFrame i, x ≠ y →
    sqDist3 x y = cubeEdgeSq ∨ sqDist3 x y = 2 * cubeEdgeSq ∨ sqDist3 x y = 3 * cubeEdgeSq := by
  decide +kernel

theorem cubeOfFrame_distinct : ∀ i j : Fin 5, i ≠ j → ∃ x ∈ cubeOfFrame i, x ∉ cubeOfFrame j := by
  decide +kernel

/-- ℤ[√5] model only: each face sum lies in exactly two of the five `cubeOfFrame i`. -/
theorem faceSums_mem_two_cubes :
    ∀ x ∈ faceSums, ((List.finRange 5).filter fun i => decide (x ∈ cubeOfFrame i)).length = 2 := by
  decide +kernel

/-- ℤ[√5] model only: points of `cubeOfFrame i` at squared distance `cubeEdgeSq` differ by
a vector parallel to a vector of frame `i` ... -/
theorem cubeOfFrame_edges_parallel_frame : ∀ i : Fin 5, ∀ x ∈ cubeOfFrame i,
    ∀ y ∈ cubeOfFrame i, sqDist3 x y = cubeEdgeSq →
      ∃ m ∈ frame i, cross3 (edgeVSub x y) m = 0 := by
  decide +kernel

/-- ... (ℤ[√5] model only) every vector of frame `i` is parallel to such a difference ... -/
theorem frame_parallel_cubeOfFrame_edge : ∀ i : Fin 5, ∀ m ∈ frame i,
    ∃ x ∈ cubeOfFrame i, ∃ y ∈ cubeOfFrame i, sqDist3 x y = cubeEdgeSq ∧
      cross3 (edgeVSub x y) m = 0 := by
  decide +kernel

/-- ... (ℤ[√5] model only) and frame `i` is the only frame with the first property. -/
theorem cubeOfFrame_edges_parallel_frame_unique : ∀ i j : Fin 5,
    (∀ x ∈ cubeOfFrame i, ∀ y ∈ cubeOfFrame i, sqDist3 x y = cubeEdgeSq →
      ∃ m ∈ frame j, cross3 (edgeVSub x y) m = 0) → i = j := by
  decide +kernel

/-! ### Classification -/

/-- `6 · d(x, y) ∈ {T, 2T, 3T}` (the `{s, 2s, 3s}` condition with `T = 6s`). -/
abbrev cubeRel (T : Zsqrt5) (x y : Fin 3 → Zsqrt5) : Prop :=
  6 * sqDist3 x y = T ∨ 6 * sqDist3 x y = 2 * T ∨ 6 * sqDist3 x y = 3 * T

theorem cube_core_K1 : ∀ a ∈ faceSums, ∀ b ∈ faceSums, a ≠ b →
    ∀ T ∈ [6 * sqDist3 a b, 3 * sqDist3 a b, 2 * sqDist3 a b], T ≠ 6 * cubeEdgeSq →
      cubeRel T a b →
        (faceSums.filter fun x => decide (x ≠ a ∧ x ≠ b ∧ cubeRel T a x ∧ cubeRel T b x)).length
          < 6 := by
  decide +kernel

theorem cube_core_K2 : ∀ a ∈ faceSums, ∀ b ∈ faceSums, 6 * sqDist3 a b = 6 * cubeEdgeSq →
    ∃ i : Fin 5, a ∈ cubeOfFrame i ∧ b ∈ cubeOfFrame i ∧
      ∀ c ∈ faceSums.filter (fun c => decide (c ≠ a ∧ c ≠ b ∧ cubeRel (6 * cubeEdgeSq) a c ∧
        cubeRel (6 * cubeEdgeSq) b c ∧ c ∉ cubeOfFrame i)),
        (faceSums.filter fun x => decide (x ≠ a ∧ x ≠ b ∧ x ≠ c ∧ cubeRel (6 * cubeEdgeSq) a x ∧
          cubeRel (6 * cubeEdgeSq) b x ∧ cubeRel (6 * cubeEdgeSq) c x)).length < 5 := by
  decide +kernel

theorem sqDist3_self (x : Fin 3 → Zsqrt5) : sqDist3 x x = 0 := by
  simp [sqDist3, edgeVSub, dot3]

theorem five_le_of_subset {C : Finset (Fin 3 → Zsqrt5)} (hC : C.card = 8)
    {a b c : Fin 3 → Zsqrt5} (ha : a ∈ C) (hb : b ∈ C) (hc : c ∈ C) (hab : a ≠ b)
    (hca : c ≠ a) (hcb : c ≠ b)
    (l : List (Fin 3 → Zsqrt5)) (h : ∀ x ∈ C, x ≠ a → x ≠ b → x ≠ c → x ∈ l) :
    5 ≤ l.length := by
  have h1 : (((C.erase a).erase b).erase c).card = 5 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hcb, Finset.mem_erase.mpr ⟨hca, hc⟩⟩),
      Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hab, hb⟩),
      Finset.card_erase_of_mem ha, hC]
  have h2 : ((C.erase a).erase b).erase c ⊆ l.toFinset := by
    intro x hx
    simp only [Finset.mem_erase] at hx
    exact List.mem_toFinset.mpr (h x hx.2.2.2 hx.2.2.1 hx.2.1 hx.1)
  calc 5 = (((C.erase a).erase b).erase c).card := h1.symm
    _ ≤ l.toFinset.card := Finset.card_le_card h2
    _ ≤ l.length := List.toFinset_card_le l

theorem cube_core_K3 : ∀ a ∈ faceSums, ∀ b ∈ faceSums, a ≠ b →
    cubeRel (6 * cubeEdgeSq) a b → 6 * sqDist3 a b ≠ 6 * cubeEdgeSq →
      (faceSums.filter fun x => decide (x ≠ a ∧ x ≠ b ∧ cubeRel (6 * cubeEdgeSq) a x ∧
        cubeRel (6 * cubeEdgeSq) b x ∧ 6 * sqDist3 a x ≠ 6 * cubeEdgeSq ∧
          6 * sqDist3 b x ≠ 6 * cubeEdgeSq)).length < 6 := by
  decide +kernel

theorem six_le_of_subset {C : Finset (Fin 3 → Zsqrt5)} (hC : C.card = 8)
    {a b : Fin 3 → Zsqrt5} (ha : a ∈ C) (hb : b ∈ C) (hab : a ≠ b)
    (l : List (Fin 3 → Zsqrt5)) (h : ∀ x ∈ C, x ≠ a → x ≠ b → x ∈ l) : 6 ≤ l.length := by
  have h1 : ((C.erase a).erase b).card = 6 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hab, hb⟩),
      Finset.card_erase_of_mem ha, hC]
  have h2 : (C.erase a).erase b ⊆ l.toFinset := by
    intro x hx
    simp only [Finset.mem_erase] at hx
    exact List.mem_toFinset.mpr (h x hx.2.2 hx.2.1 hx.1)
  calc 6 = ((C.erase a).erase b).card := h1.symm
    _ ≤ l.toFinset.card := Finset.card_le_card h2
    _ ≤ l.length := List.toFinset_card_le l

/-- Core classification with `T = 6s`. -/
theorem cube_core (C : Finset (Fin 3 → Zsqrt5)) (hF : ∀ x ∈ C, x ∈ faceSums)
    (hcard : C.card = 8) (T : Zsqrt5) (a b : Fin 3 → Zsqrt5) (ha : a ∈ C) (hb : b ∈ C)
    (hab : a ≠ b) (hT : T = 6 * sqDist3 a b ∨ T = 3 * sqDist3 a b ∨ T = 2 * sqDist3 a b)
    (hR : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → cubeRel T x y) :
    ∃ i : Fin 5, C = (cubeOfFrame i).toFinset := by
  by_cases hT0 : T = 6 * cubeEdgeSq
  · subst hT0
    by_cases hs : ∃ x ∈ C, ∃ y ∈ C, 6 * sqDist3 x y = 6 * cubeEdgeSq
    · obtain ⟨x, hx, y, hy, hxy⟩ := hs
      obtain ⟨i, hxi, hyi, hall⟩ := cube_core_K2 x (hF x hx) y (hF y hy) hxy
      have hxy' : x ≠ y := by
        rintro rfl
        rw [sqDist3_self, mul_zero] at hxy
        exact absurd hxy (by decide)
      by_cases hout : ∃ z ∈ C, z ≠ x ∧ z ≠ y ∧ z ∉ cubeOfFrame i
      · exfalso
        obtain ⟨z, hz, hzx, hzy, hzi⟩ := hout
        have h5 := five_le_of_subset hcard hx hy hz hxy' hzx hzy
          (faceSums.filter fun w => decide (w ≠ x ∧ w ≠ y ∧ w ≠ z ∧
            cubeRel (6 * cubeEdgeSq) x w ∧ cubeRel (6 * cubeEdgeSq) y w ∧
              cubeRel (6 * cubeEdgeSq) z w)) (by
            intro w hw hwx hwy hwz
            simp only [List.mem_filter, decide_eq_true_eq]
            exact ⟨hF w hw, hwx, hwy, hwz, hR x hx w hw (Ne.symm hwx),
              hR y hy w hw (Ne.symm hwy), hR z hz w hw (Ne.symm hwz)⟩)
        have := hall z (by
          simp only [List.mem_filter, decide_eq_true_eq]
          exact ⟨hF z hz, hzx, hzy, hR x hx z hz (Ne.symm hzx), hR y hy z hz (Ne.symm hzy), hzi⟩)
        omega
      refine ⟨i, Finset.eq_of_subset_of_card_le ?_ ?_⟩
      · intro z hz
        rw [List.mem_toFinset]
        by_cases hzx : z = x
        · rw [hzx]; exact hxi
        by_cases hzy : z = y
        · rw [hzy]; exact hyi
        by_contra hzi
        exact hout ⟨z, hz, hzx, hzy, hzi⟩
      · rw [hcard, List.toFinset_card_of_nodup (cubeOfFrame_nodup i), cubeOfFrame_length]
    · have hs' : ∀ x ∈ C, ∀ y ∈ C, 6 * sqDist3 x y ≠ 6 * cubeEdgeSq :=
        fun x hx y hy h => hs ⟨x, hx, y, hy, h⟩
      exfalso
      have h6 := six_le_of_subset hcard ha hb hab
        (faceSums.filter fun x => decide (x ≠ a ∧ x ≠ b ∧ cubeRel (6 * cubeEdgeSq) a x ∧
          cubeRel (6 * cubeEdgeSq) b x ∧ 6 * sqDist3 a x ≠ 6 * cubeEdgeSq ∧
            6 * sqDist3 b x ≠ 6 * cubeEdgeSq)) (by
          intro x hx hxa hxb
          simp only [List.mem_filter, decide_eq_true_eq]
          exact ⟨hF x hx, hxa, hxb, hR a ha x hx (Ne.symm hxa), hR b hb x hx (Ne.symm hxb),
            hs' a ha x hx, hs' b hb x hx⟩)
      have := cube_core_K3 a (hF a ha) b (hF b hb) hab (hR a ha b hb hab) (hs' a ha b hb)
      omega
  · exfalso
    have h6 := six_le_of_subset hcard ha hb hab
      (faceSums.filter fun x => decide (x ≠ a ∧ x ≠ b ∧ cubeRel T a x ∧ cubeRel T b x)) (by
        intro x hx hxa hxb
        simp only [List.mem_filter, decide_eq_true_eq]
        exact ⟨hF x hx, hxa, hxb, hR a ha x hx (Ne.symm hxa), hR b hb x hx (Ne.symm hxb)⟩)
    have hTmem : T ∈ [6 * sqDist3 a b, 3 * sqDist3 a b, 2 * sqDist3 a b] := by
      rcases hT with h | h | h <;> simp [h]
    have := cube_core_K1 a (hF a ha) b (hF b hb) hab T hTmem hT0 (hR a ha b hb hab)
    omega

/-- 'Cube sets' (a name only): 8 face sums with pairwise squared distances in `{s, 2s, 3s}`. -/
def IsCubeSet (C : Finset (Fin 3 → Zsqrt5)) : Prop :=
  (∀ x ∈ C, x ∈ faceSums) ∧ C.card = 8 ∧ ∃ s : Zsqrt5, ∀ x ∈ C, ∀ y ∈ C, x ≠ y →
    sqDist3 x y = s ∨ sqDist3 x y = 2 * s ∨ sqDist3 x y = 3 * s

/-- Classification of the `{s, 2s, 3s}` 8-subsets of the 20 face sums (ℤ[√5] model): exactly
the five `cubeOfFrame i`. -/
theorem isCubeSet_iff (C : Finset (Fin 3 → Zsqrt5)) :
    IsCubeSet C ↔ ∃ i : Fin 5, C = (cubeOfFrame i).toFinset := by
  constructor
  · rintro ⟨hF, hcard, s, hs⟩
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by rw [hcard]; norm_num)
    refine cube_core C hF hcard (6 * s) a b ha hb hab ?_ ?_
    · rcases hs a ha b hb hab with h | h | h <;> rw [h]
      · left; ring
      · right; left; ring
      · right; right; ring
    · intro x hx y hy hxy
      unfold cubeRel
      rcases hs x hx y hy hxy with h | h | h <;> rw [h]
      · left; ring
      · right; left; ring
      · right; right; ring
  · rintro ⟨i, rfl⟩
    refine ⟨fun x hx => ?_, ?_, cubeEdgeSq, fun x hx y hy hxy => ?_⟩
    · rw [List.mem_toFinset] at hx; exact cubeOfFrame_subset i x hx
    · rw [List.toFinset_card_of_nodup (cubeOfFrame_nodup i), cubeOfFrame_length]
    · rw [List.mem_toFinset] at hx hy; exact cubeOfFrame_sqDist i x hx y hy hxy

theorem cubeOfFrame_toFinset_injective :
    Function.Injective fun i : Fin 5 => (cubeOfFrame i).toFinset := by
  intro i j h
  by_contra hij
  obtain ⟨x, hx, hxj⟩ := cubeOfFrame_distinct i j hij
  have hx' : x ∈ (cubeOfFrame j).toFinset := by
    rw [← show (cubeOfFrame i).toFinset = (cubeOfFrame j).toFinset from h]
    exact List.mem_toFinset.mpr hx
  exact hxj (List.mem_toFinset.mp hx')

/-- Exactly five such 8-subsets. -/
theorem cubeSets_ncard : {C | IsCubeSet C}.ncard = 5 := by
  have h : {C | IsCubeSet C} = Set.range fun i : Fin 5 => (cubeOfFrame i).toFinset := by
    ext C
    simp only [Set.mem_ofPred_eq, Set.mem_range, isCubeSet_iff]
    exact ⟨fun ⟨i, h⟩ => ⟨i, h.symm⟩, fun ⟨i, h⟩ => ⟨i, h.symm⟩⟩
  rw [h, ← Set.image_univ, Set.ncard_image_of_injective _ cubeOfFrame_toFinset_injective,
    Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]

/-! ## Part 1 on the official vertex set (by proved transfer from the ℤ[√5] model) -/

theorem halve_sqDist (x y : Fin 3 → Zsqrt5) :
    (halveToReal x - halveToReal y) ⬝ᵥ (halveToReal x - halveToReal y) =
      zsqrt5ToReal (sqDist3 x y) / 4 := by
  rw [← halveToReal_edgeVSub, dotProduct_halveToReal]; rfl

theorem real_sq_four_iff (x y : Fin 3 → Zsqrt5) :
    (halveToReal x - halveToReal y) ⬝ᵥ (halveToReal x - halveToReal y) = 4 ↔
      sqDist3 x y = 16 := by
  rw [halve_sqDist]
  constructor
  · intro h; apply zsqrt5ToReal_injective; rw [map_ofNat]; linarith
  · intro h; rw [h, map_ofNat]; norm_num

/-- Official face sums: `u + v + w` for official vertices at pairwise squared distance 4. -/
def officialFaceSums : Set (Fin 3 → ℝ) :=
  {p | ∃ u ∈ icosahedronVertexSet, ∃ v ∈ icosahedronVertexSet, ∃ w ∈ icosahedronVertexSet,
    (u - v) ⬝ᵥ (u - v) = 4 ∧ (v - w) ⬝ᵥ (v - w) = 4 ∧ (u - w) ⬝ᵥ (u - w) = 4 ∧ p = u + v + w}

theorem officialFaceSums_eq_image : officialFaceSums = halveToReal '' {x | x ∈ faceSums} := by
  ext p
  constructor
  · rintro ⟨u, hu, v, hv, w, hw, h1, h2, h3, rfl⟩
    rw [← halveToReal_image_icosahedronVerticesZsqrt5] at hu hv hw
    obtain ⟨u', hu', rfl⟩ := hu
    obtain ⟨v', hv', rfl⟩ := hv
    obtain ⟨w', hw', rfl⟩ := hw
    rw [real_sq_four_iff] at h1 h2 h3
    refine ⟨edgeVAdd (edgeVAdd u' v') w', faceSum_mem u' hu' v' hv' w' hw' h1 h2 h3, ?_⟩
    rw [halveToReal_edgeVAdd, halveToReal_edgeVAdd]
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨u, hu, v, hv, w, hw, h1, h2, h3, rfl⟩ := faceSums_mem_face x hx
    refine ⟨halveToReal u, halveToReal_mem_icosahedronVertexSet hu, halveToReal v,
      halveToReal_mem_icosahedronVertexSet hv, halveToReal w,
      halveToReal_mem_icosahedronVertexSet hw, (real_sq_four_iff u v).mpr h1,
      (real_sq_four_iff v w).mpr h2, (real_sq_four_iff u w).mpr h3, ?_⟩
    rw [halveToReal_edgeVAdd, halveToReal_edgeVAdd]

theorem officialFaceSums_ncard : officialFaceSums.ncard = 20 := by
  rw [officialFaceSums_eq_image, ncard_image_list faceSums_nodup, faceSums_length]

theorem halve_dot_sq_eq_iff (x y y' : Fin 3 → Zsqrt5) :
    (halveToReal x ⬝ᵥ halveToReal y) ^ 2 = (halveToReal x ⬝ᵥ halveToReal y') ^ 2 ↔
      dot3 x y * dot3 x y = dot3 x y' * dot3 x y' := by
  rw [dotProduct_halveToReal, dotProduct_halveToReal]
  constructor
  · intro h
    apply zsqrt5ToReal_injective
    rw [map_mul, map_mul]
    nlinarith [h]
  · intro h
    have h' := congrArg zsqrt5ToReal h
    rw [map_mul, map_mul] at h'
    rw [div_pow, div_pow, sq, sq (zsqrt5ToReal (dot3 x y')), h']

/-- `officialCube i` ('cube' a name only): official face sums with equal squared projections onto all
vectors of `officialFrame i`. -/
def officialCube (i : Fin 5) : Set (Fin 3 → ℝ) :=
  {p | p ∈ officialFaceSums ∧ ∀ m ∈ officialFrame i, ∀ m' ∈ officialFrame i,
    (p ⬝ᵥ m) ^ 2 = (p ⬝ᵥ m') ^ 2}

theorem officialCube_eq_image (i : Fin 5) :
    officialCube i = halveToReal '' {x | x ∈ cubeOfFrame i} := by
  ext p
  simp only [officialCube, officialFaceSums_eq_image, Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, h⟩
    refine ⟨x, ?_, rfl⟩
    simp only [cubeOfFrame, List.mem_filter, decide_eq_true_eq]
    refine ⟨hx, fun y hy y' hy' => ?_⟩
    rw [← halve_dot_sq_eq_iff]
    exact h _ ((mem_officialFrame_iff i _).mpr ⟨y, hy, rfl⟩) _
      ((mem_officialFrame_iff i _).mpr ⟨y', hy', rfl⟩)
  · rintro ⟨x, hx, rfl⟩
    simp only [cubeOfFrame, List.mem_filter, decide_eq_true_eq] at hx
    refine ⟨⟨x, hx.1, rfl⟩, fun m hm m' hm' => ?_⟩
    obtain ⟨y, hy, rfl⟩ := (mem_officialFrame_iff i m).mp hm
    obtain ⟨y', hy', rfl⟩ := (mem_officialFrame_iff i m').mp hm'
    rw [halve_dot_sq_eq_iff]
    exact hx.2 y hy y' hy'

theorem officialCube_ncard (i : Fin 5) : (officialCube i).ncard = 8 := by
  rw [officialCube_eq_image, ncard_image_list (cubeOfFrame_nodup i), cubeOfFrame_length]

theorem officialCube_finite (i : Fin 5) : (officialCube i).Finite := by
  rw [officialCube_eq_image]; exact (List.finite_toSet _).image _

/-- `IsOfficialCube` (a name only): 8 official face sums with pairwise squared distances in `{s, 2s, 3s}`. -/
def IsOfficialCube (C : Finset (Fin 3 → ℝ)) : Prop :=
  (∀ p ∈ C, p ∈ officialFaceSums) ∧ C.card = 8 ∧ ∃ s : ℝ, ∀ p ∈ C, ∀ q ∈ C, p ≠ q →
    (p - q) ⬝ᵥ (p - q) = s ∨ (p - q) ⬝ᵥ (p - q) = 2 * s ∨ (p - q) ⬝ᵥ (p - q) = 3 * s

/-- Classification of the `{s, 2s, 3s}` 8-subsets of the 20 official face sums (by proved
transfer): exactly the five `officialCube i`. -/
theorem isOfficialCube_iff (C : Finset (Fin 3 → ℝ)) :
    IsOfficialCube C ↔ ∃ i : Fin 5, (C : Set (Fin 3 → ℝ)) = officialCube i := by
  classical
  constructor
  · rintro ⟨hF, hcard, s, hs⟩
    let C' := faceSums.toFinset.filter fun x => halveToReal x ∈ C
    have hC : C = C'.image halveToReal := by
      ext p
      simp only [C', Finset.mem_image, Finset.mem_filter, List.mem_toFinset]
      constructor
      · intro hp
        have := hF p hp
        rw [officialFaceSums_eq_image] at this
        obtain ⟨x, hx, rfl⟩ := this
        exact ⟨x, ⟨hx, hp⟩, rfl⟩
      · rintro ⟨x, ⟨-, hx⟩, rfl⟩
        exact hx
    have hF' : ∀ x ∈ C', x ∈ faceSums := by
      intro x hx
      simp only [C', Finset.mem_filter, List.mem_toFinset] at hx
      exact hx.1
    have hmem : ∀ x ∈ C', halveToReal x ∈ C := by
      intro x hx
      simp only [C', Finset.mem_filter] at hx
      exact hx.2
    have hcard' : C'.card = 8 := by
      rw [hC, Finset.card_image_of_injective _ halveToReal_injective] at hcard
      exact hcard
    have hs' : ∀ x ∈ C', ∀ y ∈ C', x ≠ y →
        zsqrt5ToReal (sqDist3 x y) / 4 = s ∨ zsqrt5ToReal (sqDist3 x y) / 4 = 2 * s ∨
          zsqrt5ToReal (sqDist3 x y) / 4 = 3 * s := by
      intro x hx y hy hxy
      rw [← halve_sqDist]
      exact hs _ (hmem x hx) _ (hmem y hy) (fun h => hxy (halveToReal_injective h))
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by rw [hcard']; norm_num)
    have hT : ∃ T : Zsqrt5, (T = 6 * sqDist3 a b ∨ T = 3 * sqDist3 a b ∨ T = 2 * sqDist3 a b) ∧
        zsqrt5ToReal T = 24 * s := by
      rcases hs' a ha b hb hab with h | h | h
      · exact ⟨6 * sqDist3 a b, Or.inl rfl, by rw [map_mul, map_ofNat]; linarith⟩
      · exact ⟨3 * sqDist3 a b, Or.inr (Or.inl rfl), by rw [map_mul, map_ofNat]; linarith⟩
      · exact ⟨2 * sqDist3 a b, Or.inr (Or.inr rfl), by rw [map_mul, map_ofNat]; linarith⟩
    obtain ⟨T, hTc, hTs⟩ := hT
    have hR : ∀ x ∈ C', ∀ y ∈ C', x ≠ y → cubeRel T x y := by
      intro x hx y hy hxy
      unfold cubeRel
      rcases hs' x hx y hy hxy with h | h | h
      · left; apply zsqrt5ToReal_injective; rw [map_mul, map_ofNat]; linarith
      · right; left; apply zsqrt5ToReal_injective; rw [map_mul, map_mul, map_ofNat, map_ofNat]
        linarith
      · right; right; apply zsqrt5ToReal_injective; rw [map_mul, map_mul, map_ofNat, map_ofNat]
        linarith
    obtain ⟨i, hi⟩ := cube_core C' hF' hcard' T a b ha hb hab hTc hR
    refine ⟨i, ?_⟩
    rw [hC, Finset.coe_image, hi, List.coe_toFinset, officialCube_eq_image]
  · rintro ⟨i, hi⟩
    have hmem : ∀ p, p ∈ C ↔ p ∈ officialCube i := fun p => by
      rw [← Finset.mem_coe, hi]
    refine ⟨fun p hp => ((hmem p).mp hp).1, ?_, zsqrt5ToReal cubeEdgeSq / 4,
      fun p hp q hq hpq => ?_⟩
    · rw [← Set.ncard_coe_finset, hi, officialCube_ncard]
    · rw [hmem, officialCube_eq_image] at hp hq
      obtain ⟨x, hx, rfl⟩ := hp
      obtain ⟨y, hy, rfl⟩ := hq
      have hxy : x ≠ y := fun h => hpq (by rw [h])
      rw [halve_sqDist]
      rcases cubeOfFrame_sqDist i x hx y hy hxy with h | h | h <;> rw [h]
      · left; rfl
      · right; left; rw [map_mul, map_ofNat]; ring
      · right; right; rw [map_mul, map_ofNat]; ring

theorem officialCube_injective : Function.Injective officialCube := by
  intro i j h
  by_contra hij
  obtain ⟨x, hx, hxj⟩ := cubeOfFrame_distinct i j hij
  have hx' : halveToReal x ∈ officialCube j := by
    rw [← h, officialCube_eq_image]; exact ⟨x, hx, rfl⟩
  rw [officialCube_eq_image] at hx'
  obtain ⟨y, hy, hyx⟩ := hx'
  exact hxj (halveToReal_injective hyx ▸ hy)

/-- Exactly five such 8-subsets of the official face sums. -/
theorem officialCubeSets_ncard : {C : Finset (Fin 3 → ℝ) | IsOfficialCube C}.ncard = 5 := by
  have himg : (fun C : Finset (Fin 3 → ℝ) => (C : Set (Fin 3 → ℝ))) ''
      {C | IsOfficialCube C} = Set.range officialCube := by
    ext S
    simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_range]
    constructor
    · rintro ⟨C, hC, rfl⟩
      obtain ⟨i, hi⟩ := (isOfficialCube_iff C).mp hC
      exact ⟨i, hi.symm⟩
    · rintro ⟨i, rfl⟩
      refine ⟨(officialCube_finite i).toFinset, ?_, Set.Finite.coe_toFinset _⟩
      exact (isOfficialCube_iff _).mpr ⟨i, Set.Finite.coe_toFinset _⟩
  rw [← Set.ncard_image_of_injective _ Finset.coe_injective, himg, ← Set.image_univ,
    Set.ncard_image_of_injective _ officialCube_injective, Set.ncard_univ,
    Nat.card_eq_fintype_card, Fintype.card_fin]

theorem zsqrt5ToReal_cubeEdgeSq : zsqrt5ToReal cubeEdgeSq = 56 + 24 * Real.sqrt 5 := by
  rw [zsqrt5ToReal_apply]; norm_num [cubeEdgeSq]

/-- Two points of `officialCube i` at squared distance `14 + 6√5` differ by a vector parallel
to a vector of `officialFrame i`. -/
theorem officialCube_edges_parallel_frame (i : Fin 5) :
    ∀ p ∈ officialCube i, ∀ q ∈ officialCube i, (p - q) ⬝ᵥ (p - q) = 14 + 6 * Real.sqrt 5 →
      ∃ m ∈ officialFrame i, crossProduct (p - q) m = 0 := by
  intro p hp q hq hpq
  rw [officialCube_eq_image] at hp hq
  obtain ⟨x, hx, rfl⟩ := hp
  obtain ⟨y, hy, rfl⟩ := hq
  have hd : sqDist3 x y = cubeEdgeSq := by
    apply zsqrt5ToReal_injective
    rw [halve_sqDist] at hpq
    rw [zsqrt5ToReal_cubeEdgeSq]
    linarith
  obtain ⟨m, hm, hc⟩ := cubeOfFrame_edges_parallel_frame i x hx y hy hd
  refine ⟨halveToReal m, (mem_officialFrame_iff i _).mpr ⟨m, hm, rfl⟩, ?_⟩
  rw [← halveToReal_edgeVSub, halveToReal_cross_eq_zero_iff]
  exact hc

/-! ## Part 2: involutions and edge sign-pairs `{p, -p}` -/

theorem realQuarter_mulVec_halveToReal_iff (S : Matrix (Fin 3) (Fin 3) Zsqrt5)
    (v w : Fin 3 → Zsqrt5) :
    realQuarter S *ᵥ halveToReal v = halveToReal w ↔ S *ᵥ v = (4 : Zsqrt5) • w := by
  constructor
  · intro h
    funext i
    have hi := congrFun h i
    have key : (realQuarter S *ᵥ halveToReal v) i = zsqrt5ToReal ((S *ᵥ v) i) / 8 := by
      rw [halveToReal_eq, realQuarter, Matrix.smul_mulVec, Matrix.mulVec_smul]
      simp only [Pi.smul_apply, smul_eq_mul, map_mulVec_apply]
      ring
    rw [key] at hi
    simp only [halveToReal] at hi
    apply zsqrt5ToReal_injective
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_ofNat]
    linarith
  · exact realQuarter_mulVec_halveToReal S

theorem mem_scaledInvolutions {A : M3} :
    A ∈ scaledInvolutions ↔ A ∈ scaledRotationList ∧ A ≠ M3.scal 4 ∧ A.mul A = M3.scal 16 := by
  simp only [scaledInvolutions, List.mem_filter, decide_eq_true_eq]

theorem scaledInvolutions_nodup : scaledInvolutions.Nodup :=
  scaledRotationList_nodup.filter _

/-- An involution among the 60 fixes (up to the factor 4) at most one pair `±x`. -/
theorem scaledInvolution_fixed_unique :
    ∀ A ∈ scaledInvolutions, ∀ x ∈ edgeSums, ∀ y ∈ edgeSums,
      A.mulVec x = (4 : Zsqrt5) • x → A.mulVec y = (4 : Zsqrt5) • y → y = x ∨ y = -x := by
  decide +kernel

/-- An edge sum is fixed (up to the factor 4) by at most one involution among the 60. -/
theorem scaledInvolution_unique_of_fixed :
    ∀ A ∈ scaledInvolutions, ∀ B ∈ scaledInvolutions, ∀ x ∈ edgeSums,
      A.mulVec x = (4 : Zsqrt5) • x → B.mulVec x = (4 : Zsqrt5) • x → A = B := by
  decide +kernel

theorem repM3_mul_self_of_sq {S : scaledIcosahedralRotations} (hS2 : S * S = 1) :
    (repM3 S).mul (repM3 S) = M3.scal 16 := by
  apply M3.toMatrix_injective
  rw [M3.toMatrix_mul, repM3_toMatrix, M3.toMatrix_scal]
  have h := (scaledMul_eq_iff S S 1).mp (by rw [← scaledIcosahedralRotations_mul_def]; exact hS2)
  rw [h, scaledIcosahedralGroup_one_coe, smul_smul]
  norm_num

theorem repM3_ne_of_ne_one {S : scaledIcosahedralRotations} (hS1 : S ≠ 1) :
    repM3 S ≠ M3.scal 4 := by
  intro h
  apply hS1
  apply Subtype.ext
  rw [scaledIcosahedralGroup_one_coe, ← repM3_toMatrix, h, M3.toMatrix_scal]

theorem sq_one_of_repM3 {S : scaledIcosahedralRotations}
    (h : (repM3 S).mul (repM3 S) = M3.scal 16) : S * S = 1 := by
  rw [scaledIcosahedralRotations_mul_def, scaledMul_eq_iff, scaledIcosahedralGroup_one_coe,
    smul_smul, ← repM3_toMatrix, ← M3.toMatrix_mul, h, M3.toMatrix_scal]
  norm_num

theorem ne_one_of_repM3 {S : scaledIcosahedralRotations} (h : repM3 S ≠ M3.scal 4) :
    S ≠ 1 := by
  intro h1
  apply h
  apply M3.toMatrix_injective
  rw [repM3_toMatrix, h1, scaledIcosahedralGroup_one_coe, M3.toMatrix_scal]

theorem coe_eq_realQuarter_repM3 (g : icosahedralRotationGroup) :
    ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) =
      realQuarter (repM3 (scaledIcosahedralMulEquiv.symm g)).toMatrix := by
  rw [repM3_toMatrix]
  conv_lhs => rw [← scaledIcosahedralMulEquiv.apply_symm_apply g]
  rfl

theorem repM3_mem_scaledInvolutions {g : icosahedralRotationGroup} (hg1 : g ≠ 1)
    (hg2 : g * g = 1) : repM3 (scaledIcosahedralMulEquiv.symm g) ∈ scaledInvolutions := by
  have hS2 : scaledIcosahedralMulEquiv.symm g * scaledIcosahedralMulEquiv.symm g = 1 := by
    rw [← map_mul, hg2, map_one]
  have hS1 : scaledIcosahedralMulEquiv.symm g ≠ 1 := by
    intro h
    apply hg1
    rw [← scaledIcosahedralMulEquiv.apply_symm_apply g, h, map_one]
  exact mem_scaledInvolutions.mpr ⟨repM3_mem _, repM3_ne_of_ne_one hS1, repM3_mul_self_of_sq hS2⟩

/-- Real fixing of `halveToReal x` is scaled fixing of `x`. -/
theorem fixes_halve_iff (g : icosahedralRotationGroup) (x : Fin 3 → Zsqrt5) :
    ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ halveToReal x =
        halveToReal x ↔
      (repM3 (scaledIcosahedralMulEquiv.symm g)).mulVec x = (4 : Zsqrt5) • x := by
  rw [coe_eq_realQuarter_repM3, realQuarter_mulVec_halveToReal_iff, M3.toMatrix_mulVec]

/-- Two official edge vectors fixed by the same involution agree up to sign (one sign-pair). -/
theorem involution_fixed_edgeVector_unique (g : icosahedralRotationGroup) (hg1 : g ≠ 1)
    (hg2 : g * g = 1) {p q : Fin 3 → ℝ} (hp : p ∈ officialEdgeVectors)
    (hq : q ∈ officialEdgeVectors)
    (hgp : ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ p = p)
    (hgq : ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ q = q) :
    q = p ∨ q = -p := by
  rw [officialEdgeVectors_eq_image] at hp hq
  obtain ⟨x, hx, rfl⟩ := hp
  obtain ⟨y, hy, rfl⟩ := hq
  rw [fixes_halve_iff] at hgp hgq
  rcases scaledInvolution_fixed_unique _ (repM3_mem_scaledInvolutions hg1 hg2) x hx y hy hgp hgq
    with h | h
  · left; rw [h]
  · right; rw [h, halveToReal_neg]

/-- Two involutions fixing the same official edge vector are equal. -/
theorem involution_unique_of_fixes (g h : icosahedralRotationGroup) (hg1 : g ≠ 1)
    (hg2 : g * g = 1) (hh1 : h ≠ 1) (hh2 : h * h = 1) {p : Fin 3 → ℝ}
    (hp : p ∈ officialEdgeVectors)
    (hgp : ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ p = p)
    (hhp : ((h : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ p = p) :
    g = h := by
  rw [officialEdgeVectors_eq_image] at hp
  obtain ⟨x, hx, rfl⟩ := hp
  rw [fixes_halve_iff] at hgp hhp
  have hAB := scaledInvolution_unique_of_fixed _ (repM3_mem_scaledInvolutions hg1 hg2) _
    (repM3_mem_scaledInvolutions hh1 hh2) x hx hgp hhp
  have hS : scaledIcosahedralMulEquiv.symm g = scaledIcosahedralMulEquiv.symm h := by
    apply Subtype.ext
    rw [← repM3_toMatrix, ← repM3_toMatrix, hAB]
  exact scaledIcosahedralMulEquiv.symm.injective hS

theorem natCard_mem_list {α : Type*} [DecidableEq α] (l : List α) (hl : l.Nodup) :
    Nat.card {a // a ∈ l} = l.length := by
  have h : {a | a ∈ l} = ((l.toFinset : Finset α) : Set α) := by ext; simp
  rw [show Nat.card {a // a ∈ l} = Nat.card ↥{a | a ∈ l} from rfl, Nat.card_coe_set_eq, h,
    Set.ncard_coe_finset, List.toFinset_card_of_nodup hl]

/-- The map from the official group's involutions to the 15 scaled involutions. -/
noncomputable def involutionToScaled :
    {g : icosahedralRotationGroup // g ≠ 1 ∧ g * g = 1} → {A : M3 // A ∈ scaledInvolutions} :=
  fun g => ⟨repM3 (scaledIcosahedralMulEquiv.symm g.1),
    repM3_mem_scaledInvolutions g.2.1 g.2.2⟩

theorem involutionToScaled_bijective : Function.Bijective involutionToScaled := by
  constructor
  · rintro ⟨g, hg⟩ ⟨h, hh⟩ hgh
    have hA : repM3 (scaledIcosahedralMulEquiv.symm g) = repM3 (scaledIcosahedralMulEquiv.symm h) :=
      congrArg Subtype.val hgh
    have hS : scaledIcosahedralMulEquiv.symm g = scaledIcosahedralMulEquiv.symm h := by
      apply Subtype.ext
      rw [← repM3_toMatrix, ← repM3_toMatrix, hA]
    exact Subtype.ext (scaledIcosahedralMulEquiv.symm.injective hS)
  · rintro ⟨A, hA⟩
    obtain ⟨hAL, hA4, hA16⟩ := mem_scaledInvolutions.mp hA
    let S : scaledIcosahedralRotations :=
      ⟨A.toMatrix, mem_scaledIcosahedralRotations.mpr ⟨A, hAL, rfl⟩⟩
    have hrep : repM3 S = A := by
      apply M3.toMatrix_injective
      rw [repM3_toMatrix]
    have hS2 : S * S = 1 := sq_one_of_repM3 (by rw [hrep]; exact hA16)
    have hS1 : S ≠ 1 := ne_one_of_repM3 (by rw [hrep]; exact hA4)
    refine ⟨⟨scaledIcosahedralMulEquiv S, ?_, ?_⟩, ?_⟩
    · intro h
      exact hS1 (scaledIcosahedralMulEquiv.injective (h.trans (map_one _).symm))
    · rw [← map_mul, hS2, map_one]
    · apply Subtype.ext
      change repM3 (scaledIcosahedralMulEquiv.symm (scaledIcosahedralMulEquiv S)) = A
      rw [MulEquiv.symm_apply_apply, hrep]

/-- The imported official group has exactly 15 elements `g ≠ 1` with `g * g = 1`. -/
theorem natCard_involutions :
    Nat.card {g : icosahedralRotationGroup // g ≠ 1 ∧ g * g = 1} = 15 := by
  rw [Nat.card_eq_of_bijective _ involutionToScaled_bijective,
    natCard_mem_list _ scaledInvolutions_nodup, scaledInvolutions_length]

theorem mulVec_neg_fix {M : Matrix (Fin 3) (Fin 3) ℝ} {p : Fin 3 → ℝ} (h : M *ᵥ p = p) :
    M *ᵥ (-p) = -p := by
  rw [Matrix.mulVec_neg, h]

/-- Bijection from involutions to edge sign-pairs: each involution is sent to the sign-pair
`{p, -p}` whose points it fixes. -/
theorem involution_line_bijection :
    ∃ f : {g : icosahedralRotationGroup // g ≠ 1 ∧ g * g = 1} → officialEdgeLines,
      Function.Bijective f ∧ ∀ g, ∀ p ∈ (f g : Set (Fin 3 → ℝ)),
        ((g.1 : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ p = p := by
  have hex := fun g : {g : icosahedralRotationGroup // g ≠ 1 ∧ g * g = 1} =>
    icosahedralRotationGroup_involution_fixes_edgeVector g.1 g.2.1 g.2.2
  choose pt hptE hptF using hex
  let f : {g : icosahedralRotationGroup // g ≠ 1 ∧ g * g = 1} → officialEdgeLines :=
    fun g => ⟨{pt g, -pt g}, pt g, hptE g, rfl⟩
  have hfix : ∀ g, ∀ p ∈ (f g : Set (Fin 3 → ℝ)),
      ((g.1 : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ p = p := by
    intro g p hp
    rcases hp with rfl | hp
    · exact hptF g
    · rw [Set.mem_singleton_iff] at hp
      rw [hp]
      exact mulVec_neg_fix (hptF g)
  refine ⟨f, ⟨?_, ?_⟩, hfix⟩
  · intro g h hgh
    have hmem : pt g ∈ (f h : Set (Fin 3 → ℝ)) := by
      rw [← hgh]; exact Set.mem_insert _ _
    exact Subtype.ext (involution_unique_of_fixes g.1 h.1 g.2.1 g.2.2 h.2.1 h.2.2 (hptE g)
      (hptF g) (hfix h _ hmem))
  · rintro ⟨L, p, hp, rfl⟩
    obtain ⟨g, hg1, hg2, hgp⟩ := officialEdgeVectors_fixed_by_involution p hp
    refine ⟨⟨g, hg1, hg2⟩, Subtype.ext ?_⟩
    change ({pt ⟨g, hg1, hg2⟩, -pt ⟨g, hg1, hg2⟩} : Set (Fin 3 → ℝ)) = {p, -p}
    rcases involution_fixed_edgeVector_unique g hg1 hg2 (hptE ⟨g, hg1, hg2⟩) hp
      (hptF ⟨g, hg1, hg2⟩) hgp with h | h
    · rw [h]
    · rw [h, neg_neg, Set.pair_comm]

#print axioms faceSums_length
#print axioms cubeOfFrame_length
#print axioms faceSums_mem_two_cubes
#print axioms cubeOfFrame_edges_parallel_frame
#print axioms frame_parallel_cubeOfFrame_edge
#print axioms cubeOfFrame_edges_parallel_frame_unique
#print axioms isCubeSet_iff
#print axioms cubeSets_ncard
#print axioms officialFaceSums_ncard
#print axioms officialCube_eq_image
#print axioms officialCube_ncard
#print axioms isOfficialCube_iff
#print axioms officialCubeSets_ncard
#print axioms officialCube_edges_parallel_frame
#print axioms involution_fixed_edgeVector_unique
#print axioms involution_unique_of_fixes
#print axioms natCard_involutions
#print axioms involution_line_bijection
