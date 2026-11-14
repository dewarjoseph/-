/-
Scratch file, dated 2026-11-10. Not a Lake target. Not peer reviewed.

Element orders and conjugacy classes of the official group.
Statement text was frozen before proving.
Imports `IcosahedralAbstractions_2026-11-10` (src dc045da6…) unchanged. No existing file is
edited.

Proved: every element has order 1, 2, 3 or 5, with 1, 15, 20, 24 elements of each order; the
conjugacy class of `g` has 1, 15, 20, 12 elements according as its order is 1, 2, 3, 5; every
`g` is conjugate to `g⁻¹`; for `g` of order 5, `g` and `g ^ 2` are not conjugate; there are
exactly five conjugacy classes, and a bijection `Fin 5 ≃ ConjClasses` sends `i` to a class
with `![1, 15, 20, 12, 12] i` elements. Method: orders and conjugacy are read through the
injective hom `toPermHom` (σ, the table-defined isomorphism) and checked by `decide +kernel`
on the table `framePermList`. The tables `orderTable` and the representative positions were
read off a throwaway `#eval` and are re-checked here.

Not proved: characters, irreducible representations, or which size-12 class contains which
rotation angle.
-/

import «IcosahedralAbstractions_2026-11-10»
open Equiv Matrix

noncomputable def toPermHom : icosahedralRotationGroup →* Perm (Fin 5) :=
  (alternatingGroup (Fin 5)).subtype.comp icosahedralRotationGroupMulEquivAlternatingGroup.toMonoidHom

theorem toPermHom_apply (g : icosahedralRotationGroup) : toPermHom g = toPerm g := rfl

theorem orderOf_toPerm (g : icosahedralRotationGroup) : orderOf (toPerm g) = orderOf g :=
  orderOf_injective toPermHom toPerm_injective g

def orderTable : List ℕ :=
  [1, 2, 2, 2, 3, 2, 3, 3, 2, 3, 2, 2, 5, 2, 5, 5, 2, 5, 2, 2, 5, 2, 5, 5, 2, 5, 2, 3, 3, 3, 3, 3, 3, 3, 3, 5, 3, 5, 3, 3, 5, 3, 5, 3, 5, 3, 5, 5, 3, 5, 3, 5, 5, 5, 5, 5, 5, 5, 5, 2]

def ordFn (p : Perm (Fin 5)) : ℕ := ((framePermList.zip orderTable).lookup p).getD 0

theorem table_order : ∀ p ∈ framePermList,
    0 < ordFn p ∧ p ^ ordFn p = 1 ∧ ∀ m < ordFn p, 0 < m → p ^ m ≠ 1 := by decide +kernel

theorem map_ordFn : framePermList.map ordFn = orderTable := by decide +kernel

theorem orderOf_eq_ordFn (g : icosahedralRotationGroup) : orderOf g = ordFn (toPerm g) := by
  obtain ⟨h0, h1, h2⟩ := table_order _ (toPerm_mem g)
  rw [← orderOf_toPerm]
  exact (orderOf_eq_iff h0).mpr ⟨h1, h2⟩

theorem ordFn_mem_orderTable (g : icosahedralRotationGroup) : ordFn (toPerm g) ∈ orderTable := by
  rw [← map_ordFn]; exact List.mem_map_of_mem (toPerm_mem g)

theorem orderOf_cases (g : icosahedralRotationGroup) :
    orderOf g = 1 ∨ orderOf g = 2 ∨ orderOf g = 3 ∨ orderOf g = 5 := by
  have key : ∀ n ∈ orderTable, n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 5 := by decide
  rw [orderOf_eq_ordFn]
  exact key _ (ordFn_mem_orderTable g)

theorem natCard_orderOf_eq (n : ℕ) :
    Nat.card {g : icosahedralRotationGroup // orderOf g = n} = orderTable.count n := by
  simp only [orderOf_eq_ordFn]
  rw [natCard_filter_of_bijOn_list toPerm _ framePermList_nodup toPerm_mem toPerm_injective
    toPerm_surj (fun q => ordFn q = n), length_filter_eq_count_map, map_ordFn]

theorem orderOf_counts :
    Nat.card {g : icosahedralRotationGroup // orderOf g = 1} = 1 ∧
    Nat.card {g : icosahedralRotationGroup // orderOf g = 2} = 15 ∧
    Nat.card {g : icosahedralRotationGroup // orderOf g = 3} = 20 ∧
    Nat.card {g : icosahedralRotationGroup // orderOf g = 5} = 24 := by
  simp only [natCard_orderOf_eq]
  decide

theorem pair_mem_zip (g : icosahedralRotationGroup) :
    (ordFn (toPerm g), classSize (toPerm g)) ∈ orderTable.zip classSizeTable := by
  rw [← map_ordFn, ← classSize_table, List.zip_map']
  exact List.mem_map_of_mem (f := fun a => (ordFn a, classSize a)) (toPerm_mem g)

theorem conjClass_card_of_orderOf (g : icosahedralRotationGroup) :
    (orderOf g = 1 → Nat.card {h : icosahedralRotationGroup // IsConj g h} = 1) ∧
    (orderOf g = 2 → Nat.card {h : icosahedralRotationGroup // IsConj g h} = 15) ∧
    (orderOf g = 3 → Nat.card {h : icosahedralRotationGroup // IsConj g h} = 20) ∧
    (orderOf g = 5 → Nat.card {h : icosahedralRotationGroup // IsConj g h} = 12) := by
  have key : ∀ x ∈ orderTable.zip classSizeTable, (x.1 = 1 → x.2 = 1) ∧ (x.1 = 2 → x.2 = 15) ∧
      (x.1 = 3 → x.2 = 20) ∧ (x.1 = 5 → x.2 = 12) := by decide
  rw [natCard_conj, orderOf_eq_ordFn]
  exact key _ (pair_mem_zip g)

theorem table_conj_inv : ∀ p ∈ framePermList, conjB p p⁻¹ = true := by decide +kernel

theorem table_not_conj_sq : ∀ p ∈ framePermList, ordFn p = 5 → conjB p (p ^ 2) = false := by
  decide +kernel

theorem isConj_inv_self (g : icosahedralRotationGroup) : IsConj g g⁻¹ := by
  rw [isConj_iff_conjB, ← toPermHom_apply, ← toPermHom_apply, map_inv]
  exact table_conj_inv _ (toPerm_mem g)

theorem not_isConj_sq_of_orderOf_eq_five (g : icosahedralRotationGroup) (hg : orderOf g = 5) :
    ¬ IsConj g (g ^ 2) := by
  rw [isConj_iff_conjB, ← toPermHom_apply, ← toPermHom_apply, map_pow, toPermHom_apply]
  rw [orderOf_eq_ordFn] at hg
  rw [table_not_conj_sq _ (toPerm_mem g) hg]
  decide

/-! ### The five conjugacy classes -/

def repIndex : Fin 5 → ℕ := ![0, 1, 4, 12, 20]

def repPerm (i : Fin 5) : Perm (Fin 5) := framePermList.getD (repIndex i) 1

theorem repPerm_mem : ∀ i : Fin 5, repPerm i ∈ framePermList := by decide +kernel

theorem reps_distinct : ∀ i j : Fin 5, conjB (repPerm i) (repPerm j) = true → i = j := by
  decide +kernel

theorem reps_cover : ∀ p ∈ framePermList, ∃ i : Fin 5, conjB (repPerm i) p = true := by
  decide +kernel

theorem reps_classSize : ∀ i : Fin 5, classSize (repPerm i) = (![1, 15, 20, 12, 12] : Fin 5 → ℕ) i := by
  decide +kernel

noncomputable def repI (i : Fin 5) : icosahedralRotationGroup :=
  Classical.choose (toPerm_surj _ (repPerm_mem i))

theorem toPerm_repI (i : Fin 5) : toPerm (repI i) = repPerm i :=
  Classical.choose_spec (toPerm_surj _ (repPerm_mem i))

noncomputable def classMap (i : Fin 5) : ConjClasses icosahedralRotationGroup :=
  ConjClasses.mk (repI i)

theorem classMap_bijective : Function.Bijective classMap := by
  constructor
  · intro i j hij
    have h := (ConjClasses.mk_eq_mk_iff_isConj).mp hij
    rw [isConj_iff_conjB, toPerm_repI, toPerm_repI] at h
    exact reps_distinct i j h
  · intro c
    obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
    obtain ⟨i, hi⟩ := reps_cover _ (toPerm_mem g)
    refine ⟨i, (ConjClasses.mk_eq_mk_iff_isConj).mpr ?_⟩
    rw [isConj_iff_conjB, toPerm_repI]
    exact hi

theorem conjClasses_natCard : Nat.card (ConjClasses icosahedralRotationGroup) = 5 := by
  rw [← Nat.card_eq_of_bijective classMap classMap_bijective, Nat.card_eq_fintype_card,
    Fintype.card_fin]

theorem natCard_carrier_mk (g : icosahedralRotationGroup) :
    Nat.card (ConjClasses.mk g).carrier = Nat.card {h : icosahedralRotationGroup // IsConj g h} := by
  have hset : (ConjClasses.mk g).carrier = {h | IsConj g h} := by
    ext h
    rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj, Set.mem_ofPred_eq,
      isConj_comm]
  rw [hset]
  rfl

theorem conjClasses_sizes : ∃ e : Fin 5 ≃ ConjClasses icosahedralRotationGroup,
    ∀ i : Fin 5, Nat.card (e i).carrier = (![1, 15, 20, 12, 12] : Fin 5 → ℕ) i := by
  refine ⟨Equiv.ofBijective classMap classMap_bijective, fun i => ?_⟩
  rw [Equiv.ofBijective_apply, classMap, natCard_carrier_mk, natCard_conj, toPerm_repI]
  exact reps_classSize i

#print axioms toPermHom
#print axioms orderOf_toPerm
#print axioms table_order
#print axioms map_ordFn
#print axioms orderOf_eq_ordFn
#print axioms orderOf_cases
#print axioms orderOf_counts
#print axioms conjClass_card_of_orderOf
#print axioms isConj_inv_self
#print axioms not_isConj_sq_of_orderOf_eq_five
#print axioms classMap_bijective
#print axioms conjClasses_natCard
#print axioms conjClasses_sizes
