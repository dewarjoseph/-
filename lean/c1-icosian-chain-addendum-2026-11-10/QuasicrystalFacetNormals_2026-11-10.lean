/-
  QuasicrystalFacetNormals_2026-11-10.lean (scratch, 2026-11-10; not peer reviewed)

  Uniqueness of the 15 'facet normals' built by `Zonotope.__init__` (`qc/cutproject.py`, sha256
  84663d07…) from the rows of
  `perp`. The 15 crosses `perp_i ⨯₃ perp_j` (i < j) are nonzero, and distinct pairs give normalised
  crosses with |u·w| ≠ 1, so the 1e-12 / 1e-9 filters keep all 15 and the ±u are 30 distinct vectors.
  Exact checks over ℤ[√5] (`decide +kernel`) on `icoWc`, transferred through `icoPerp_eq'`.
  'Facet normal' here means exactly the normals that constructor computes. That they are the
  facet normals of a polytope, and any triacontahedron reading, is not proved in Lean.
  Statement text was frozen before proving.
  Imports `QuasicrystalCutProject6D_2026-11-10` unchanged.
-/
import «QuasicrystalCutProject6D_2026-11-10»
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Matrix.DotProduct

open Equiv Matrix

/-- Index pairs `i < j` of the six generators (the `itertools.combinations(range(6), 2)` loop). -/
abbrev FacetPair := {p : Fin 6 × Fin 6 // p.1 < p.2}

/-- Exact cross product of the unnormalised internal rows `icoWc i = 2 (A + (1 − τ) B)_i`. -/
def facetNormalZ (p : FacetPair) : Fin 3 → Zsqrt5 := icoWc p.1.1 ⨯₃ icoWc p.1.2

/-- `u = g_i × g_j` with `g = perp` (the rows of `icoPerp`), as in `Zonotope.__init__`. -/
noncomputable def facetNormal (p : FacetPair) : Fin 3 → ℝ := icoPerp p.1.1 ⨯₃ icoPerp p.1.2

/-- `u / ‖u‖`. -/
noncomputable def unitFacetNormal (p : FacetPair) : Fin 3 → ℝ :=
  (Real.sqrt (facetNormal p ⬝ᵥ facetNormal p))⁻¹ • facetNormal p

/-! ## Exact checks over `ℤ[√5]` -/

theorem facetPair_card : Fintype.card FacetPair = 15 := by decide +kernel

theorem facetNormalZ_ne_zero : ∀ p : FacetPair, facetNormalZ p ≠ 0 := by
  simp only [facetNormalZ, cross_apply]; decide +kernel

theorem facetNormalZ_cross_ne_zero : ∀ p q : FacetPair, p ≠ q → facetNormalZ p ⨯₃ facetNormalZ q ≠ 0 := by
  simp only [facetNormalZ, cross_apply]; decide +kernel

/-! ## Transfer -/

theorem map_cross (f : Zsqrt5 →+* ℝ) (a b : Fin 3 → Zsqrt5) :
    (fun k => f ((a ⨯₃ b) k)) = (fun k => f (a k)) ⨯₃ (fun k => f (b k)) := by
  ext k; fin_cases k <;> simp [cross_apply]

theorem dot_self_nonneg (v : Fin 3 → ℝ) : 0 ≤ v ⬝ᵥ v := by
  simp only [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

theorem dot_self_pos {v : Fin 3 → ℝ} (h : v ≠ 0) : 0 < v ⬝ᵥ v :=
  lt_of_le_of_ne (dot_self_nonneg v) (fun h0 => h (dotProduct_self_eq_zero.mp h0.symm))

theorem realZ_ne_zero {x : Fin 3 → Zsqrt5} (h : x ≠ 0) : (fun k => zsqrt5ToReal (x k)) ≠ 0 := by
  intro h0
  apply h
  apply zsqrt5ToReal_vec_injective
  show (fun k => zsqrt5ToReal (x k)) = fun k => zsqrt5ToReal ((0 : Fin 3 → Zsqrt5) k)
  rw [h0]; ext k; simp

theorem icoPerp_row (i : Fin 6) :
    icoPerp i = (Real.sqrt (20 - 4 * Real.sqrt 5))⁻¹ • fun k => zsqrt5ToReal (icoWc i k) := by
  ext k; rw [icoPerp_eq']; rfl

theorem facetNormal_eq_smul (p : FacetPair) :
    facetNormal p = (20 - 4 * Real.sqrt 5)⁻¹ • fun k => zsqrt5ToReal (facetNormalZ p k) := by
  rw [facetNormal, icoPerp_row, icoPerp_row, facetNormalZ, map_cross, LinearMap.map_smul₂,
    LinearMap.map_smul, smul_smul, ← mul_inv, Real.mul_self_sqrt nPerp_pos.le]

theorem facetNormal_ne_zero (p : FacetPair) : facetNormal p ≠ 0 := by
  rw [facetNormal_eq_smul]
  exact smul_ne_zero (inv_ne_zero nPerp_pos.ne') (realZ_ne_zero (facetNormalZ_ne_zero p))

theorem facetNormal_cross_eq_zero_iff (p q : FacetPair) :
    facetNormal p ⨯₃ facetNormal q = 0 ↔ p = q := by
  constructor
  · intro h
    by_contra hpq
    rw [facetNormal_eq_smul, facetNormal_eq_smul, LinearMap.map_smul₂, LinearMap.map_smul,
      ← map_cross] at h
    exact smul_ne_zero (inv_ne_zero nPerp_pos.ne') (smul_ne_zero (inv_ne_zero nPerp_pos.ne')
      (realZ_ne_zero (facetNormalZ_cross_ne_zero p q hpq))) h
  · rintro rfl; exact cross_self _

theorem facetNormal_parallel_iff (p q : FacetPair) :
    (∃ c : ℝ, facetNormal p = c • facetNormal q) ↔ p = q := by
  constructor
  · rintro ⟨c, hc⟩
    rw [← facetNormal_cross_eq_zero_iff, hc, LinearMap.map_smul₂, cross_self, smul_zero]
  · rintro rfl; exact ⟨1, (one_smul ℝ _).symm⟩

theorem unitFacetNormal_dot_self (p : FacetPair) : unitFacetNormal p ⬝ᵥ unitFacetNormal p = 1 := by
  have hpos := dot_self_pos (facetNormal_ne_zero p)
  rw [unitFacetNormal, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
    ← mul_inv, Real.mul_self_sqrt hpos.le, inv_mul_cancel₀ hpos.ne']

theorem abs_dot_unitFacetNormal_eq_one_iff (p q : FacetPair) :
    |unitFacetNormal p ⬝ᵥ unitFacetNormal q| = 1 ↔ p = q := by
  set a := facetNormal p
  set b := facetNormal q
  have ha : 0 < a ⬝ᵥ a := dot_self_pos (facetNormal_ne_zero p)
  have hb : 0 < b ⬝ᵥ b := dot_self_pos (facetNormal_ne_zero q)
  have hL := cross_dot_cross a b a b
  have hx : unitFacetNormal p ⬝ᵥ unitFacetNormal q =
      (Real.sqrt (a ⬝ᵥ a))⁻¹ * (Real.sqrt (b ⬝ᵥ b))⁻¹ * (a ⬝ᵥ b) := by
    rw [unitFacetNormal, unitFacetNormal, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    ring
  have hsq : (unitFacetNormal p ⬝ᵥ unitFacetNormal q) ^ 2 * ((a ⬝ᵥ a) * (b ⬝ᵥ b)) = (a ⬝ᵥ b) ^ 2 := by
    rw [hx, mul_pow, mul_pow, inv_pow, inv_pow, Real.sq_sqrt ha.le, Real.sq_sqrt hb.le]
    field_simp
  have habs : |unitFacetNormal p ⬝ᵥ unitFacetNormal q| = 1 ↔
      (unitFacetNormal p ⬝ᵥ unitFacetNormal q) ^ 2 = 1 := by
    rw [← sq_abs]
    constructor
    · intro h; rw [h, one_pow]
    · intro h
      have h0 := abs_nonneg (unitFacetNormal p ⬝ᵥ unitFacetNormal q)
      nlinarith
  rw [habs, ← facetNormal_cross_eq_zero_iff, ← dotProduct_self_eq_zero, hL, dotProduct_comm b a]
  have hab : 0 < (a ⬝ᵥ a) * (b ⬝ᵥ b) := mul_pos ha hb
  constructor
  · intro h; rw [h, one_mul] at hsq; nlinarith
  · intro h
    have e : (a ⬝ᵥ b) ^ 2 = (a ⬝ᵥ a) * (b ⬝ᵥ b) := by nlinarith
    rw [e] at hsq
    have := mul_right_cancel₀ hab.ne' (hsq.trans (one_mul _).symm)
    exact this

theorem signedUnitFacetNormal_injective :
    Function.Injective (fun x : FacetPair × Bool => (if x.2 then (1 : ℝ) else -1) • unitFacetNormal x.1) := by
  rintro ⟨p, s⟩ ⟨q, t⟩ h
  simp only at h
  have hs : ∀ b : Bool, (if b then (1 : ℝ) else -1) ^ 2 = 1 := by intro b; cases b <;> norm_num
  have hd := congrArg (fun v => ((if s then (1 : ℝ) else -1) • unitFacetNormal p) ⬝ᵥ v) h
  simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul, unitFacetNormal_dot_self] at hd
  have hpq : p = q := by
    rw [← abs_dot_unitFacetNormal_eq_one_iff, abs_eq zero_le_one]
    cases s <;> cases t <;> norm_num at hd <;> first | (left; linarith) | (right; linarith)
  subst hpq
  have hdd := congrArg (fun v => unitFacetNormal p ⬝ᵥ v) h
  simp only [dotProduct_smul, smul_eq_mul, unitFacetNormal_dot_self, mul_one] at hdd
  cases s <;> cases t <;> first | rfl | (exfalso; norm_num at hdd)

theorem ncard_signedUnitFacetNormals :
    (Set.range (fun x : FacetPair × Bool => (if x.2 then (1 : ℝ) else -1) • unitFacetNormal x.1)).ncard = 30 := by
  rw [Set.ncard_range_of_injective signedUnitFacetNormal_injective, Nat.card_eq_fintype_card,
    Fintype.card_prod, facetPair_card, Fintype.card_bool]

#print axioms facetPair_card
#print axioms facetNormalZ_ne_zero
#print axioms facetNormalZ_cross_ne_zero
#print axioms facetNormal_eq_smul
#print axioms facetNormal_ne_zero
#print axioms facetNormal_cross_eq_zero_iff
#print axioms facetNormal_parallel_iff
#print axioms unitFacetNormal_dot_self
#print axioms abs_dot_unitFacetNormal_eq_one_iff
#print axioms signedUnitFacetNormal_injective
#print axioms ncard_signedUnitFacetNormals
