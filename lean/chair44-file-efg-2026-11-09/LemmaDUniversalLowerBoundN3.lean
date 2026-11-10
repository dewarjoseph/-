import LeanLab.Scratch.LemmaDGeneralLowerBound
import LeanLab.Scratch.LemmaDL1SevenClassification
import LeanLab.Scratch.LemmaDOrbitNoZero
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# A uniform lower bound ‖F‖ ≥ 1/N³ at any integer q with F ≠ 0 (scratch)

**[P, Lean]** For every integer wavevector `qZ : Fin 3 → ℤ`, every `N ≥ 1`,
and every equal-weight D-form box, if `F ≠ 0` then `‖F‖ ≥ 1/N³` (and
`|F|² ≥ 1/N⁶`). This sharpens the cyclotomic-resultant bound
`‖F‖ ≥ 1/N⁶` of LemmaDGeneralLowerBound by using that the six embeddings
of `ℚ(ζ₇)` come in three complex-conjugate pairs.

The argument reuses that file's phase polynomial `P ∈ ℤ[X]` with
`S = N·F = P(ζ₇)`, the identity `|Res(Φ₇, P)| = |∏_{j=1}^6 P(ζ₇^j)|`,
and `|P(α)| ≤ N` at every primitive seventh root `α`. Because `P` has
integer (hence real) coefficients, `P(conj α) = conj (P(α))`, so the
six factors pair as three squares. One pair is `|S|²`; the other four
factors are `≤ N`, and the nonzero integer resultant gives
`|S|² N⁴ ≥ 1`, hence `|S| ≥ 1/N²` and `‖F‖ ≥ 1/N³`.

Corollaries record the bound at the fifteen two- and three-pair
representatives (using the classification's non-vanishing) and on
each of those full signed-permutation orbits. The general statement
already applies to every integer orbit element: if `F ≠ 0` at that
integer `q`, the same `1/N³` bound holds.

The exponent 3 is what this method gives, not claimed sharp. Infima
stay `[X]`. Specialised cubic constants `c0/N³` at the one-pair
representatives (LemmaDLowerBound220/330Sharper/L1SevenCubic) remain
the sharper statements there.

D-form class only. Scratch; not a Lake target; not peer reviewed.
Licenses nothing about ETH (false stays `[X]`), R2/R4/R5,
ScaleLiftToRAM, PrimToRAM, CH-V-020, or Theorem F.

Dated 2026-11-09.
-/

namespace LeanLab.Scratch.LemmaDUniversalLowerBoundN3

open Complex Polynomial Finset ComplexConjugate Equiv
open LeanLab.Scratch.LemmaD4 (dot3 structureFactor centroidPoint)
open LeanLab.Scratch.LemmaDIntVec (qReal zeta7 isPrimitiveRoot_zeta7)
open LeanLab.Scratch.LemmaDGeneralLowerBound
open LeanLab.Scratch.LemmaDL1SevenClassification
open LeanLab.Scratch.LemmaDOrbitNoZero
  (orbitQ structureFactor_ne_zero_orbit_transfer)

lemma zeta7_pow_seven : zeta7 ^ 7 = 1 :=
  isPrimitiveRoot_zeta7.pow_eq_one

lemma zeta7_mul_pow_six : zeta7 * zeta7 ^ 6 = 1 := by
  rw [← pow_succ', zeta7_pow_seven]

lemma conj_zeta7_eq_pow_six : conj zeta7 = zeta7 ^ 6 := by
  have hnorm : ‖zeta7‖ = 1 :=
    primitive_root_norm_one isPrimitiveRoot_zeta7
  have hmul : zeta7 * conj zeta7 = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]
    simp
  have : conj zeta7 = zeta7⁻¹ :=
    (inv_eq_of_mul_eq_one_right hmul).symm
  have hinv : zeta7 ^ 6 = zeta7⁻¹ :=
    (inv_eq_of_mul_eq_one_right zeta7_mul_pow_six).symm
  rw [this, hinv]

lemma isPrimitiveRoot_conj_zeta7 : IsPrimitiveRoot (conj zeta7) 7 := by
  rw [conj_zeta7_eq_pow_six]
  exact isPrimitiveRoot_zeta7.pow_of_coprime 6 (by decide)

lemma zeta7_ne_conj : zeta7 ≠ conj zeta7 := by
  intro h
  have him0 : zeta7.im = 0 := Complex.conj_eq_iff_im.mp h.symm
  have hform : (2 * Real.pi * I / 7 : ℂ) = (2 * Real.pi / 7 : ℝ) * I := by
    push_cast
    ring
  have him : zeta7.im = Real.sin (2 * Real.pi / 7) := by
    unfold zeta7
    rw [hform, Complex.exp_ofReal_mul_I_im]
  have hpos : 0 < Real.sin (2 * Real.pi / 7) := by
    refine Real.sin_pos_of_pos_of_lt_pi ?_ ?_
    · positivity
    · have : (2 : ℝ) / 7 < 1 := by norm_num
      nlinarith [Real.pi_pos]
  linarith

lemma eval_map_int_conj (P : ℤ[X]) (α : ℂ) :
    eval (conj α) (P.map (Int.castRingHom ℂ)) =
      conj (eval α (P.map (Int.castRingHom ℂ))) := by
  let Pℝ : ℝ[X] := P.map (Int.castRingHom ℝ)
  have hcomp : (algebraMap ℝ ℂ).comp (Int.castRingHom ℝ) = Int.castRingHom ℂ := by
    ext
    simp
  have hmap : Pℝ.map (algebraMap ℝ ℂ) = P.map (Int.castRingHom ℂ) := by
    simp only [Pℝ]
    rw [Polynomial.map_map, hcomp]
  have hconj : aeval (conj α) Pℝ = conj (aeval α Pℝ) := aeval_conj Pℝ α
  have hL : aeval (conj α) Pℝ = eval (conj α) (P.map (Int.castRingHom ℂ)) := by
    rw [aeval_def, ← eval_map, hmap]
  have hR : aeval α Pℝ = eval α (P.map (Int.castRingHom ℂ)) := by
    rw [aeval_def, ← eval_map, hmap]
  rw [← hL, hconj, hR]

/-- Conjugate pairing: `|Res(Φ₇,P)| = |S|² · |P(ζ₂)|² · |P(ζ₃)|²` is used
in the form `|∏ P(α)| = |S|² · (product of the other four factors)`. -/
lemma abs_resultant_phasePoly_conj {N : ℕ}
    (s : Fin N → Fin 3 → ℤ) (q : Fin 3 → ℤ)
    (hS : eval zeta7 ((phasePoly s q).map (Int.castRingHom ℂ)) ≠ 0) :
    1 ≤ ‖eval zeta7 ((phasePoly s q).map (Int.castRingHom ℂ))‖ ^ 2 *
      (N : ℝ) ^ 4 := by
  set P := phasePoly s q
  set Pℂ := P.map (Int.castRingHom ℂ)
  set ΦZ := cyclotomic 7 ℤ
  set ΦC := cyclotomic 7 ℂ
  set φ : ℤ →+* ℂ := Int.castRingHom ℂ
  have hmapΦ : ΦC = ΦZ.map φ := (map_cyclotomic_int 7 ℂ).symm
  have hdegP : Pℂ.natDegree = P.natDegree :=
    natDegree_map_eq_of_injective int_castHom_complex_injective P
  have hdegΦmap : (ΦZ.map φ).natDegree = ΦZ.natDegree :=
    natDegree_map_eq_of_injective int_castHom_complex_injective ΦZ
  have hres :
      resultant (ΦZ.map φ) Pℂ ΦZ.natDegree P.natDegree =
        φ (resultant ΦZ P ΦZ.natDegree P.natDegree) :=
    resultant_map_map (f := ΦZ) (g := P) (m := ΦZ.natDegree) (n := P.natDegree)
      (φ := φ)
  have hprod :
      resultant ΦC Pℂ ΦC.natDegree Pℂ.natDegree =
        ΦC.leadingCoeff ^ Pℂ.natDegree *
          (ΦC.roots.map (fun α => eval α Pℂ)).prod :=
    resultant_eq_prod_eval ΦC Pℂ Pℂ.natDegree le_rfl cyclotomic7_complex_splits
  have hlead : ΦC.leadingCoeff = 1 := (cyclotomic.monic 7 ℂ).leadingCoeff
  have hdegmatch :
      resultant ΦC Pℂ ΦC.natDegree Pℂ.natDegree =
        resultant (ΦZ.map φ) Pℂ ΦZ.natDegree P.natDegree := by
    have h1 : resultant ΦC Pℂ ΦC.natDegree Pℂ.natDegree =
        resultant (ΦZ.map φ) Pℂ (ΦZ.map φ).natDegree Pℂ.natDegree := by
      rw [hmapΦ]
    rw [h1, hdegΦmap, hdegP]
  have hprod' : (ΦC.roots.map (fun α => eval α Pℂ)).prod =
      φ (resultant ΦZ P ΦZ.natDegree P.natDegree) := by
    have := hprod
    rw [hlead, one_pow, one_mul] at this
    rw [← this, hdegmatch, hres]
  have hroots : ΦC.roots = (primitiveRoots 7 ℂ).val :=
    cyclotomic.roots_eq_primitiveRoots_val
  have hζ : zeta7 ∈ primitiveRoots 7 ℂ :=
    (mem_primitiveRoots (by decide : 0 < 7)).mpr isPrimitiveRoot_zeta7
  have hζc : conj zeta7 ∈ primitiveRoots 7 ℂ :=
    (mem_primitiveRoots (by decide : 0 < 7)).mpr isPrimitiveRoot_conj_zeta7
  have hprodFin :
      (ΦC.roots.map (fun α => eval α Pℂ)).prod =
        ∏ α ∈ primitiveRoots 7 ℂ, eval α Pℂ := by
    rw [hroots, Finset.prod_eq_multiset_prod]
  have hfactors : ∀ α ∈ primitiveRoots 7 ℂ, eval α Pℂ ≠ 0 := by
    intro α hα
    have hprim : IsPrimitiveRoot α 7 :=
      (mem_primitiveRoots (by decide : 0 < 7)).mp hα
    exact phasePoly_eval_ne_zero_of_primitive s q hS hprim
  have hresZ : resultant ΦZ P ΦZ.natDegree P.natDegree ≠ 0 := by
    intro hz
    have hprod0 : (∏ α ∈ primitiveRoots 7 ℂ, eval α Pℂ) = 0 := by
      rw [← hprodFin, hprod', hz, map_zero]
    rcases Finset.prod_eq_zero_iff.mp hprod0 with ⟨α, hα, hα0⟩
    exact hfactors α hα hα0
  have habsRes : 1 ≤ ‖φ (resultant ΦZ P ΦZ.natDegree P.natDegree)‖ := by
    change ‖((resultant ΦZ P ΦZ.natDegree P.natDegree : ℤ) : ℂ)‖ ≥ 1
    rw [Complex.norm_intCast, ← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hresZ
  set R := primitiveRoots 7 ℂ
  set Rrest := (R.erase zeta7).erase (conj zeta7)
  have hζc' : conj zeta7 ∈ R.erase zeta7 :=
    Finset.mem_erase.mpr ⟨zeta7_ne_conj.symm, hζc⟩
  have hsplit :
      eval zeta7 Pℂ * eval (conj zeta7) Pℂ * ∏ α ∈ Rrest, eval α Pℂ =
        ∏ α ∈ R, eval α Pℂ := by
    have h1 : eval zeta7 Pℂ * ∏ α ∈ R.erase zeta7, eval α Pℂ =
        ∏ α ∈ R, eval α Pℂ :=
      Finset.mul_prod_erase R (fun α => eval α Pℂ) hζ
    have h2 : eval (conj zeta7) Pℂ * ∏ α ∈ Rrest, eval α Pℂ =
        ∏ α ∈ R.erase zeta7, eval α Pℂ :=
      Finset.mul_prod_erase (R.erase zeta7) (fun α => eval α Pℂ) hζc'
    rw [← h1, ← h2]
    ring
  have hcard0 : R.card = 6 := by
    have : ΦC.roots.card = 6 := by
      rw [← cyclotomic7_complex_splits.natDegree_eq_card_roots,
        natDegree_cyclotomic, Nat.totient_prime (by decide : Nat.Prime 7)]
    rw [hroots] at this
    exact this
  have hcard : Rrest.card = 4 := by
    unfold Rrest
    rw [Finset.card_erase_of_mem hζc', Finset.card_erase_of_mem hζ, hcard0]
  have heq_conj : eval (conj zeta7) Pℂ = conj (eval zeta7 Pℂ) :=
    eval_map_int_conj P zeta7
  have hpair :
      ‖eval zeta7 Pℂ * eval (conj zeta7) Pℂ‖ =
        ‖eval zeta7 Pℂ‖ ^ 2 := by
    rw [heq_conj, norm_mul, Complex.norm_conj, ← pow_two]
  have hbound : ∀ α ∈ Rrest, ‖eval α Pℂ‖ ≤ N := by
    intro α hα
    have hα' : α ∈ R :=
      Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hα)
    have hprim : IsPrimitiveRoot α 7 :=
      (mem_primitiveRoots (by decide : 0 < 7)).mp hα'
    exact phasePoly_eval_bound s q (primitive_root_norm_one hprim)
  have hrest : ‖∏ α ∈ Rrest, eval α Pℂ‖ ≤ (N : ℝ) ^ 4 := by
    rw [norm_prod]
    have hle :=
      Finset.prod_le_prod₀
        (fun _ _ => norm_nonneg _)
        (fun α hα => hbound α hα)
    have hNprod : ∏ _α ∈ Rrest, (N : ℝ) = (N : ℝ) ^ 4 := by
      simp [Finset.prod_const, hcard]
    rwa [hNprod] at hle
  have hprodAbs :
      ‖∏ α ∈ R, eval α Pℂ‖ =
        ‖eval zeta7 Pℂ‖ ^ 2 * ‖∏ α ∈ Rrest, eval α Pℂ‖ := by
    rw [← hsplit, norm_mul, hpair]
  have : 1 ≤ ‖eval zeta7 Pℂ‖ ^ 2 * ‖∏ α ∈ Rrest, eval α Pℂ‖ := by
    rw [← hprodAbs, ← hprodFin, hprod']
    exact habsRes
  nlinarith [hrest, sq_nonneg ‖eval zeta7 Pℂ‖]


lemma abs_S_ge_inv_N_pow_two {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ) (q : Fin 3 → ℤ)
    (hS : (∑ k : Fin N,
        exp (2 * Real.pi * I * dot3 (qReal q) (centroidPoint (n k) (s k)))) ≠ 0) :
    (1 : ℝ) / (N : ℝ) ^ 2 ≤
      ‖(∑ k : Fin N,
          exp (2 * Real.pi * I * dot3 (qReal q) (centroidPoint (n k) (s k))))‖ := by
  have heval :
      (∑ k : Fin N,
          exp (2 * Real.pi * I * dot3 (qReal q) (centroidPoint (n k) (s k)))) =
        eval zeta7 ((phasePoly s q).map (Int.castRingHom ℂ)) :=
    sum_phase_eq_eval_phasePoly n s q
  have hS' : eval zeta7 ((phasePoly s q).map (Int.castRingHom ℂ)) ≠ 0 := by
    rwa [← heval]
  have hlb := abs_resultant_phasePoly_conj s q hS'
  rw [heval]
  set Sℂ := eval zeta7 ((phasePoly s q).map (Int.castRingHom ℂ))
  have hN2 : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
  have hN4 : (0 : ℝ) < (N : ℝ) ^ 4 := by positivity
  have hsq : ((1 : ℝ) / (N : ℝ) ^ 2) ^ 2 ≤ ‖Sℂ‖ ^ 2 := by
    have hpow : ((1 : ℝ) / (N : ℝ) ^ 2) ^ 2 = (1 : ℝ) / (N : ℝ) ^ 4 := by
      field_simp
    rw [hpow, div_le_iff₀ hN4]
    exact hlb
  exact (sq_le_sq₀ (by positivity) (norm_nonneg Sℂ)).mp hsq

/-- `[P, Lean]` If `F ≠ 0` at an integer wavevector then `‖F‖ ≥ 1/N³`. -/
theorem norm_structureFactor_ge_inv_N_pow_three {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (_hs : ∀ k j, s k j = 1 ∨ s k j = -1)
    (qZ : Fin 3 → ℤ)
    (hF : structureFactor (fun k => centroidPoint (n k) (s k)) (qReal qZ) ≠ 0) :
    (1 : ℝ) / (N : ℝ) ^ 3 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) (qReal qZ)‖ := by
  set S := (∑ k : Fin N,
      exp (2 * Real.pi * I * dot3 (qReal qZ) (centroidPoint (n k) (s k))))
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hSF : structureFactor (fun k => centroidPoint (n k) (s k)) (qReal qZ) =
      (N : ℂ)⁻¹ * S := rfl
  have hS0 : S ≠ 0 := by
    intro h0
    apply hF
    rw [hSF, h0, mul_zero]
  have hSbound := abs_S_ge_inv_N_pow_two hN n s qZ hS0
  have hnorm : ‖structureFactor (fun k => centroidPoint (n k) (s k)) (qReal qZ)‖ =
      ‖S‖ / N := by
    rw [hSF, norm_mul, norm_inv, Complex.norm_natCast]
    field_simp [hNpos.ne']
  rw [hnorm]
  have heq : (1 : ℝ) / (N : ℝ) ^ 3 = ((1 : ℝ) / (N : ℝ) ^ 2) / N := by
    field_simp
  rw [heq]
  exact div_le_div_of_nonneg_right hSbound hNpos.le

theorem normSq_structureFactor_ge_inv_N_pow_six {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1)
    (qZ : Fin 3 → ℤ)
    (hF : structureFactor (fun k => centroidPoint (n k) (s k)) (qReal qZ) ≠ 0) :
    (1 : ℝ) / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) (qReal qZ)‖ ^ 2 := by
  have h := norm_structureFactor_ge_inv_N_pow_three hN n s hs qZ hF
  have hpos : 0 ≤ (1 : ℝ) / (N : ℝ) ^ 3 := by positivity
  have hpow := pow_le_pow_left₀ hpos h (n := 2)
  have hsq : ((1 : ℝ) / (N : ℝ) ^ 3) ^ 2 = (1 : ℝ) / (N : ℝ) ^ 6 := by
    field_simp
  rwa [hsq] at hpow

/-- The general bound applies to every signed-permutation image, since
`orbitQ q σ eps` is an integer wavevector. -/
theorem norm_structureFactor_ge_inv_N_pow_three_orbit {N : ℕ} (hN : 1 ≤ N)
    (qZ : Fin 3 → ℤ) (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (_heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1)
    (hF : structureFactor (fun k => centroidPoint (n k) (s k))
      (qReal (orbitQ qZ σ eps)) ≠ 0) :
    (1 : ℝ) / (N : ℝ) ^ 3 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (orbitQ qZ σ eps))‖ :=
  norm_structureFactor_ge_inv_N_pow_three hN n s hs (orbitQ qZ σ eps) hF

/-! ## Corollaries at the fifteen two- and three-pair representatives -/

/-- `[P, Lean]` `‖F‖ ≥ 1/N³` at the representative `(2,1,0)`. -/
theorem norm_structureFactor_ge_inv_N_pow_three_at_210
    {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 3 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (qOf 2 1 0))‖ :=
  norm_structureFactor_ge_inv_N_pow_three hN n s hs (qOf 2 1 0)
    (structureFactor_ne_zero_at_210 hN n s hs)

theorem normSq_structureFactor_ge_inv_N_pow_six_at_210
    {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (qOf 2 1 0))‖ ^ 2 :=
  normSq_structureFactor_ge_inv_N_pow_six hN n s hs (qOf 2 1 0)
    (structureFactor_ne_zero_at_210 hN n s hs)

/-- `[P, Lean]` The same `1/N³` bound on the full signed-permutation orbit of `(2,1,0)`. -/
theorem norm_structureFactor_ge_inv_N_pow_three_orbit_210
    {N : ℕ} (hN : 1 ≤ N)
    (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 3 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (orbitQ (qOf 2 1 0) σ eps))‖ :=
  norm_structureFactor_ge_inv_N_pow_three hN n s hs
    (orbitQ (qOf 2 1 0) σ eps)
    (structureFactor_ne_zero_orbit_transfer hN (qOf 2 1 0)
      (fun {_N'} hN' n' s' hs' =>
        structureFactor_ne_zero_at_210 hN' n' s' hs')
      σ eps heps n s hs)

theorem normSq_structureFactor_ge_inv_N_pow_six_orbit_210
    {N : ℕ} (hN : 1 ≤ N)
    (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (orbitQ (qOf 2 1 0) σ eps))‖ ^ 2 :=
  normSq_structureFactor_ge_inv_N_pow_six hN n s hs
    (orbitQ (qOf 2 1 0) σ eps)
    (structureFactor_ne_zero_orbit_transfer hN (qOf 2 1 0)
      (fun {_N'} hN' n' s' hs' =>
        structureFactor_ne_zero_at_210 hN' n' s' hs')
      σ eps heps n s hs)

/-- `[P, Lean]` `‖F‖ ≥ 1/N³` at the representative `(1,1,1)`. -/
theorem norm_structureFactor_ge_inv_N_pow_three_at_111
    {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 3 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (qOf 1 1 1))‖ :=
  norm_structureFactor_ge_inv_N_pow_three hN n s hs (qOf 1 1 1)
    (structureFactor_ne_zero_at_111 hN n s hs)

theorem normSq_structureFactor_ge_inv_N_pow_six_at_111
    {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (qOf 1 1 1))‖ ^ 2 :=
  normSq_structureFactor_ge_inv_N_pow_six hN n s hs (qOf 1 1 1)
    (structureFactor_ne_zero_at_111 hN n s hs)

/-- `[P, Lean]` The same `1/N³` bound on the full signed-permutation orbit of `(1,1,1)`. -/
theorem norm_structureFactor_ge_inv_N_pow_three_orbit_111
    {N : ℕ} (hN : 1 ≤ N)
    (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 3 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (orbitQ (qOf 1 1 1) σ eps))‖ :=
  norm_structureFactor_ge_inv_N_pow_three hN n s hs
    (orbitQ (qOf 1 1 1) σ eps)
    (structureFactor_ne_zero_orbit_transfer hN (qOf 1 1 1)
      (fun {_N'} hN' n' s' hs' =>
        structureFactor_ne_zero_at_111 hN' n' s' hs')
      σ eps heps n s hs)

theorem normSq_structureFactor_ge_inv_N_pow_six_orbit_111
    {N : ℕ} (hN : 1 ≤ N)
    (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (orbitQ (qOf 1 1 1) σ eps))‖ ^ 2 :=
  normSq_structureFactor_ge_inv_N_pow_six hN n s hs
    (orbitQ (qOf 1 1 1) σ eps)
    (structureFactor_ne_zero_orbit_transfer hN (qOf 1 1 1)
      (fun {_N'} hN' n' s' hs' =>
        structureFactor_ne_zero_at_111 hN' n' s' hs')
      σ eps heps n s hs)

/-- `[P, Lean]` `‖F‖ ≥ 1/N³` at the representative `(3,1,0)`. -/
theorem norm_structureFactor_ge_inv_N_pow_three_at_310
    {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 3 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (qOf 3 1 0))‖ :=
  norm_structureFactor_ge_inv_N_pow_three hN n s hs (qOf 3 1 0)
    (structureFactor_ne_zero_at_310 hN n s hs)

theorem normSq_structureFactor_ge_inv_N_pow_six_at_310
    {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (qOf 3 1 0))‖ ^ 2 :=
  normSq_structureFactor_ge_inv_N_pow_six hN n s hs (qOf 3 1 0)
    (structureFactor_ne_zero_at_310 hN n s hs)

/-- `[P, Lean]` The same `1/N³` bound on the full signed-permutation orbit of `(3,1,0)`. -/
theorem norm_structureFactor_ge_inv_N_pow_three_orbit_310
    {N : ℕ} (hN : 1 ≤ N)
    (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 3 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (orbitQ (qOf 3 1 0) σ eps))‖ :=
  norm_structureFactor_ge_inv_N_pow_three hN n s hs
    (orbitQ (qOf 3 1 0) σ eps)
    (structureFactor_ne_zero_orbit_transfer hN (qOf 3 1 0)
      (fun {_N'} hN' n' s' hs' =>
        structureFactor_ne_zero_at_310 hN' n' s' hs')
      σ eps heps n s hs)

theorem normSq_structureFactor_ge_inv_N_pow_six_orbit_310
    {N : ℕ} (hN : 1 ≤ N)
    (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (orbitQ (qOf 3 1 0) σ eps))‖ ^ 2 :=
  normSq_structureFactor_ge_inv_N_pow_six hN n s hs
    (orbitQ (qOf 3 1 0) σ eps)
    (structureFactor_ne_zero_orbit_transfer hN (qOf 3 1 0)
      (fun {_N'} hN' n' s' hs' =>
        structureFactor_ne_zero_at_310 hN' n' s' hs')
      σ eps heps n s hs)

/-- `[P, Lean]` `‖F‖ ≥ 1/N³` at the representative `(2,1,1)`. -/
theorem norm_structureFactor_ge_inv_N_pow_three_at_211
    {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 3 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (qOf 2 1 1))‖ :=
  norm_structureFactor_ge_inv_N_pow_three hN n s hs (qOf 2 1 1)
    (structureFactor_ne_zero_at_211 hN n s hs)

theorem normSq_structureFactor_ge_inv_N_pow_six_at_211
    {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (qOf 2 1 1))‖ ^ 2 :=
  normSq_structureFactor_ge_inv_N_pow_six hN n s hs (qOf 2 1 1)
    (structureFactor_ne_zero_at_211 hN n s hs)

/-- `[P, Lean]` The same `1/N³` bound on the full signed-permutation orbit of `(2,1,1)`. -/
theorem norm_structureFactor_ge_inv_N_pow_three_orbit_211
    {N : ℕ} (hN : 1 ≤ N)
    (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 3 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (orbitQ (qOf 2 1 1) σ eps))‖ :=
  norm_structureFactor_ge_inv_N_pow_three hN n s hs
    (orbitQ (qOf 2 1 1) σ eps)
    (structureFactor_ne_zero_orbit_transfer hN (qOf 2 1 1)
      (fun {_N'} hN' n' s' hs' =>
        structureFactor_ne_zero_at_211 hN' n' s' hs')
      σ eps heps n s hs)

theorem normSq_structureFactor_ge_inv_N_pow_six_orbit_211
    {N : ℕ} (hN : 1 ≤ N)
    (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (orbitQ (qOf 2 1 1) σ eps))‖ ^ 2 :=
  normSq_structureFactor_ge_inv_N_pow_six hN n s hs
    (orbitQ (qOf 2 1 1) σ eps)
    (structureFactor_ne_zero_orbit_transfer hN (qOf 2 1 1)
      (fun {_N'} hN' n' s' hs' =>
        structureFactor_ne_zero_at_211 hN' n' s' hs')
      σ eps heps n s hs)

/-- `[P, Lean]` `‖F‖ ≥ 1/N³` at the representative `(4,1,0)`. -/
theorem norm_structureFactor_ge_inv_N_pow_three_at_410
    {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 3 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (qOf 4 1 0))‖ :=
  norm_structureFactor_ge_inv_N_pow_three hN n s hs (qOf 4 1 0)
    (structureFactor_ne_zero_at_410 hN n s hs)

theorem normSq_structureFactor_ge_inv_N_pow_six_at_410
    {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (qOf 4 1 0))‖ ^ 2 :=
  normSq_structureFactor_ge_inv_N_pow_six hN n s hs (qOf 4 1 0)
    (structureFactor_ne_zero_at_410 hN n s hs)

/-- `[P, Lean]` The same `1/N³` bound on the full signed-permutation orbit of `(4,1,0)`. -/
theorem norm_structureFactor_ge_inv_N_pow_three_orbit_410
    {N : ℕ} (hN : 1 ≤ N)
    (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 3 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (orbitQ (qOf 4 1 0) σ eps))‖ :=
  norm_structureFactor_ge_inv_N_pow_three hN n s hs
    (orbitQ (qOf 4 1 0) σ eps)
    (structureFactor_ne_zero_orbit_transfer hN (qOf 4 1 0)
      (fun {_N'} hN' n' s' hs' =>
        structureFactor_ne_zero_at_410 hN' n' s' hs')
      σ eps heps n s hs)

theorem normSq_structureFactor_ge_inv_N_pow_six_orbit_410
    {N : ℕ} (hN : 1 ≤ N)
    (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (orbitQ (qOf 4 1 0) σ eps))‖ ^ 2 :=
  normSq_structureFactor_ge_inv_N_pow_six hN n s hs
    (orbitQ (qOf 4 1 0) σ eps)
    (structureFactor_ne_zero_orbit_transfer hN (qOf 4 1 0)
      (fun {_N'} hN' n' s' hs' =>
        structureFactor_ne_zero_at_410 hN' n' s' hs')
      σ eps heps n s hs)

/-- `[P, Lean]` `‖F‖ ≥ 1/N³` at the representative `(3,2,0)`. -/
theorem norm_structureFactor_ge_inv_N_pow_three_at_320
    {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 3 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (qOf 3 2 0))‖ :=
  norm_structureFactor_ge_inv_N_pow_three hN n s hs (qOf 3 2 0)
    (structureFactor_ne_zero_at_320 hN n s hs)

theorem normSq_structureFactor_ge_inv_N_pow_six_at_320
    {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (qOf 3 2 0))‖ ^ 2 :=
  normSq_structureFactor_ge_inv_N_pow_six hN n s hs (qOf 3 2 0)
    (structureFactor_ne_zero_at_320 hN n s hs)

/-- `[P, Lean]` The same `1/N³` bound on the full signed-permutation orbit of `(3,2,0)`. -/
theorem norm_structureFactor_ge_inv_N_pow_three_orbit_320
    {N : ℕ} (hN : 1 ≤ N)
    (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 3 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (orbitQ (qOf 3 2 0) σ eps))‖ :=
  norm_structureFactor_ge_inv_N_pow_three hN n s hs
    (orbitQ (qOf 3 2 0) σ eps)
    (structureFactor_ne_zero_orbit_transfer hN (qOf 3 2 0)
      (fun {_N'} hN' n' s' hs' =>
        structureFactor_ne_zero_at_320 hN' n' s' hs')
      σ eps heps n s hs)

theorem normSq_structureFactor_ge_inv_N_pow_six_orbit_320
    {N : ℕ} (hN : 1 ≤ N)
    (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (orbitQ (qOf 3 2 0) σ eps))‖ ^ 2 :=
  normSq_structureFactor_ge_inv_N_pow_six hN n s hs
    (orbitQ (qOf 3 2 0) σ eps)
    (structureFactor_ne_zero_orbit_transfer hN (qOf 3 2 0)
      (fun {_N'} hN' n' s' hs' =>
        structureFactor_ne_zero_at_320 hN' n' s' hs')
      σ eps heps n s hs)

/-- `[P, Lean]` `‖F‖ ≥ 1/N³` at the representative `(3,1,1)`. -/
theorem norm_structureFactor_ge_inv_N_pow_three_at_311
    {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 3 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (qOf 3 1 1))‖ :=
  norm_structureFactor_ge_inv_N_pow_three hN n s hs (qOf 3 1 1)
    (structureFactor_ne_zero_at_311 hN n s hs)

theorem normSq_structureFactor_ge_inv_N_pow_six_at_311
    {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (qOf 3 1 1))‖ ^ 2 :=
  normSq_structureFactor_ge_inv_N_pow_six hN n s hs (qOf 3 1 1)
    (structureFactor_ne_zero_at_311 hN n s hs)

/-- `[P, Lean]` The same `1/N³` bound on the full signed-permutation orbit of `(3,1,1)`. -/
theorem norm_structureFactor_ge_inv_N_pow_three_orbit_311
    {N : ℕ} (hN : 1 ≤ N)
    (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 3 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (orbitQ (qOf 3 1 1) σ eps))‖ :=
  norm_structureFactor_ge_inv_N_pow_three hN n s hs
    (orbitQ (qOf 3 1 1) σ eps)
    (structureFactor_ne_zero_orbit_transfer hN (qOf 3 1 1)
      (fun {_N'} hN' n' s' hs' =>
        structureFactor_ne_zero_at_311 hN' n' s' hs')
      σ eps heps n s hs)

theorem normSq_structureFactor_ge_inv_N_pow_six_orbit_311
    {N : ℕ} (hN : 1 ≤ N)
    (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (orbitQ (qOf 3 1 1) σ eps))‖ ^ 2 :=
  normSq_structureFactor_ge_inv_N_pow_six hN n s hs
    (orbitQ (qOf 3 1 1) σ eps)
    (structureFactor_ne_zero_orbit_transfer hN (qOf 3 1 1)
      (fun {_N'} hN' n' s' hs' =>
        structureFactor_ne_zero_at_311 hN' n' s' hs')
      σ eps heps n s hs)

/-- `[P, Lean]` `‖F‖ ≥ 1/N³` at the representative `(2,2,1)`. -/
theorem norm_structureFactor_ge_inv_N_pow_three_at_221
    {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 3 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (qOf 2 2 1))‖ :=
  norm_structureFactor_ge_inv_N_pow_three hN n s hs (qOf 2 2 1)
    (structureFactor_ne_zero_at_221 hN n s hs)

theorem normSq_structureFactor_ge_inv_N_pow_six_at_221
    {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (qOf 2 2 1))‖ ^ 2 :=
  normSq_structureFactor_ge_inv_N_pow_six hN n s hs (qOf 2 2 1)
    (structureFactor_ne_zero_at_221 hN n s hs)

/-- `[P, Lean]` The same `1/N³` bound on the full signed-permutation orbit of `(2,2,1)`. -/
theorem norm_structureFactor_ge_inv_N_pow_three_orbit_221
    {N : ℕ} (hN : 1 ≤ N)
    (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 3 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (orbitQ (qOf 2 2 1) σ eps))‖ :=
  norm_structureFactor_ge_inv_N_pow_three hN n s hs
    (orbitQ (qOf 2 2 1) σ eps)
    (structureFactor_ne_zero_orbit_transfer hN (qOf 2 2 1)
      (fun {_N'} hN' n' s' hs' =>
        structureFactor_ne_zero_at_221 hN' n' s' hs')
      σ eps heps n s hs)

theorem normSq_structureFactor_ge_inv_N_pow_six_orbit_221
    {N : ℕ} (hN : 1 ≤ N)
    (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (orbitQ (qOf 2 2 1) σ eps))‖ ^ 2 :=
  normSq_structureFactor_ge_inv_N_pow_six hN n s hs
    (orbitQ (qOf 2 2 1) σ eps)
    (structureFactor_ne_zero_orbit_transfer hN (qOf 2 2 1)
      (fun {_N'} hN' n' s' hs' =>
        structureFactor_ne_zero_at_221 hN' n' s' hs')
      σ eps heps n s hs)

/-- `[P, Lean]` `‖F‖ ≥ 1/N³` at the representative `(5,1,0)`. -/
theorem norm_structureFactor_ge_inv_N_pow_three_at_510
    {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 3 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (qOf 5 1 0))‖ :=
  norm_structureFactor_ge_inv_N_pow_three hN n s hs (qOf 5 1 0)
    (structureFactor_ne_zero_at_510 hN n s hs)

theorem normSq_structureFactor_ge_inv_N_pow_six_at_510
    {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (qOf 5 1 0))‖ ^ 2 :=
  normSq_structureFactor_ge_inv_N_pow_six hN n s hs (qOf 5 1 0)
    (structureFactor_ne_zero_at_510 hN n s hs)

/-- `[P, Lean]` The same `1/N³` bound on the full signed-permutation orbit of `(5,1,0)`. -/
theorem norm_structureFactor_ge_inv_N_pow_three_orbit_510
    {N : ℕ} (hN : 1 ≤ N)
    (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 3 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (orbitQ (qOf 5 1 0) σ eps))‖ :=
  norm_structureFactor_ge_inv_N_pow_three hN n s hs
    (orbitQ (qOf 5 1 0) σ eps)
    (structureFactor_ne_zero_orbit_transfer hN (qOf 5 1 0)
      (fun {_N'} hN' n' s' hs' =>
        structureFactor_ne_zero_at_510 hN' n' s' hs')
      σ eps heps n s hs)

theorem normSq_structureFactor_ge_inv_N_pow_six_orbit_510
    {N : ℕ} (hN : 1 ≤ N)
    (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (orbitQ (qOf 5 1 0) σ eps))‖ ^ 2 :=
  normSq_structureFactor_ge_inv_N_pow_six hN n s hs
    (orbitQ (qOf 5 1 0) σ eps)
    (structureFactor_ne_zero_orbit_transfer hN (qOf 5 1 0)
      (fun {_N'} hN' n' s' hs' =>
        structureFactor_ne_zero_at_510 hN' n' s' hs')
      σ eps heps n s hs)

/-- `[P, Lean]` `‖F‖ ≥ 1/N³` at the representative `(4,2,0)`. -/
theorem norm_structureFactor_ge_inv_N_pow_three_at_420
    {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 3 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (qOf 4 2 0))‖ :=
  norm_structureFactor_ge_inv_N_pow_three hN n s hs (qOf 4 2 0)
    (structureFactor_ne_zero_at_420 hN n s hs)

theorem normSq_structureFactor_ge_inv_N_pow_six_at_420
    {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (qOf 4 2 0))‖ ^ 2 :=
  normSq_structureFactor_ge_inv_N_pow_six hN n s hs (qOf 4 2 0)
    (structureFactor_ne_zero_at_420 hN n s hs)

/-- `[P, Lean]` The same `1/N³` bound on the full signed-permutation orbit of `(4,2,0)`. -/
theorem norm_structureFactor_ge_inv_N_pow_three_orbit_420
    {N : ℕ} (hN : 1 ≤ N)
    (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 3 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (orbitQ (qOf 4 2 0) σ eps))‖ :=
  norm_structureFactor_ge_inv_N_pow_three hN n s hs
    (orbitQ (qOf 4 2 0) σ eps)
    (structureFactor_ne_zero_orbit_transfer hN (qOf 4 2 0)
      (fun {_N'} hN' n' s' hs' =>
        structureFactor_ne_zero_at_420 hN' n' s' hs')
      σ eps heps n s hs)

theorem normSq_structureFactor_ge_inv_N_pow_six_orbit_420
    {N : ℕ} (hN : 1 ≤ N)
    (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (orbitQ (qOf 4 2 0) σ eps))‖ ^ 2 :=
  normSq_structureFactor_ge_inv_N_pow_six hN n s hs
    (orbitQ (qOf 4 2 0) σ eps)
    (structureFactor_ne_zero_orbit_transfer hN (qOf 4 2 0)
      (fun {_N'} hN' n' s' hs' =>
        structureFactor_ne_zero_at_420 hN' n' s' hs')
      σ eps heps n s hs)

/-- `[P, Lean]` `‖F‖ ≥ 1/N³` at the representative `(4,1,1)`. -/
theorem norm_structureFactor_ge_inv_N_pow_three_at_411
    {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 3 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (qOf 4 1 1))‖ :=
  norm_structureFactor_ge_inv_N_pow_three hN n s hs (qOf 4 1 1)
    (structureFactor_ne_zero_at_411 hN n s hs)

theorem normSq_structureFactor_ge_inv_N_pow_six_at_411
    {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (qOf 4 1 1))‖ ^ 2 :=
  normSq_structureFactor_ge_inv_N_pow_six hN n s hs (qOf 4 1 1)
    (structureFactor_ne_zero_at_411 hN n s hs)

/-- `[P, Lean]` The same `1/N³` bound on the full signed-permutation orbit of `(4,1,1)`. -/
theorem norm_structureFactor_ge_inv_N_pow_three_orbit_411
    {N : ℕ} (hN : 1 ≤ N)
    (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 3 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (orbitQ (qOf 4 1 1) σ eps))‖ :=
  norm_structureFactor_ge_inv_N_pow_three hN n s hs
    (orbitQ (qOf 4 1 1) σ eps)
    (structureFactor_ne_zero_orbit_transfer hN (qOf 4 1 1)
      (fun {_N'} hN' n' s' hs' =>
        structureFactor_ne_zero_at_411 hN' n' s' hs')
      σ eps heps n s hs)

theorem normSq_structureFactor_ge_inv_N_pow_six_orbit_411
    {N : ℕ} (hN : 1 ≤ N)
    (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (orbitQ (qOf 4 1 1) σ eps))‖ ^ 2 :=
  normSq_structureFactor_ge_inv_N_pow_six hN n s hs
    (orbitQ (qOf 4 1 1) σ eps)
    (structureFactor_ne_zero_orbit_transfer hN (qOf 4 1 1)
      (fun {_N'} hN' n' s' hs' =>
        structureFactor_ne_zero_at_411 hN' n' s' hs')
      σ eps heps n s hs)

/-- `[P, Lean]` `‖F‖ ≥ 1/N³` at the representative `(2,2,2)`. -/
theorem norm_structureFactor_ge_inv_N_pow_three_at_222
    {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 3 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (qOf 2 2 2))‖ :=
  norm_structureFactor_ge_inv_N_pow_three hN n s hs (qOf 2 2 2)
    (structureFactor_ne_zero_at_222 hN n s hs)

theorem normSq_structureFactor_ge_inv_N_pow_six_at_222
    {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (qOf 2 2 2))‖ ^ 2 :=
  normSq_structureFactor_ge_inv_N_pow_six hN n s hs (qOf 2 2 2)
    (structureFactor_ne_zero_at_222 hN n s hs)

/-- `[P, Lean]` The same `1/N³` bound on the full signed-permutation orbit of `(2,2,2)`. -/
theorem norm_structureFactor_ge_inv_N_pow_three_orbit_222
    {N : ℕ} (hN : 1 ≤ N)
    (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 3 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (orbitQ (qOf 2 2 2) σ eps))‖ :=
  norm_structureFactor_ge_inv_N_pow_three hN n s hs
    (orbitQ (qOf 2 2 2) σ eps)
    (structureFactor_ne_zero_orbit_transfer hN (qOf 2 2 2)
      (fun {_N'} hN' n' s' hs' =>
        structureFactor_ne_zero_at_222 hN' n' s' hs')
      σ eps heps n s hs)

theorem normSq_structureFactor_ge_inv_N_pow_six_orbit_222
    {N : ℕ} (hN : 1 ≤ N)
    (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (orbitQ (qOf 2 2 2) σ eps))‖ ^ 2 :=
  normSq_structureFactor_ge_inv_N_pow_six hN n s hs
    (orbitQ (qOf 2 2 2) σ eps)
    (structureFactor_ne_zero_orbit_transfer hN (qOf 2 2 2)
      (fun {_N'} hN' n' s' hs' =>
        structureFactor_ne_zero_at_222 hN' n' s' hs')
      σ eps heps n s hs)

/-- `[P, Lean]` `‖F‖ ≥ 1/N³` at the representative `(5,1,1)`. -/
theorem norm_structureFactor_ge_inv_N_pow_three_at_511
    {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 3 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (qOf 5 1 1))‖ :=
  norm_structureFactor_ge_inv_N_pow_three hN n s hs (qOf 5 1 1)
    (structureFactor_ne_zero_at_511 hN n s hs)

theorem normSq_structureFactor_ge_inv_N_pow_six_at_511
    {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (qOf 5 1 1))‖ ^ 2 :=
  normSq_structureFactor_ge_inv_N_pow_six hN n s hs (qOf 5 1 1)
    (structureFactor_ne_zero_at_511 hN n s hs)

/-- `[P, Lean]` The same `1/N³` bound on the full signed-permutation orbit of `(5,1,1)`. -/
theorem norm_structureFactor_ge_inv_N_pow_three_orbit_511
    {N : ℕ} (hN : 1 ≤ N)
    (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 3 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (orbitQ (qOf 5 1 1) σ eps))‖ :=
  norm_structureFactor_ge_inv_N_pow_three hN n s hs
    (orbitQ (qOf 5 1 1) σ eps)
    (structureFactor_ne_zero_orbit_transfer hN (qOf 5 1 1)
      (fun {_N'} hN' n' s' hs' =>
        structureFactor_ne_zero_at_511 hN' n' s' hs')
      σ eps heps n s hs)

theorem normSq_structureFactor_ge_inv_N_pow_six_orbit_511
    {N : ℕ} (hN : 1 ≤ N)
    (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (orbitQ (qOf 5 1 1) σ eps))‖ ^ 2 :=
  normSq_structureFactor_ge_inv_N_pow_six hN n s hs
    (orbitQ (qOf 5 1 1) σ eps)
    (structureFactor_ne_zero_orbit_transfer hN (qOf 5 1 1)
      (fun {_N'} hN' n' s' hs' =>
        structureFactor_ne_zero_at_511 hN' n' s' hs')
      σ eps heps n s hs)

/-- `[P, Lean]` `‖F‖ ≥ 1/N³` at the representative `(3,3,1)`. -/
theorem norm_structureFactor_ge_inv_N_pow_three_at_331
    {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 3 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (qOf 3 3 1))‖ :=
  norm_structureFactor_ge_inv_N_pow_three hN n s hs (qOf 3 3 1)
    (structureFactor_ne_zero_at_331 hN n s hs)

theorem normSq_structureFactor_ge_inv_N_pow_six_at_331
    {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (qOf 3 3 1))‖ ^ 2 :=
  normSq_structureFactor_ge_inv_N_pow_six hN n s hs (qOf 3 3 1)
    (structureFactor_ne_zero_at_331 hN n s hs)

/-- `[P, Lean]` The same `1/N³` bound on the full signed-permutation orbit of `(3,3,1)`. -/
theorem norm_structureFactor_ge_inv_N_pow_three_orbit_331
    {N : ℕ} (hN : 1 ≤ N)
    (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 3 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (orbitQ (qOf 3 3 1) σ eps))‖ :=
  norm_structureFactor_ge_inv_N_pow_three hN n s hs
    (orbitQ (qOf 3 3 1) σ eps)
    (structureFactor_ne_zero_orbit_transfer hN (qOf 3 3 1)
      (fun {_N'} hN' n' s' hs' =>
        structureFactor_ne_zero_at_331 hN' n' s' hs')
      σ eps heps n s hs)

theorem normSq_structureFactor_ge_inv_N_pow_six_orbit_331
    {N : ℕ} (hN : 1 ≤ N)
    (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (orbitQ (qOf 3 3 1) σ eps))‖ ^ 2 :=
  normSq_structureFactor_ge_inv_N_pow_six hN n s hs
    (orbitQ (qOf 3 3 1) σ eps)
    (structureFactor_ne_zero_orbit_transfer hN (qOf 3 3 1)
      (fun {_N'} hN' n' s' hs' =>
        structureFactor_ne_zero_at_331 hN' n' s' hs')
      σ eps heps n s hs)

/-- `[P, Lean]` `‖F‖ ≥ 1/N³` at the representative `(3,2,2)`. -/
theorem norm_structureFactor_ge_inv_N_pow_three_at_322
    {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 3 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (qOf 3 2 2))‖ :=
  norm_structureFactor_ge_inv_N_pow_three hN n s hs (qOf 3 2 2)
    (structureFactor_ne_zero_at_322 hN n s hs)

theorem normSq_structureFactor_ge_inv_N_pow_six_at_322
    {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (qOf 3 2 2))‖ ^ 2 :=
  normSq_structureFactor_ge_inv_N_pow_six hN n s hs (qOf 3 2 2)
    (structureFactor_ne_zero_at_322 hN n s hs)

/-- `[P, Lean]` The same `1/N³` bound on the full signed-permutation orbit of `(3,2,2)`. -/
theorem norm_structureFactor_ge_inv_N_pow_three_orbit_322
    {N : ℕ} (hN : 1 ≤ N)
    (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 3 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (orbitQ (qOf 3 2 2) σ eps))‖ :=
  norm_structureFactor_ge_inv_N_pow_three hN n s hs
    (orbitQ (qOf 3 2 2) σ eps)
    (structureFactor_ne_zero_orbit_transfer hN (qOf 3 2 2)
      (fun {_N'} hN' n' s' hs' =>
        structureFactor_ne_zero_at_322 hN' n' s' hs')
      σ eps heps n s hs)

theorem normSq_structureFactor_ge_inv_N_pow_six_orbit_322
    {N : ℕ} (hN : 1 ≤ N)
    (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (orbitQ (qOf 3 2 2) σ eps))‖ ^ 2 :=
  normSq_structureFactor_ge_inv_N_pow_six hN n s hs
    (orbitQ (qOf 3 2 2) σ eps)
    (structureFactor_ne_zero_orbit_transfer hN (qOf 3 2 2)
      (fun {_N'} hN' n' s' hs' =>
        structureFactor_ne_zero_at_322 hN' n' s' hs')
      σ eps heps n s hs)

#print axioms conj_zeta7_eq_pow_six
#print axioms eval_map_int_conj
#print axioms abs_resultant_phasePoly_conj
#print axioms norm_structureFactor_ge_inv_N_pow_three
#print axioms normSq_structureFactor_ge_inv_N_pow_six
#print axioms norm_structureFactor_ge_inv_N_pow_three_orbit
#print axioms norm_structureFactor_ge_inv_N_pow_three_at_210
#print axioms norm_structureFactor_ge_inv_N_pow_three_orbit_210
#print axioms norm_structureFactor_ge_inv_N_pow_three_at_111
#print axioms norm_structureFactor_ge_inv_N_pow_three_orbit_111
#print axioms norm_structureFactor_ge_inv_N_pow_three_at_310
#print axioms norm_structureFactor_ge_inv_N_pow_three_orbit_310
#print axioms norm_structureFactor_ge_inv_N_pow_three_at_211
#print axioms norm_structureFactor_ge_inv_N_pow_three_orbit_211
#print axioms norm_structureFactor_ge_inv_N_pow_three_at_410
#print axioms norm_structureFactor_ge_inv_N_pow_three_orbit_410
#print axioms norm_structureFactor_ge_inv_N_pow_three_at_320
#print axioms norm_structureFactor_ge_inv_N_pow_three_orbit_320
#print axioms norm_structureFactor_ge_inv_N_pow_three_at_311
#print axioms norm_structureFactor_ge_inv_N_pow_three_orbit_311
#print axioms norm_structureFactor_ge_inv_N_pow_three_at_221
#print axioms norm_structureFactor_ge_inv_N_pow_three_orbit_221
#print axioms norm_structureFactor_ge_inv_N_pow_three_at_510
#print axioms norm_structureFactor_ge_inv_N_pow_three_orbit_510
#print axioms norm_structureFactor_ge_inv_N_pow_three_at_420
#print axioms norm_structureFactor_ge_inv_N_pow_three_orbit_420
#print axioms norm_structureFactor_ge_inv_N_pow_three_at_411
#print axioms norm_structureFactor_ge_inv_N_pow_three_orbit_411
#print axioms norm_structureFactor_ge_inv_N_pow_three_at_222
#print axioms norm_structureFactor_ge_inv_N_pow_three_orbit_222
#print axioms norm_structureFactor_ge_inv_N_pow_three_at_511
#print axioms norm_structureFactor_ge_inv_N_pow_three_orbit_511
#print axioms norm_structureFactor_ge_inv_N_pow_three_at_331
#print axioms norm_structureFactor_ge_inv_N_pow_three_orbit_331
#print axioms norm_structureFactor_ge_inv_N_pow_three_at_322
#print axioms norm_structureFactor_ge_inv_N_pow_three_orbit_322

end LeanLab.Scratch.LemmaDUniversalLowerBoundN3
