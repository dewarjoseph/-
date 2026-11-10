import LeanLab.Scratch.LemmaDNoZero220
import LeanLab.Scratch.LemmaDL1Six
import LeanLab.Scratch.LemmaDNoZero310211
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Polynomial.Tower

/-!
# A uniform lower bound |F| ≥ 1/N⁶ at any integer q with F ≠ 0
(public-screen)

Public-screen v2 copy of LeanLab.Scratch.LemmaDGeneralLowerBound (official pin src
`884d0aceccc2000ea93d77fcae48caff6c61178a4083d1845b1a601a6ef9d394`).
Header redacted; theorem bodies are unchanged. This copy is not a
replacement pin.

**[P, Lean]** For every integer wavevector `qZ : Fin 3 → ℤ`, every `N ≥ 1`, and
every equal-weight D-form box `(n, s)` with signs `hs`, if
`F := structureFactor (fun k => centroidPoint (n k) (s k)) (qReal qZ)` is
nonzero, then `‖F‖ ≥ 1/N⁶` (so one may take `c_q = 1` and exponent `k = 6`),
and therefore `|F|² ≥ 1/N¹²`. The contrapositive is
`‖F‖ < 1/N⁶ → F = 0`.

This is weaker than the specialised bounds
`‖F(q₂₂₀)‖ ≥ 1/(30 N³)` (LemmaDLowerBound220) and
`‖F(q₃₃₀)‖ ≥ 1/(65 N³)` (LemmaDLowerBound330); those remain the sharper
statements at those two vectors. The present file only uses `F ≠ 0` plus
the field norm of a cyclotomic integer.

**Argument (checked).** At integer `q` the origins `n_k` drop out of the
phase (`exp_centroid_int_q`), and every summand is `exp(-iπ t/7)` with
`t = q·s`. This equals `ζ₇^m` for even `t` and `-ζ₇^m` for odd `t`
(`exp_neg_pi_t_eq_zeta` / `exp_neg_pi_t_eq_neg_zeta`, packed below as a
general-`t` phase lemma). Hence `N·F = S = ∑_{k=1}^N ε_k ζ^{m_k}` with
`ε_k = ±1`. Let `P ∈ ℤ[X]` be the polynomial `∑_k ε_k X^{m_k}`, so
`S = P(ζ₇)`.

`S` is a nonzero element of `ℤ[ζ₇]`. The resultant
`Res(Φ₇, P) ∈ ℤ` equals (after mapping to `ℂ`) the product
`∏_{j=1}^6 P(ζ₇^j)` over the roots of the 7th cyclotomic polynomial.
If any factor vanished then `Φ₇` (the minpoly of every primitive 7th root)
would divide `P` over `ℚ`, hence also `P(ζ₇) = 0`, contradicting `S ≠ 0`.
Thus the integer resultant is nonzero, so its absolute value is at least 1.
Each `|P(ζ₇^j)|` is the modulus of a sum of `N` unit complex numbers, hence
`≤ N`. The identity-type factor is `|S|`, and therefore
`|S| · N⁵ ≥ 1`, i.e. `|S| ≥ N⁻⁵` and `|F| = |S|/N ≥ N⁻⁶`.

**Not proved / out of scope:**
* Sharpness of the exponent 6, or any improvement of `c_q`.
* Nothing at non-integer `q`. The specialised cubic bounds at `(2,2,0)`
  and `(3,3,0)` are not reproduced here.
* D-form class only. Scratch; not a Lake target; not peer reviewed.

This file is source-only and is not a Lake package. It claims nothing
beyond the theorems stated below.

Dated 2026-11-10.
-/

namespace LeanLab.Scratch.LemmaDGeneralLowerBound

open Complex Polynomial Finset
open LeanLab.Scratch.LemmaD4 (dot3 structureFactor centroidPoint)
open LeanLab.Scratch.LemmaDIntVec
  (qReal signedWeight zeta7 zeta7_pow isPrimitiveRoot_zeta7
    exp_centroid_int_q exp_neg_pi_t_eq_neg_zeta)
open LeanLab.Scratch.LemmaDNoZero310211 (exp_neg_pi_t_eq_zeta)
open LeanLab.Scratch.LemmaDNoZero220
  (qZ220 structureFactor_ne_zero_at_220)
open LeanLab.Scratch.LemmaDL1Six
  (qZ330 q330 structureFactor_ne_zero_at_330)

/-! ## Residues and the general-t phase formula -/

lemma toNat_emod_seven_lt (a : ℤ) : (a % 7).toNat < 7 := by
  have hnn : 0 ≤ a % 7 := Int.emod_nonneg _ (by decide : (7 : ℤ) ≠ 0)
  have hlt : a % 7 < 7 := Int.emod_lt_of_pos _ (by decide : (0 : ℤ) < 7)
  have : ((a % 7).toNat : ℤ) = a % 7 := Int.toNat_of_nonneg hnn
  omega

def residualMod7 (a : ℤ) : Fin 7 :=
  ⟨(a % 7).toNat, toNat_emod_seven_lt a⟩

lemma residualMod7_coe (a : ℤ) : (residualMod7 a : ℤ) = a % 7 :=
  Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide : (7 : ℤ) ≠ 0))

/-- Even `t`: residue `k ≡ -t/2 (mod 7)`. Odd `t`: `k ≡ (7-t)/2 (mod 7)`. -/
def phaseRes (t : ℤ) : Fin 7 :=
  if Even t then residualMod7 (-t / 2) else residualMod7 ((7 - t) / 2)

def phaseSign (t : ℤ) : ℤ := if Even t then 1 else -1

lemma phaseSign_is_sign (t : ℤ) : phaseSign t = 1 ∨ phaseSign t = -1 := by
  unfold phaseSign
  split_ifs <;> simp


lemma even_ediv_two {t : ℤ} (he : Even t) : t = 2 * (t / 2) := by
  obtain ⟨ℓ, hℓ⟩ := he
  have h2 : t = 2 * ℓ := by
    rw [hℓ, two_mul]
  have : t / 2 = ℓ := by
    rw [h2, Int.mul_ediv_cancel_left ℓ (by decide : (2 : ℤ) ≠ 0)]
  rw [this, h2]

lemma even_neg_ediv_two {t : ℤ} (he : Even t) : -t / 2 = -(t / 2) := by
  obtain ⟨ℓ, hℓ⟩ := he
  have h2 : t = 2 * ℓ := by rw [hℓ, two_mul]
  have ht2 : t / 2 = ℓ := by
    rw [h2, Int.mul_ediv_cancel_left ℓ (by decide : (2 : ℤ) ≠ 0)]
  have hneg : -t = 2 * (-ℓ) := by
    rw [h2]; ring
  rw [hneg, ht2, Int.mul_ediv_cancel_left _ (by decide : (2 : ℤ) ≠ 0)]

lemma even_phase_eq (t : ℤ) (he : Even t) :
    t = -2 * (phaseRes t : ℤ) - 14 * ((-t / 2) / 7) := by
  unfold phaseRes
  rw [ite_eq_left he, residualMod7_coe]
  have hdiv := Int.emod_add_mul_ediv (-t / 2) 7
  have ht := even_ediv_two he
  have hneg := even_neg_ediv_two he
  linarith

lemma odd_sub_seven_even {t : ℤ} (ho : Odd t) : Even (7 - t) := by
  have h7 : Odd (7 : ℤ) := by decide
  simpa [sub_eq_add_neg] using Odd.add_odd h7 ho.neg

lemma not_even_iff_odd_int {t : ℤ} : ¬ Even t ↔ Odd t := by
  constructor
  · intro h
    have hmod : t % 2 = 1 := by
      have hlt : t % 2 < 2 := Int.emod_lt_of_pos _ (by decide : (0 : ℤ) < 2)
      have hnn : 0 ≤ t % 2 := Int.emod_nonneg _ (by decide : (2 : ℤ) ≠ 0)
      have hne : t % 2 ≠ 0 := by
        intro hz
        exact h (Int.even_iff.mpr hz)
      have : t % 2 = 0 ∨ t % 2 = 1 := by omega
      exact this.resolve_left hne
    refine ⟨t / 2, ?_⟩
    have := Int.emod_add_mul_ediv t 2
    linarith
  · intro ⟨k, hk⟩ ⟨ℓ, hℓ⟩
    have : (2 * k + 1 : ℤ) = 2 * ℓ := by
      rw [← hk, hℓ, two_mul]
    omega

lemma odd_phase_eq (t : ℤ) (ho : Odd t) :
    t = 7 - 2 * (phaseRes t : ℤ) - 14 * (((7 - t) / 2) / 7) := by
  unfold phaseRes
  have hne : ¬ Even t := not_even_iff_odd_int.mpr ho
  rw [ite_eq_right hne, residualMod7_coe]
  have hdiv := Int.emod_add_mul_ediv ((7 - t) / 2) 7
  have he : Even (7 - t) := odd_sub_seven_even ho
  have h2 : 7 - t = 2 * ((7 - t) / 2) := even_ediv_two he
  linarith

lemma exp_neg_pi_t_eq_signed_zeta (t : ℤ) :
    exp (((-(Real.pi * (t : ℝ) / 7) : ℝ) : ℂ) * I) =
      (phaseSign t : ℂ) * zeta7 ^ (phaseRes t).val := by
  by_cases he : Even t
  · have hform := even_phase_eq t he
    have hs : phaseSign t = 1 := ite_eq_left he
    rw [hs, Int.cast_one, one_mul]
    exact exp_neg_pi_t_eq_zeta t (phaseRes t).val ((-t / 2) / 7) hform
  · have ho : Odd t := not_even_iff_odd_int.mp he
    have hform := odd_phase_eq t ho
    have hs : phaseSign t = -1 := ite_eq_right he
    rw [hs, Int.cast_neg, Int.cast_one, neg_one_mul]
    exact exp_neg_pi_t_eq_neg_zeta t (phaseRes t).val (((7 - t) / 2) / 7) hform

lemma exp_centroid_eq_signed_zeta (n s q : Fin 3 → ℤ) :
    exp (2 * Real.pi * I * dot3 (qReal q) (centroidPoint n s)) =
      (phaseSign (signedWeight q s) : ℂ) *
        zeta7 ^ (phaseRes (signedWeight q s)).val := by
  rw [exp_centroid_int_q, exp_neg_pi_t_eq_signed_zeta]

/-! ## The cyclotomic phase polynomial -/

noncomputable def phasePoly {N : ℕ} (s : Fin N → Fin 3 → ℤ) (q : Fin 3 → ℤ) : ℤ[X] :=
  ∑ k : Fin N, C (phaseSign (signedWeight q (s k))) *
    X ^ (phaseRes (signedWeight q (s k))).val

lemma eval_phasePoly {N : ℕ} (s : Fin N → Fin 3 → ℤ) (q : Fin 3 → ℤ) (α : ℂ) :
    eval α ((phasePoly s q).map (Int.castRingHom ℂ)) =
      ∑ k : Fin N, (phaseSign (signedWeight q (s k)) : ℂ) *
        α ^ (phaseRes (signedWeight q (s k))).val := by
  unfold phasePoly
  rw [Polynomial.map_sum, eval_finsetSum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp

lemma sum_phase_eq_eval_phasePoly {N : ℕ}
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ) (q : Fin 3 → ℤ) :
    (∑ k : Fin N,
        exp (2 * Real.pi * I * dot3 (qReal q) (centroidPoint (n k) (s k)))) =
      eval zeta7 ((phasePoly s q).map (Int.castRingHom ℂ)) := by
  rw [eval_phasePoly]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact exp_centroid_eq_signed_zeta (n k) (s k) q

lemma phasePoly_eval_bound {N : ℕ} (s : Fin N → Fin 3 → ℤ) (q : Fin 3 → ℤ)
    {α : ℂ} (hα : ‖α‖ = 1) :
    ‖eval α ((phasePoly s q).map (Int.castRingHom ℂ))‖ ≤ N := by
  rw [eval_phasePoly]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ k : Fin N,
      ‖(phaseSign (signedWeight q (s k)) : ℂ) *
        α ^ (phaseRes (signedWeight q (s k))).val‖ = 1 := by
    intro k
    have hε := phaseSign_is_sign (signedWeight q (s k))
    have hsign : ‖(phaseSign (signedWeight q (s k)) : ℂ)‖ = 1 := by
      rcases hε with hε | hε <;> simp [hε]
    rw [norm_mul, hsign, one_mul, norm_pow, hα, one_pow]
  simp only [hterm, Finset.sum_const, Finset.card_univ, nsmul_one]
  exact le_of_eq (by simp)

lemma aeval_map_int_complex (p : ℤ[X]) (α : ℂ) :
    aeval α (p.map (Int.castRingHom ℚ)) =
      eval α (p.map (Int.castRingHom ℂ)) := by
  have h1 : Int.castRingHom ℚ = algebraMap ℤ ℚ := rfl
  rw [h1, aeval_map_algebraMap, aeval_def, ← eval_map]
  rfl

lemma aeval_cyclotomic7_zeta7 : aeval zeta7 (cyclotomic 7 ℚ) = 0 := by
  have hroot : (cyclotomic 7 ℂ).IsRoot zeta7 :=
    IsPrimitiveRoot.isRoot_cyclotomic (by decide : 0 < 7) isPrimitiveRoot_zeta7
  have hmap : (cyclotomic 7 ℚ).map (algebraMap ℚ ℂ) = cyclotomic 7 ℂ :=
    map_cyclotomic 7 (algebraMap ℚ ℂ)
  rw [aeval_def, ← eval_map, hmap, IsRoot.def.mp hroot]

lemma phasePoly_eval_ne_zero_of_primitive {N : ℕ}
    (s : Fin N → Fin 3 → ℤ) (q : Fin 3 → ℤ)
    (hS : eval zeta7 ((phasePoly s q).map (Int.castRingHom ℂ)) ≠ 0)
    {α : ℂ} (hα : IsPrimitiveRoot α 7) :
    eval α ((phasePoly s q).map (Int.castRingHom ℂ)) ≠ 0 := by
  intro hα0
  have hmin : minpoly ℚ α = cyclotomic 7 ℚ :=
    (cyclotomic_eq_minpoly_rat hα (by decide)).symm
  have hdiv : minpoly ℚ α ∣ (phasePoly s q).map (Int.castRingHom ℚ) := by
    refine minpoly.dvd ℚ α ?_
    rw [aeval_map_int_complex, hα0]
  have hdiv' : cyclotomic 7 ℚ ∣ (phasePoly s q).map (Int.castRingHom ℚ) := by
    rwa [hmin] at hdiv
  have hz0 : aeval zeta7 ((phasePoly s q).map (Int.castRingHom ℚ)) = 0 := by
    obtain ⟨r, hr⟩ := hdiv'
    rw [hr, map_mul, aeval_cyclotomic7_zeta7, zero_mul]
  have : eval zeta7 ((phasePoly s q).map (Int.castRingHom ℂ)) = 0 := by
    rwa [← aeval_map_int_complex]
  exact hS this

lemma cyclotomic7_complex_splits : (cyclotomic 7 ℂ).Splits :=
  IsAlgClosed.splits _

lemma zeta7_mem_cyclotomic_roots : zeta7 ∈ (cyclotomic 7 ℂ).roots := by
  rw [mem_roots (cyclotomic_ne_zero 7 ℂ), isRoot_cyclotomic_iff]
  exact isPrimitiveRoot_zeta7

lemma roots_are_primitive {α : ℂ} (hα : α ∈ (cyclotomic 7 ℂ).roots) :
    IsPrimitiveRoot α 7 := by
  rw [mem_roots (cyclotomic_ne_zero 7 ℂ), isRoot_cyclotomic_iff] at hα
  exact hα

lemma primitive_root_norm_one {α : ℂ} (hα : IsPrimitiveRoot α 7) : ‖α‖ = 1 :=
  IsPrimitiveRoot.norm'_eq_one hα (by decide)

lemma int_castHom_complex_injective :
    Function.Injective (Int.castRingHom ℂ) :=
  Int.cast_injective

lemma abs_resultant_phasePoly {N : ℕ}
    (s : Fin N → Fin 3 → ℤ) (q : Fin 3 → ℤ)
    (hS : eval zeta7 ((phasePoly s q).map (Int.castRingHom ℂ)) ≠ 0) :
    1 ≤ ‖eval zeta7 ((phasePoly s q).map (Int.castRingHom ℂ))‖ * (N : ℝ) ^ 5 := by
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
  have hprodFin :
      (ΦC.roots.map (fun α => eval α Pℂ)).prod =
        ∏ α ∈ primitiveRoots 7 ℂ, eval α Pℂ := by
    rw [hroots, Finset.prod_eq_multiset_prod]
  have hsplit :
      eval zeta7 Pℂ * ∏ α ∈ (primitiveRoots 7 ℂ).erase zeta7, eval α Pℂ =
        ∏ α ∈ primitiveRoots 7 ℂ, eval α Pℂ :=
    Finset.mul_prod_erase (primitiveRoots 7 ℂ) (fun α => eval α Pℂ) hζ
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
  have hcard : ((primitiveRoots 7 ℂ).erase zeta7).card = 5 := by
    have hcard0 : (primitiveRoots 7 ℂ).card = 6 := by
      have : ΦC.roots.card = 6 := by
        rw [← cyclotomic7_complex_splits.natDegree_eq_card_roots,
          natDegree_cyclotomic, Nat.totient_prime (by decide : Nat.Prime 7)]
      rw [hroots] at this
      exact this
    rw [Finset.card_erase_of_mem hζ, hcard0]
  have hbound : ∀ α ∈ (primitiveRoots 7 ℂ).erase zeta7,
      ‖eval α Pℂ‖ ≤ N := by
    intro α hα
    have hα' : α ∈ primitiveRoots 7 ℂ := Finset.mem_of_mem_erase hα
    have hprim : IsPrimitiveRoot α 7 :=
      (mem_primitiveRoots (by decide : 0 < 7)).mp hα'
    exact phasePoly_eval_bound s q (primitive_root_norm_one hprim)
  have hprodAbs :
      ‖∏ α ∈ primitiveRoots 7 ℂ, eval α Pℂ‖ =
        ‖eval zeta7 Pℂ‖ *
          ‖∏ α ∈ (primitiveRoots 7 ℂ).erase zeta7, eval α Pℂ‖ := by
    rw [← hsplit, norm_mul]
  have hrest :
      ‖∏ α ∈ (primitiveRoots 7 ℂ).erase zeta7, eval α Pℂ‖ ≤ (N : ℝ) ^ 5 := by
    rw [norm_prod]
    have hle :=
      Finset.prod_le_prod₀
        (fun _ _ => norm_nonneg _)
        (fun α hα => hbound α hα)
    have hNprod :
        ∏ _α ∈ (primitiveRoots 7 ℂ).erase zeta7, (N : ℝ) = (N : ℝ) ^ 5 := by
      simp [Finset.prod_const, hcard]
    rwa [hNprod] at hle
  have : 1 ≤ ‖eval zeta7 Pℂ‖ *
      ‖∏ α ∈ (primitiveRoots 7 ℂ).erase zeta7, eval α Pℂ‖ := by
    rw [← hprodAbs, ← hprodFin, hprod']
    exact habsRes
  nlinarith [hrest, norm_nonneg (eval zeta7 Pℂ)]

lemma abs_S_ge_inv_N_pow_five {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ) (q : Fin 3 → ℤ)
    (hS : (∑ k : Fin N,
        exp (2 * Real.pi * I * dot3 (qReal q) (centroidPoint (n k) (s k)))) ≠ 0) :
    (1 : ℝ) / (N : ℝ) ^ 5 ≤
      ‖(∑ k : Fin N,
          exp (2 * Real.pi * I * dot3 (qReal q) (centroidPoint (n k) (s k))))‖ := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have heval :
      (∑ k : Fin N,
          exp (2 * Real.pi * I * dot3 (qReal q) (centroidPoint (n k) (s k)))) =
        eval zeta7 ((phasePoly s q).map (Int.castRingHom ℂ)) :=
    sum_phase_eq_eval_phasePoly n s q
  have hS' : eval zeta7 ((phasePoly s q).map (Int.castRingHom ℂ)) ≠ 0 := by
    rwa [← heval]
  have hlb := abs_resultant_phasePoly s q hS'
  rw [heval]
  have hN5 : (0 : ℝ) < (N : ℝ) ^ 5 := by positivity
  exact (div_le_iff₀ hN5).mpr hlb

/-- `[P, Lean]` If `F ≠ 0` at an integer wavevector then `‖F‖ ≥ 1/N⁶`. -/
theorem norm_structureFactor_ge_inv_N_pow_six {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (_hs : ∀ k j, s k j = 1 ∨ s k j = -1)
    (qZ : Fin 3 → ℤ)
    (hF : structureFactor (fun k => centroidPoint (n k) (s k)) (qReal qZ) ≠ 0) :
    (1 : ℝ) / (N : ℝ) ^ 6 ≤
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
  have hSbound := abs_S_ge_inv_N_pow_five hN n s qZ hS0
  have hnorm : ‖structureFactor (fun k => centroidPoint (n k) (s k)) (qReal qZ)‖ =
      ‖S‖ / N := by
    rw [hSF, norm_mul, norm_inv, Complex.norm_natCast]
    field_simp [hNpos.ne']
  rw [hnorm]
  have heq : (1 : ℝ) / (N : ℝ) ^ 6 = ((1 : ℝ) / (N : ℝ) ^ 5) / N := by
    field_simp
  rw [heq]
  exact div_le_div_of_nonneg_right hSbound hNpos.le

theorem normSq_structureFactor_ge_inv_N_pow_twelve {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1)
    (qZ : Fin 3 → ℤ)
    (hF : structureFactor (fun k => centroidPoint (n k) (s k)) (qReal qZ) ≠ 0) :
    (1 : ℝ) / (N : ℝ) ^ 12 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) (qReal qZ)‖ ^ 2 := by
  have h := norm_structureFactor_ge_inv_N_pow_six hN n s hs qZ hF
  have hpos : 0 ≤ (1 : ℝ) / (N : ℝ) ^ 6 := by positivity
  have hpow := pow_le_pow_left₀ hpos h (n := 2)
  have hsq : ((1 : ℝ) / (N : ℝ) ^ 6) ^ 2 = (1 : ℝ) / (N : ℝ) ^ 12 := by
    field_simp
  rwa [hsq] at hpow

/-- Contrapositive: `‖F‖ < 1/N⁶` implies `F = 0`. -/
theorem structureFactor_eq_zero_of_norm_lt_inv_N_pow_six {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1)
    (qZ : Fin 3 → ℤ)
    (hlt : ‖structureFactor (fun k => centroidPoint (n k) (s k)) (qReal qZ)‖ <
      (1 : ℝ) / (N : ℝ) ^ 6) :
    structureFactor (fun k => centroidPoint (n k) (s k)) (qReal qZ) = 0 := by
  by_contra hF
  have := norm_structureFactor_ge_inv_N_pow_six hN n s hs qZ hF
  linarith

/-! ## Corollaries at (2,2,0) and (3,3,0)

These are weaker than the specialised cubic bounds of
LemmaDLowerBound220 (`1/(30 N³)`) and LemmaDLowerBound330 (`1/(65 N³)`).
-/

theorem norm_structureFactor_ge_inv_N_pow_six_at_220 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) (qReal qZ220)‖ :=
  norm_structureFactor_ge_inv_N_pow_six hN n s hs qZ220
    (structureFactor_ne_zero_at_220 hN n s hs)

theorem norm_structureFactor_ge_inv_N_pow_six_at_330 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) q330‖ := by
  simpa [q330] using
    norm_structureFactor_ge_inv_N_pow_six hN n s hs qZ330
      (structureFactor_ne_zero_at_330 hN n s hs)

#print axioms norm_structureFactor_ge_inv_N_pow_six
#print axioms normSq_structureFactor_ge_inv_N_pow_twelve
#print axioms structureFactor_eq_zero_of_norm_lt_inv_N_pow_six
#print axioms norm_structureFactor_ge_inv_N_pow_six_at_220
#print axioms norm_structureFactor_ge_inv_N_pow_six_at_330

end LeanLab.Scratch.LemmaDGeneralLowerBound
