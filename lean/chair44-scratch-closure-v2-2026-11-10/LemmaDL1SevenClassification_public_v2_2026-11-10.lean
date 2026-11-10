import LeanLab.Scratch.LemmaDGeneralLowerBound
import LeanLab.Scratch.LemmaDL1SevenMore
import LeanLab.Scratch.LemmaDOrbitNoZero
import LeanLab.Scratch.LemmaDNoZero310211

/-!
# Classification of integer q with ‖q‖₁ ≤ 7
(public-screen)

Public-screen v2 copy of LeanLab.Scratch.LemmaDL1SevenClassification (official pin src
`c26fbbd6ae052f49d3fe2d642b1c9d2bb413e1bce606cd5d2f8e7439b22f159a`).
Header redacted; theorem bodies are unchanged. This copy is not a
replacement pin.

**[P, Lean]** For every integer wavevector `q` with `|q₀|+|q₁|+|q₂| ≤ 7`,
exactly one of the following holds:

* **(a)** `F ≠ 0` for every nonempty finite equal-weight D-form box
  (hence `‖F‖ ≥ 1/N⁶` by LemmaDGeneralLowerBound);
* **(b)** `q` lies in the coordinate-permutation / coordinate-sign orbit
  of `(3,2,1)` or of `(4,2,1)`, and there exists an `N=7` equal-weight
  D-form box with `F=0`. The zero at `(4,2,1)` is imported from
  LemmaDL1SevenMore; the zero at `(3,2,1)` is replayed here from the
  standard 7-sign witness (all of `{±1}³` except `(−1,1,1)`). Zeros
  transfer along orbits via `structureFactor_orbit_pull` and a push
  inverse of `pullVec`.

**Argument.** The eight sign vectors determine a residue set `R(q) ⊆ Fin 7`
in the orientation of LemmaDGeneralLowerBound
(`k ≡ −t/2 (mod 7)` for even `t`, `k ≡ (7−t)/2 (mod 7)` for odd `t`).
Even / odd `‖q‖₁` makes every phase uniformly `ζ^k` or uniformly `−ζ^k`,
so a missing residue implies `F ≠ 0` by the existing cyclotomic
independence lemmas. Among the 31 sorted nonnegative representatives
with `L¹ ≤ 7`, `R(q)=univ` if and only if `q ∈ {(3,2,1),(4,2,1)}`
(checked by `decide`). Every integer `q` with `L¹ ≤ 7` is an orbit of
its nonnegative nonincreasing rearrangement.

**Residue check (Lean orientation):** `(5,1,0)` residues `{2,3,4,5}` miss `0`; `(6,0,0)` residues
`{3,4}`; `(6,1,0)` residues `{0,1,6}`; `(7,0,0)` residues `{0}`. A zero
coordinate does not enlarge the residue set.

**Not proved / out of scope:**
* Sharpness of the `1/N⁶` bound; specialised cubic bounds at `(2,2,0)`
  and `(3,3,0)` remain sharper.
* Nothing for `‖q‖₁ > 7`. D-form class only. Scratch; not a Lake target;
  not peer reviewed.

This file is source-only and is not a Lake package. It claims nothing
beyond the theorems stated below.

Dated 2026-11-10.
-/

namespace LeanLab.Scratch.LemmaDL1SevenClassification

open Complex Equiv Finset
open LeanLab.Scratch.LemmaD4 (dot3 structureFactor centroidPoint)
open LeanLab.Scratch.LemmaDIntVec
  (qReal signedWeight qL1 qL1_eq_sum_abs zeta7 isPrimitiveRoot_zeta7)
open LeanLab.Scratch.LemmaDNoZero310211
  (structureFactor_ne_zero_of_missing_residue)
open LeanLab.Scratch.LemmaDOrbitNoZero
  (structureFactor_ne_zero_of_missing_residue_neg
    signedWeight_even_iff_qL1_even signedWeight_odd_of_qL1_odd
    orbitQ pullVec pullVec_is_sign structureFactor_orbit_pull
    structureFactor_ne_zero_orbit_transfer)
open LeanLab.Scratch.LemmaDGeneralLowerBound
  (phaseRes phaseSign
    exp_centroid_eq_signed_zeta not_even_iff_odd_int
    norm_structureFactor_ge_inv_N_pow_six)
open LeanLab.Scratch.LemmaDL1SevenMore
  (qZ421 exists_box_structureFactor_eq_zero_at_421)

/-! ## Signs, residue sets, and the missing-residue criterion -/

def qOf (a b c : ℤ) : Fin 3 → ℤ
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b
  | ⟨2, _⟩ => c

/-- The eight sign vectors, indexed so that bit `j` of `k` is the sign of coordinate `j`
(`false ↦ -1`, `true ↦ 1`). -/
def allSigns : Fin 8 → Fin 3 → ℤ :=
  ![ ![-1, -1, -1], ![1, -1, -1], ![-1, 1, -1], ![1, 1, -1],
     ![-1, -1, 1], ![1, -1, 1], ![-1, 1, 1], ![1, 1, 1] ]

lemma allSigns_is_sign (k : Fin 8) (j : Fin 3) :
    allSigns k j = 1 ∨ allSigns k j = -1 := by
  fin_cases k <;> fin_cases j <;> simp [allSigns]

lemma exists_allSigns (s : Fin 3 → ℤ) (hs : ∀ j, s j = 1 ∨ s j = -1) :
    ∃ k : Fin 8, ∀ j, s j = allSigns k j := by
  have h0 := hs 0
  have h1 := hs 1
  have h2 := hs 2
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · refine ⟨⟨7, by decide⟩, ?_⟩
    intro j; fin_cases j <;> simp [allSigns, h0, h1, h2]
  · refine ⟨⟨3, by decide⟩, ?_⟩
    intro j; fin_cases j <;> simp [allSigns, h0, h1, h2]
  · refine ⟨⟨5, by decide⟩, ?_⟩
    intro j; fin_cases j <;> simp [allSigns, h0, h1, h2]
  · refine ⟨⟨1, by decide⟩, ?_⟩
    intro j; fin_cases j <;> simp [allSigns, h0, h1, h2]
  · refine ⟨⟨6, by decide⟩, ?_⟩
    intro j; fin_cases j <;> simp [allSigns, h0, h1, h2]
  · refine ⟨⟨2, by decide⟩, ?_⟩
    intro j; fin_cases j <;> simp [allSigns, h0, h1, h2]
  · refine ⟨⟨4, by decide⟩, ?_⟩
    intro j; fin_cases j <;> simp [allSigns, h0, h1, h2]
  · refine ⟨⟨0, by decide⟩, ?_⟩
    intro j; fin_cases j <;> simp [allSigns, h0, h1, h2]

def residueSet (q : Fin 3 → ℤ) : Finset (Fin 7) :=
  Finset.univ.image (fun k : Fin 8 => phaseRes (signedWeight q (allSigns k)))

lemma mem_residueSet_of_sign (q s : Fin 3 → ℤ)
    (hs : ∀ j, s j = 1 ∨ s j = -1) :
    phaseRes (signedWeight q s) ∈ residueSet q := by
  obtain ⟨k, hk⟩ := exists_allSigns s hs
  have hsw : signedWeight q s = signedWeight q (allSigns k) := by
    unfold signedWeight
    exact Finset.sum_congr rfl fun j _ => by rw [hk j]
  rw [hsw]
  exact Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩

lemma phaseSign_even {t : ℤ} (he : Even t) : phaseSign t = 1 :=
  ite_eq_left he

lemma phaseSign_odd {t : ℤ} (ho : Odd t) : phaseSign t = -1 :=
  ite_eq_right (not_even_iff_odd_int.mpr ho)

lemma exp_centroid_of_even_qL1 (n s q : Fin 3 → ℤ)
    (hs : ∀ j, s j = 1 ∨ s j = -1) (he : Even (qL1 q)) :
    exp (2 * Real.pi * I * dot3 (qReal q) (centroidPoint n s)) =
      zeta7 ^ (phaseRes (signedWeight q s)).val := by
  have ht : Even (signedWeight q s) :=
    (signedWeight_even_iff_qL1_even q s hs).mpr he
  have h := exp_centroid_eq_signed_zeta n s q
  rwa [phaseSign_even ht, Int.cast_one, one_mul] at h

lemma exp_centroid_of_odd_qL1 (n s q : Fin 3 → ℤ)
    (hs : ∀ j, s j = 1 ∨ s j = -1) (ho : Odd (qL1 q)) :
    exp (2 * Real.pi * I * dot3 (qReal q) (centroidPoint n s)) =
      -(zeta7 ^ (phaseRes (signedWeight q s)).val) := by
  have ht : Odd (signedWeight q s) := signedWeight_odd_of_qL1_odd q s hs ho
  have h := exp_centroid_eq_signed_zeta n s q
  rwa [phaseSign_odd ht, Int.cast_neg, Int.cast_one, neg_one_mul] at h

theorem structureFactor_ne_zero_of_missing_phaseRes {N : ℕ} (hN : 1 ≤ N)
    (qZ : Fin 3 → ℤ)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1)
    (r0 : Fin 7) (hmiss : r0 ∉ residueSet qZ) :
    structureFactor (fun k => centroidPoint (n k) (s k)) (qReal qZ) ≠ 0 := by
  have hmiss' : ∀ (s' : Fin 3 → ℤ), (∀ j, s' j = 1 ∨ s' j = -1) →
      phaseRes (signedWeight qZ s') ≠ r0 := by
    intro s' hs' heq
    exact hmiss (heq ▸ mem_residueSet_of_sign qZ s' hs')
  by_cases he : Even (qL1 qZ)
  · exact structureFactor_ne_zero_of_missing_residue hN qZ n s hs
      (fun s' => phaseRes (signedWeight qZ s'))
      (fun k => exp_centroid_of_even_qL1 (n k) (s k) qZ (hs k) he) r0 hmiss'
  · have ho : Odd (qL1 qZ) := Nat.not_even_iff_odd.mp he
    exact structureFactor_ne_zero_of_missing_residue_neg hN qZ n s hs
      (fun s' => phaseRes (signedWeight qZ s'))
      (fun k => exp_centroid_of_odd_qL1 (n k) (s k) qZ (hs k) ho) r0 hmiss'

theorem structureFactor_ne_zero_of_residueSet_ne_univ {N : ℕ} (hN : 1 ≤ N)
    (qZ : Fin 3 → ℤ)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1)
    (hR : residueSet qZ ≠ Finset.univ) :
    structureFactor (fun k => centroidPoint (n k) (s k)) (qReal qZ) ≠ 0 := by
  have : ∃ r : Fin 7, r ∉ residueSet qZ := by
    contrapose! hR
    exact Finset.eq_univ_iff_forall.mpr hR
  obtain ⟨r0, hr0⟩ := this
  exact structureFactor_ne_zero_of_missing_phaseRes hN qZ n s hs r0 hr0

/-! ## Non-vanishing at sorted nonnegative representatives except (3,2,1) and (4,2,1) -/

lemma miss_000 : (1 : Fin 7) ∉ residueSet (qOf 0 0 0) := by decide

theorem structureFactor_ne_zero_at_000 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    structureFactor (fun k => centroidPoint (n k) (s k)) (qReal (qOf 0 0 0)) ≠ 0 :=
  structureFactor_ne_zero_of_missing_phaseRes hN (qOf 0 0 0) n s hs
    ⟨1, by decide⟩ miss_000

theorem norm_ge_inv_N6_at_000 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) (qReal (qOf 0 0 0))‖ :=
  norm_structureFactor_ge_inv_N_pow_six hN n s hs (qOf 0 0 0)
    (structureFactor_ne_zero_at_000 hN n s hs)

lemma miss_100 : (0 : Fin 7) ∉ residueSet (qOf 1 0 0) := by decide

theorem structureFactor_ne_zero_at_100 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    structureFactor (fun k => centroidPoint (n k) (s k)) (qReal (qOf 1 0 0)) ≠ 0 :=
  structureFactor_ne_zero_of_missing_phaseRes hN (qOf 1 0 0) n s hs
    ⟨0, by decide⟩ miss_100

theorem norm_ge_inv_N6_at_100 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) (qReal (qOf 1 0 0))‖ :=
  norm_structureFactor_ge_inv_N_pow_six hN n s hs (qOf 1 0 0)
    (structureFactor_ne_zero_at_100 hN n s hs)

lemma miss_200 : (0 : Fin 7) ∉ residueSet (qOf 2 0 0) := by decide

theorem structureFactor_ne_zero_at_200 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    structureFactor (fun k => centroidPoint (n k) (s k)) (qReal (qOf 2 0 0)) ≠ 0 :=
  structureFactor_ne_zero_of_missing_phaseRes hN (qOf 2 0 0) n s hs
    ⟨0, by decide⟩ miss_200

theorem norm_ge_inv_N6_at_200 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) (qReal (qOf 2 0 0))‖ :=
  norm_structureFactor_ge_inv_N_pow_six hN n s hs (qOf 2 0 0)
    (structureFactor_ne_zero_at_200 hN n s hs)

lemma miss_110 : (2 : Fin 7) ∉ residueSet (qOf 1 1 0) := by decide

theorem structureFactor_ne_zero_at_110 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    structureFactor (fun k => centroidPoint (n k) (s k)) (qReal (qOf 1 1 0)) ≠ 0 :=
  structureFactor_ne_zero_of_missing_phaseRes hN (qOf 1 1 0) n s hs
    ⟨2, by decide⟩ miss_110

theorem norm_ge_inv_N6_at_110 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) (qReal (qOf 1 1 0))‖ :=
  norm_structureFactor_ge_inv_N_pow_six hN n s hs (qOf 1 1 0)
    (structureFactor_ne_zero_at_110 hN n s hs)

lemma miss_300 : (0 : Fin 7) ∉ residueSet (qOf 3 0 0) := by decide

theorem structureFactor_ne_zero_at_300 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    structureFactor (fun k => centroidPoint (n k) (s k)) (qReal (qOf 3 0 0)) ≠ 0 :=
  structureFactor_ne_zero_of_missing_phaseRes hN (qOf 3 0 0) n s hs
    ⟨0, by decide⟩ miss_300

theorem norm_ge_inv_N6_at_300 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) (qReal (qOf 3 0 0))‖ :=
  norm_structureFactor_ge_inv_N_pow_six hN n s hs (qOf 3 0 0)
    (structureFactor_ne_zero_at_300 hN n s hs)

lemma miss_210 : (0 : Fin 7) ∉ residueSet (qOf 2 1 0) := by decide

theorem structureFactor_ne_zero_at_210 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    structureFactor (fun k => centroidPoint (n k) (s k)) (qReal (qOf 2 1 0)) ≠ 0 :=
  structureFactor_ne_zero_of_missing_phaseRes hN (qOf 2 1 0) n s hs
    ⟨0, by decide⟩ miss_210

theorem norm_ge_inv_N6_at_210 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) (qReal (qOf 2 1 0))‖ :=
  norm_structureFactor_ge_inv_N_pow_six hN n s hs (qOf 2 1 0)
    (structureFactor_ne_zero_at_210 hN n s hs)

lemma miss_111 : (0 : Fin 7) ∉ residueSet (qOf 1 1 1) := by decide

theorem structureFactor_ne_zero_at_111 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    structureFactor (fun k => centroidPoint (n k) (s k)) (qReal (qOf 1 1 1)) ≠ 0 :=
  structureFactor_ne_zero_of_missing_phaseRes hN (qOf 1 1 1) n s hs
    ⟨0, by decide⟩ miss_111

theorem norm_ge_inv_N6_at_111 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) (qReal (qOf 1 1 1))‖ :=
  norm_structureFactor_ge_inv_N_pow_six hN n s hs (qOf 1 1 1)
    (structureFactor_ne_zero_at_111 hN n s hs)

lemma miss_400 : (0 : Fin 7) ∉ residueSet (qOf 4 0 0) := by decide

theorem structureFactor_ne_zero_at_400 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    structureFactor (fun k => centroidPoint (n k) (s k)) (qReal (qOf 4 0 0)) ≠ 0 :=
  structureFactor_ne_zero_of_missing_phaseRes hN (qOf 4 0 0) n s hs
    ⟨0, by decide⟩ miss_400

theorem norm_ge_inv_N6_at_400 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) (qReal (qOf 4 0 0))‖ :=
  norm_structureFactor_ge_inv_N_pow_six hN n s hs (qOf 4 0 0)
    (structureFactor_ne_zero_at_400 hN n s hs)

lemma miss_310 : (0 : Fin 7) ∉ residueSet (qOf 3 1 0) := by decide

theorem structureFactor_ne_zero_at_310 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    structureFactor (fun k => centroidPoint (n k) (s k)) (qReal (qOf 3 1 0)) ≠ 0 :=
  structureFactor_ne_zero_of_missing_phaseRes hN (qOf 3 1 0) n s hs
    ⟨0, by decide⟩ miss_310

theorem norm_ge_inv_N6_at_310 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) (qReal (qOf 3 1 0))‖ :=
  norm_structureFactor_ge_inv_N_pow_six hN n s hs (qOf 3 1 0)
    (structureFactor_ne_zero_at_310 hN n s hs)

lemma miss_220 : (1 : Fin 7) ∉ residueSet (qOf 2 2 0) := by decide

theorem structureFactor_ne_zero_at_220 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    structureFactor (fun k => centroidPoint (n k) (s k)) (qReal (qOf 2 2 0)) ≠ 0 :=
  structureFactor_ne_zero_of_missing_phaseRes hN (qOf 2 2 0) n s hs
    ⟨1, by decide⟩ miss_220

theorem norm_ge_inv_N6_at_220 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) (qReal (qOf 2 2 0))‖ :=
  norm_structureFactor_ge_inv_N_pow_six hN n s hs (qOf 2 2 0)
    (structureFactor_ne_zero_at_220 hN n s hs)

lemma miss_211 : (3 : Fin 7) ∉ residueSet (qOf 2 1 1) := by decide

theorem structureFactor_ne_zero_at_211 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    structureFactor (fun k => centroidPoint (n k) (s k)) (qReal (qOf 2 1 1)) ≠ 0 :=
  structureFactor_ne_zero_of_missing_phaseRes hN (qOf 2 1 1) n s hs
    ⟨3, by decide⟩ miss_211

theorem norm_ge_inv_N6_at_211 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) (qReal (qOf 2 1 1))‖ :=
  norm_structureFactor_ge_inv_N_pow_six hN n s hs (qOf 2 1 1)
    (structureFactor_ne_zero_at_211 hN n s hs)

lemma miss_500 : (0 : Fin 7) ∉ residueSet (qOf 5 0 0) := by decide

theorem structureFactor_ne_zero_at_500 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    structureFactor (fun k => centroidPoint (n k) (s k)) (qReal (qOf 5 0 0)) ≠ 0 :=
  structureFactor_ne_zero_of_missing_phaseRes hN (qOf 5 0 0) n s hs
    ⟨0, by decide⟩ miss_500

theorem norm_ge_inv_N6_at_500 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) (qReal (qOf 5 0 0))‖ :=
  norm_structureFactor_ge_inv_N_pow_six hN n s hs (qOf 5 0 0)
    (structureFactor_ne_zero_at_500 hN n s hs)

lemma miss_410 : (0 : Fin 7) ∉ residueSet (qOf 4 1 0) := by decide

theorem structureFactor_ne_zero_at_410 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    structureFactor (fun k => centroidPoint (n k) (s k)) (qReal (qOf 4 1 0)) ≠ 0 :=
  structureFactor_ne_zero_of_missing_phaseRes hN (qOf 4 1 0) n s hs
    ⟨0, by decide⟩ miss_410

theorem norm_ge_inv_N6_at_410 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) (qReal (qOf 4 1 0))‖ :=
  norm_structureFactor_ge_inv_N_pow_six hN n s hs (qOf 4 1 0)
    (structureFactor_ne_zero_at_410 hN n s hs)

lemma miss_320 : (0 : Fin 7) ∉ residueSet (qOf 3 2 0) := by decide

theorem structureFactor_ne_zero_at_320 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    structureFactor (fun k => centroidPoint (n k) (s k)) (qReal (qOf 3 2 0)) ≠ 0 :=
  structureFactor_ne_zero_of_missing_phaseRes hN (qOf 3 2 0) n s hs
    ⟨0, by decide⟩ miss_320

theorem norm_ge_inv_N6_at_320 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) (qReal (qOf 3 2 0))‖ :=
  norm_structureFactor_ge_inv_N_pow_six hN n s hs (qOf 3 2 0)
    (structureFactor_ne_zero_at_320 hN n s hs)

lemma miss_311 : (0 : Fin 7) ∉ residueSet (qOf 3 1 1) := by decide

theorem structureFactor_ne_zero_at_311 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    structureFactor (fun k => centroidPoint (n k) (s k)) (qReal (qOf 3 1 1)) ≠ 0 :=
  structureFactor_ne_zero_of_missing_phaseRes hN (qOf 3 1 1) n s hs
    ⟨0, by decide⟩ miss_311

theorem norm_ge_inv_N6_at_311 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) (qReal (qOf 3 1 1))‖ :=
  norm_structureFactor_ge_inv_N_pow_six hN n s hs (qOf 3 1 1)
    (structureFactor_ne_zero_at_311 hN n s hs)

lemma miss_221 : (0 : Fin 7) ∉ residueSet (qOf 2 2 1) := by decide

theorem structureFactor_ne_zero_at_221 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    structureFactor (fun k => centroidPoint (n k) (s k)) (qReal (qOf 2 2 1)) ≠ 0 :=
  structureFactor_ne_zero_of_missing_phaseRes hN (qOf 2 2 1) n s hs
    ⟨0, by decide⟩ miss_221

theorem norm_ge_inv_N6_at_221 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) (qReal (qOf 2 2 1))‖ :=
  norm_structureFactor_ge_inv_N_pow_six hN n s hs (qOf 2 2 1)
    (structureFactor_ne_zero_at_221 hN n s hs)

lemma miss_600 : (0 : Fin 7) ∉ residueSet (qOf 6 0 0) := by decide

theorem structureFactor_ne_zero_at_600 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    structureFactor (fun k => centroidPoint (n k) (s k)) (qReal (qOf 6 0 0)) ≠ 0 :=
  structureFactor_ne_zero_of_missing_phaseRes hN (qOf 6 0 0) n s hs
    ⟨0, by decide⟩ miss_600

theorem norm_ge_inv_N6_at_600 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) (qReal (qOf 6 0 0))‖ :=
  norm_structureFactor_ge_inv_N_pow_six hN n s hs (qOf 6 0 0)
    (structureFactor_ne_zero_at_600 hN n s hs)

lemma miss_510 : (0 : Fin 7) ∉ residueSet (qOf 5 1 0) := by decide

theorem structureFactor_ne_zero_at_510 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    structureFactor (fun k => centroidPoint (n k) (s k)) (qReal (qOf 5 1 0)) ≠ 0 :=
  structureFactor_ne_zero_of_missing_phaseRes hN (qOf 5 1 0) n s hs
    ⟨0, by decide⟩ miss_510

theorem norm_ge_inv_N6_at_510 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) (qReal (qOf 5 1 0))‖ :=
  norm_structureFactor_ge_inv_N_pow_six hN n s hs (qOf 5 1 0)
    (structureFactor_ne_zero_at_510 hN n s hs)

lemma miss_420 : (0 : Fin 7) ∉ residueSet (qOf 4 2 0) := by decide

theorem structureFactor_ne_zero_at_420 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    structureFactor (fun k => centroidPoint (n k) (s k)) (qReal (qOf 4 2 0)) ≠ 0 :=
  structureFactor_ne_zero_of_missing_phaseRes hN (qOf 4 2 0) n s hs
    ⟨0, by decide⟩ miss_420

theorem norm_ge_inv_N6_at_420 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) (qReal (qOf 4 2 0))‖ :=
  norm_structureFactor_ge_inv_N_pow_six hN n s hs (qOf 4 2 0)
    (structureFactor_ne_zero_at_420 hN n s hs)

lemma miss_411 : (0 : Fin 7) ∉ residueSet (qOf 4 1 1) := by decide

theorem structureFactor_ne_zero_at_411 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    structureFactor (fun k => centroidPoint (n k) (s k)) (qReal (qOf 4 1 1)) ≠ 0 :=
  structureFactor_ne_zero_of_missing_phaseRes hN (qOf 4 1 1) n s hs
    ⟨0, by decide⟩ miss_411

theorem norm_ge_inv_N6_at_411 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) (qReal (qOf 4 1 1))‖ :=
  norm_structureFactor_ge_inv_N_pow_six hN n s hs (qOf 4 1 1)
    (structureFactor_ne_zero_at_411 hN n s hs)

lemma miss_330 : (1 : Fin 7) ∉ residueSet (qOf 3 3 0) := by decide

theorem structureFactor_ne_zero_at_330 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    structureFactor (fun k => centroidPoint (n k) (s k)) (qReal (qOf 3 3 0)) ≠ 0 :=
  structureFactor_ne_zero_of_missing_phaseRes hN (qOf 3 3 0) n s hs
    ⟨1, by decide⟩ miss_330

theorem norm_ge_inv_N6_at_330 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) (qReal (qOf 3 3 0))‖ :=
  norm_structureFactor_ge_inv_N_pow_six hN n s hs (qOf 3 3 0)
    (structureFactor_ne_zero_at_330 hN n s hs)

lemma miss_222 : (0 : Fin 7) ∉ residueSet (qOf 2 2 2) := by decide

theorem structureFactor_ne_zero_at_222 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    structureFactor (fun k => centroidPoint (n k) (s k)) (qReal (qOf 2 2 2)) ≠ 0 :=
  structureFactor_ne_zero_of_missing_phaseRes hN (qOf 2 2 2) n s hs
    ⟨0, by decide⟩ miss_222

theorem norm_ge_inv_N6_at_222 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) (qReal (qOf 2 2 2))‖ :=
  norm_structureFactor_ge_inv_N_pow_six hN n s hs (qOf 2 2 2)
    (structureFactor_ne_zero_at_222 hN n s hs)

lemma miss_700 : (1 : Fin 7) ∉ residueSet (qOf 7 0 0) := by decide

theorem structureFactor_ne_zero_at_700 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    structureFactor (fun k => centroidPoint (n k) (s k)) (qReal (qOf 7 0 0)) ≠ 0 :=
  structureFactor_ne_zero_of_missing_phaseRes hN (qOf 7 0 0) n s hs
    ⟨1, by decide⟩ miss_700

theorem norm_ge_inv_N6_at_700 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) (qReal (qOf 7 0 0))‖ :=
  norm_structureFactor_ge_inv_N_pow_six hN n s hs (qOf 7 0 0)
    (structureFactor_ne_zero_at_700 hN n s hs)

lemma miss_610 : (2 : Fin 7) ∉ residueSet (qOf 6 1 0) := by decide

theorem structureFactor_ne_zero_at_610 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    structureFactor (fun k => centroidPoint (n k) (s k)) (qReal (qOf 6 1 0)) ≠ 0 :=
  structureFactor_ne_zero_of_missing_phaseRes hN (qOf 6 1 0) n s hs
    ⟨2, by decide⟩ miss_610

theorem norm_ge_inv_N6_at_610 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) (qReal (qOf 6 1 0))‖ :=
  norm_structureFactor_ge_inv_N_pow_six hN n s hs (qOf 6 1 0)
    (structureFactor_ne_zero_at_610 hN n s hs)

lemma miss_520 : (1 : Fin 7) ∉ residueSet (qOf 5 2 0) := by decide

theorem structureFactor_ne_zero_at_520 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    structureFactor (fun k => centroidPoint (n k) (s k)) (qReal (qOf 5 2 0)) ≠ 0 :=
  structureFactor_ne_zero_of_missing_phaseRes hN (qOf 5 2 0) n s hs
    ⟨1, by decide⟩ miss_520

theorem norm_ge_inv_N6_at_520 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) (qReal (qOf 5 2 0))‖ :=
  norm_structureFactor_ge_inv_N_pow_six hN n s hs (qOf 5 2 0)
    (structureFactor_ne_zero_at_520 hN n s hs)

lemma miss_511 : (3 : Fin 7) ∉ residueSet (qOf 5 1 1) := by decide

theorem structureFactor_ne_zero_at_511 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    structureFactor (fun k => centroidPoint (n k) (s k)) (qReal (qOf 5 1 1)) ≠ 0 :=
  structureFactor_ne_zero_of_missing_phaseRes hN (qOf 5 1 1) n s hs
    ⟨3, by decide⟩ miss_511

theorem norm_ge_inv_N6_at_511 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) (qReal (qOf 5 1 1))‖ :=
  norm_structureFactor_ge_inv_N_pow_six hN n s hs (qOf 5 1 1)
    (structureFactor_ne_zero_at_511 hN n s hs)

lemma miss_430 : (1 : Fin 7) ∉ residueSet (qOf 4 3 0) := by decide

theorem structureFactor_ne_zero_at_430 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    structureFactor (fun k => centroidPoint (n k) (s k)) (qReal (qOf 4 3 0)) ≠ 0 :=
  structureFactor_ne_zero_of_missing_phaseRes hN (qOf 4 3 0) n s hs
    ⟨1, by decide⟩ miss_430

theorem norm_ge_inv_N6_at_430 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) (qReal (qOf 4 3 0))‖ :=
  norm_structureFactor_ge_inv_N_pow_six hN n s hs (qOf 4 3 0)
    (structureFactor_ne_zero_at_430 hN n s hs)

lemma miss_331 : (2 : Fin 7) ∉ residueSet (qOf 3 3 1) := by decide

theorem structureFactor_ne_zero_at_331 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    structureFactor (fun k => centroidPoint (n k) (s k)) (qReal (qOf 3 3 1)) ≠ 0 :=
  structureFactor_ne_zero_of_missing_phaseRes hN (qOf 3 3 1) n s hs
    ⟨2, by decide⟩ miss_331

theorem norm_ge_inv_N6_at_331 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) (qReal (qOf 3 3 1))‖ :=
  norm_structureFactor_ge_inv_N_pow_six hN n s hs (qOf 3 3 1)
    (structureFactor_ne_zero_at_331 hN n s hs)

lemma miss_322 : (1 : Fin 7) ∉ residueSet (qOf 3 2 2) := by decide

theorem structureFactor_ne_zero_at_322 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    structureFactor (fun k => centroidPoint (n k) (s k)) (qReal (qOf 3 2 2)) ≠ 0 :=
  structureFactor_ne_zero_of_missing_phaseRes hN (qOf 3 2 2) n s hs
    ⟨1, by decide⟩ miss_322

theorem norm_ge_inv_N6_at_322 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    (1 : ℝ) / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) (qReal (qOf 3 2 2))‖ :=
  norm_structureFactor_ge_inv_N_pow_six hN n s hs (qOf 3 2 2)
    (structureFactor_ne_zero_at_322 hN n s hs)

/-! ## Zero witnesses at (3,2,1) and (4,2,1) -/

def qZ321 : Fin 3 → ℤ := qOf 3 2 1

lemma qZ421_eq : qZ421 = qOf 4 2 1 := by
  ext j; fin_cases j <;> simp [qZ421, qOf]

lemma residueSet_321 : residueSet qZ321 = Finset.univ := by decide

lemma residueSet_421 : residueSet qZ421 = Finset.univ := by decide

def s321 : Fin 7 → Fin 3 → ℤ
  | ⟨0, _⟩ => fun | ⟨0, _⟩ => 1 | ⟨1, _⟩ => -1 | ⟨2, _⟩ => -1
  | ⟨1, _⟩ => fun | ⟨0, _⟩ => -1 | ⟨1, _⟩ => 1 | ⟨2, _⟩ => -1
  | ⟨2, _⟩ => fun | ⟨0, _⟩ => -1 | ⟨1, _⟩ => -1 | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => fun | ⟨0, _⟩ => -1 | ⟨1, _⟩ => -1 | ⟨2, _⟩ => -1
  | ⟨4, _⟩ => fun | ⟨0, _⟩ => 1 | ⟨1, _⟩ => 1 | ⟨2, _⟩ => 1
  | ⟨5, _⟩ => fun | ⟨0, _⟩ => 1 | ⟨1, _⟩ => 1 | ⟨2, _⟩ => -1
  | ⟨6, _⟩ => fun | ⟨0, _⟩ => 1 | ⟨1, _⟩ => -1 | ⟨2, _⟩ => 1

def n321 : Fin 7 → Fin 3 → ℤ := fun _ _ => 0

lemma hs321 (k : Fin 7) (j : Fin 3) : s321 k j = 1 ∨ s321 k j = -1 := by
  fin_cases k <;> fin_cases j <;> simp [s321]

lemma qL1_321_even : Even (qL1 qZ321) := by
  simp [qL1, qZ321, qOf, Fin.sum_univ_three]
  decide

lemma phaseRes_s321 (k : Fin 7) :
    phaseRes (signedWeight qZ321 (s321 k)) = k := by
  fin_cases k <;> decide

lemma sum_zeta7_fin : (∑ k : Fin 7, zeta7 ^ k.val) = 0 := by
  have hrange : (∑ i ∈ range 7, zeta7 ^ i) = 0 :=
    IsPrimitiveRoot.geom_sum_eq_zero isPrimitiveRoot_zeta7 (by decide)
  rw [Fin.sum_univ_eq_sum_range (fun i => zeta7 ^ i), hrange]

lemma sum_phase_s321 :
    (∑ k : Fin 7,
        exp (2 * Real.pi * I * dot3 (qReal qZ321) (centroidPoint (n321 k) (s321 k)))) =
      0 := by
  have hphase : ∀ k : Fin 7,
      exp (2 * Real.pi * I * dot3 (qReal qZ321) (centroidPoint (n321 k) (s321 k))) =
        zeta7 ^ (phaseRes (signedWeight qZ321 (s321 k))).val :=
    fun k => exp_centroid_of_even_qL1 (n321 k) (s321 k) qZ321 (hs321 k) qL1_321_even
  rw [Finset.sum_congr rfl fun k _ => hphase k]
  simp [phaseRes_s321, sum_zeta7_fin]

theorem exists_box_structureFactor_eq_zero_at_321 :
    ∃ (n : Fin 7 → Fin 3 → ℤ) (s : Fin 7 → Fin 3 → ℤ)
      (_hs : ∀ k j, s k j = 1 ∨ s k j = -1),
      structureFactor (fun k => centroidPoint (n k) (s k)) (qReal qZ321) = 0 := by
  refine ⟨n321, s321, hs321, ?_⟩
  unfold structureFactor
  rw [sum_phase_s321, mul_zero]

/-! ## Push / pull and zero transfer along orbits -/

def pushVec (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ) (v : Fin 3 → ℤ) :
    Fin 3 → ℤ :=
  fun j => eps j * v (σ j)

lemma pull_push (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1) (v : Fin 3 → ℤ) :
    pullVec σ eps (pushVec σ eps v) = v := by
  ext i
  unfold pullVec pushVec
  have : σ (σ.symm i) = i := Equiv.apply_symm_apply _ _
  rcases heps (σ.symm i) with h | h <;> simp [h, this]

lemma pushVec_is_sign (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (s : Fin 3 → ℤ) (hs : ∀ j, s j = 1 ∨ s j = -1) :
    ∀ j, pushVec σ eps s j = 1 ∨ pushVec σ eps s j = -1 := by
  intro j
  unfold pushVec
  rcases heps j with he | he <;> rcases hs (σ j) with hs' | hs' <;> simp [he, hs']

lemma structureFactor_orbit_push {N : ℕ}
    (q : Fin 3 → ℤ) (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ) :
    structureFactor (fun k => centroidPoint (n k) (s k)) (qReal q) =
      structureFactor
        (fun k => centroidPoint (pushVec σ eps (n k)) (pushVec σ eps (s k)))
        (qReal (orbitQ q σ eps)) := by
  have h := structureFactor_orbit_pull q σ eps heps
    (fun k => pushVec σ eps (n k)) (fun k => pushVec σ eps (s k))
  simpa [pull_push σ eps heps] using h

theorem exists_box_eq_zero_of_orbit {N : ℕ}
    (q : Fin 3 → ℤ) (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1)
    (hF : structureFactor (fun k => centroidPoint (n k) (s k)) (qReal q) = 0) :
    ∃ (n' : Fin N → Fin 3 → ℤ) (s' : Fin N → Fin 3 → ℤ)
      (_hs' : ∀ k j, s' k j = 1 ∨ s' k j = -1),
      structureFactor (fun k => centroidPoint (n' k) (s' k))
        (qReal (orbitQ q σ eps)) = 0 := by
  refine ⟨fun k => pushVec σ eps (n k), fun k => pushVec σ eps (s k),
    fun k => pushVec_is_sign σ eps heps (s k) (hs k), ?_⟩
  rw [← structureFactor_orbit_push q σ eps heps n s, hF]

theorem exists_box_structureFactor_eq_zero_of_orbit_321_or_421
    (q : Fin 3 → ℤ)
    (h : (∃ σ eps, (∀ j, eps j = 1 ∨ eps j = -1) ∧ orbitQ qZ321 σ eps = q) ∨
      (∃ σ eps, (∀ j, eps j = 1 ∨ eps j = -1) ∧ orbitQ qZ421 σ eps = q)) :
    ∃ (n : Fin 7 → Fin 3 → ℤ) (s : Fin 7 → Fin 3 → ℤ)
      (_hs : ∀ k j, s k j = 1 ∨ s k j = -1),
      structureFactor (fun k => centroidPoint (n k) (s k)) (qReal q) = 0 := by
  rcases h with ⟨σ, eps, heps, rfl⟩ | ⟨σ, eps, heps, rfl⟩
  · obtain ⟨n, s, hs, hF⟩ := exists_box_structureFactor_eq_zero_at_321
    exact exists_box_eq_zero_of_orbit qZ321 σ eps heps n s hs hF
  · obtain ⟨n, s, hs, hF⟩ := exists_box_structureFactor_eq_zero_at_421
    exact exists_box_eq_zero_of_orbit qZ421 σ eps heps n s hs hF

/-! ## Every q is an orbit of a nonnegative nonincreasing rearrangement -/

def signZ (n : ℤ) : ℤ := if 0 ≤ n then 1 else -1

lemma signZ_is_sign (n : ℤ) : signZ n = 1 ∨ signZ n = -1 := by
  unfold signZ; split_ifs <;> simp

lemma signZ_mul_abs (n : ℤ) : signZ n * |n| = n := by
  unfold signZ
  split_ifs with h
  · rw [abs_of_nonneg h, one_mul]
  · have : n < 0 := lt_of_not_ge h
    rw [abs_of_neg this]; ring

def perm012 : Equiv.Perm (Fin 3) := Equiv.refl _
def perm021 : Equiv.Perm (Fin 3) := Equiv.swap 1 2
def perm102 : Equiv.Perm (Fin 3) := Equiv.swap 0 1
def perm120 : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2
def perm201 : Equiv.Perm (Fin 3) := Equiv.swap 0 2 * Equiv.swap 1 2
def perm210 : Equiv.Perm (Fin 3) := Equiv.swap 0 2

lemma perm012_apply : perm012 0 = 0 ∧ perm012 1 = 1 ∧ perm012 2 = 2 := by
  simp [perm012]

lemma perm021_apply : perm021 0 = 0 ∧ perm021 1 = 2 ∧ perm021 2 = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · exact Equiv.swap_apply_of_ne_of_ne (by decide : (0 : Fin 3) ≠ 1)
      (by decide : (0 : Fin 3) ≠ 2)
  · exact Equiv.swap_apply_left 1 2
  · exact Equiv.swap_apply_right 1 2

lemma perm102_apply : perm102 0 = 1 ∧ perm102 1 = 0 ∧ perm102 2 = 2 := by
  refine ⟨?_, ?_, ?_⟩
  · exact Equiv.swap_apply_left 0 1
  · exact Equiv.swap_apply_right 0 1
  · exact Equiv.swap_apply_of_ne_of_ne (by decide : (2 : Fin 3) ≠ 0)
      (by decide : (2 : Fin 3) ≠ 1)

lemma perm210_apply : perm210 0 = 2 ∧ perm210 1 = 1 ∧ perm210 2 = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · exact Equiv.swap_apply_left 0 2
  · exact Equiv.swap_apply_of_ne_of_ne (by decide : (1 : Fin 3) ≠ 0)
      (by decide : (1 : Fin 3) ≠ 2)
  · exact Equiv.swap_apply_right 0 2

lemma perm120_apply : perm120 0 = 1 ∧ perm120 1 = 2 ∧ perm120 2 = 0 := by
  constructor
  · -- (swap 0 1) ((swap 1 2) 0) = (swap 0 1) 0 = 1
    simp [perm120, Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne (by decide : (0 : Fin 3) ≠ 1)
        (by decide : (0 : Fin 3) ≠ 2), Equiv.swap_apply_left]
  constructor
  · -- (swap 0 1) ((swap 1 2) 1) = (swap 0 1) 2 = 2
    simp [perm120, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne (by decide : (2 : Fin 3) ≠ 0)
        (by decide : (2 : Fin 3) ≠ 1)]
  · -- (swap 0 1) ((swap 1 2) 2) = (swap 0 1) 1 = 0
    simp [perm120, Equiv.Perm.mul_apply, Equiv.swap_apply_right]

lemma perm201_apply : perm201 0 = 2 ∧ perm201 1 = 0 ∧ perm201 2 = 1 := by
  constructor
  · -- (swap 0 2) ((swap 1 2) 0) = (swap 0 2) 0 = 2
    simp [perm201, Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne (by decide : (0 : Fin 3) ≠ 1)
        (by decide : (0 : Fin 3) ≠ 2), Equiv.swap_apply_left]
  constructor
  · -- (swap 0 2) ((swap 1 2) 1) = (swap 0 2) 2 = 0
    simp [perm201, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_right]
  · -- (swap 0 2) ((swap 1 2) 2) = (swap 0 2) 1 = 1
    simp [perm201, Equiv.Perm.mul_apply, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne (by decide : (1 : Fin 3) ≠ 0)
        (by decide : (1 : Fin 3) ≠ 2)]

lemma exists_sort_perm (q : Fin 3 → ℤ) :
    ∃ σ : Equiv.Perm (Fin 3),
      |q (σ 0)| ≥ |q (σ 1)| ∧ |q (σ 1)| ≥ |q (σ 2)| := by
  rcases le_total |q 1| |q 0| with h10 | h01
  · rcases le_total |q 2| |q 1| with h21 | h12
    · exact ⟨perm012, by simp [perm012_apply, h10, h21]⟩
    · rcases le_total |q 2| |q 0| with h20 | h02
      · exact ⟨perm021, by simp [perm021_apply, h20, h12]⟩
      · exact ⟨perm201, by simp [perm201_apply, h02, h10]⟩
  · rcases le_total |q 2| |q 0| with h20 | h02
    · exact ⟨perm102, by simp [perm102_apply, h01, h20]⟩
    · rcases le_total |q 1| |q 2| with h12 | h21
      · exact ⟨perm210, by simp [perm210_apply, h12, h01]⟩
      · exact ⟨perm120, by simp [perm120_apply, h21, h02]⟩

def canon (q : Fin 3 → ℤ) (σ : Equiv.Perm (Fin 3)) : Fin 3 → ℤ :=
  fun j => |q (σ j)|

lemma orbit_canon (q : Fin 3 → ℤ) (σ : Equiv.Perm (Fin 3)) :
    orbitQ (canon q σ) σ.symm (fun j => signZ (q j)) = q := by
  ext j
  unfold orbitQ canon
  simp [signZ_mul_abs (q j)]

lemma canon_noninc (q : Fin 3 → ℤ) {σ : Equiv.Perm (Fin 3)}
    (hσ : |q (σ 0)| ≥ |q (σ 1)| ∧ |q (σ 1)| ≥ |q (σ 2)|) :
    0 ≤ canon q σ 2 ∧ canon q σ 2 ≤ canon q σ 1 ∧ canon q σ 1 ≤ canon q σ 0 := by
  unfold canon
  have h2 : 0 ≤ |q (σ 2)| := abs_nonneg _
  exact ⟨h2, hσ.2, hσ.1⟩

lemma canon_qL1 (q : Fin 3 → ℤ) (σ : Equiv.Perm (Fin 3)) :
    qL1 (canon q σ) = qL1 q := by
  unfold canon qL1
  simp [Int.natAbs_abs]
  exact Equiv.sum_comp σ (fun i => (q i).natAbs)

/-- The 31 sorted nonnegative representatives with `L¹ ≤ 7`. -/
def isSortedRep (q : Fin 3 → ℤ) : Prop :=
  0 ≤ q 2 ∧ q 2 ≤ q 1 ∧ q 1 ≤ q 0 ∧ qL1 q ≤ 7

lemma isSortedRep_canon {q : Fin 3 → ℤ} (hq : qL1 q ≤ 7)
    {σ : Equiv.Perm (Fin 3)}
    (hσ : |q (σ 0)| ≥ |q (σ 1)| ∧ |q (σ 1)| ≥ |q (σ 2)|) :
    isSortedRep (canon q σ) := by
  obtain ⟨h2, h21, h10⟩ := canon_noninc q hσ
  exact ⟨h2, h21, h10, (canon_qL1 q σ).trans_le hq⟩

lemma eq_qOf (q : Fin 3 → ℤ) (a b c : ℤ)
    (h0 : q 0 = a) (h1 : q 1 = b) (h2 : q 2 = c) : q = qOf a b c := by
  ext j; fin_cases j <;> simp [qOf, h0, h1, h2]

lemma sortedRep_is_list {q : Fin 3 → ℤ} (h : isSortedRep q) :
    (q = qOf 0 0 0 ∨ q = qOf 1 0 0 ∨ q = qOf 2 0 0 ∨ q = qOf 1 1 0 ∨
     q = qOf 3 0 0 ∨ q = qOf 2 1 0 ∨ q = qOf 1 1 1 ∨ q = qOf 4 0 0 ∨
     q = qOf 3 1 0 ∨ q = qOf 2 2 0 ∨ q = qOf 2 1 1 ∨ q = qOf 5 0 0 ∨
     q = qOf 4 1 0 ∨ q = qOf 3 2 0 ∨ q = qOf 3 1 1 ∨ q = qOf 2 2 1 ∨
     q = qOf 6 0 0 ∨ q = qOf 5 1 0 ∨ q = qOf 4 2 0 ∨ q = qOf 4 1 1 ∨
     q = qOf 3 3 0 ∨ q = qOf 3 2 1 ∨ q = qOf 2 2 2 ∨ q = qOf 7 0 0 ∨
     q = qOf 6 1 0 ∨ q = qOf 5 2 0 ∨ q = qOf 5 1 1 ∨ q = qOf 4 3 0 ∨
     q = qOf 4 2 1 ∨ q = qOf 3 3 1 ∨ q = qOf 3 2 2) := by
  obtain ⟨h2, h21, h10, hL⟩ := h
  have ha0 : 0 ≤ q 0 := le_trans (le_trans h2 h21) h10
  have ha1 : 0 ≤ q 1 := le_trans h2 h21
  have hA : q 0 + q 1 + q 2 = (qL1 q : ℤ) := by
    unfold qL1
    simp [Fin.sum_univ_three, Int.natAbs_of_nonneg ha0,
      Int.natAbs_of_nonneg ha1, Int.natAbs_of_nonneg h2]
  have hsum : q 0 + q 1 + q 2 ≤ (7 : ℤ) := by
    have : (qL1 q : ℤ) ≤ 7 := Nat.cast_le.mpr hL
    simpa [hA] using this
  have hfin0 : q 0 = 0 ∨ q 0 = 1 ∨ q 0 = 2 ∨ q 0 = 3 ∨ q 0 = 4 ∨
      q 0 = 5 ∨ q 0 = 6 ∨ q 0 = 7 := by omega
  rcases hfin0 with h0 | hfin0
  · -- q 0 = 0
    have hq1 : q 1 = 0 := by omega
    have hq2 : q 2 = 0 := by omega
    exact Or.inl (eq_qOf q 0 0 0 h0 hq1 hq2)
  rcases hfin0 with h0 | hfin0
  · -- q 0 = 1
    have hfin1 : q 1 = 0 ∨ q 1 = 1 := by omega
    rcases hfin1 with hq1 | hfin1
    · -- q 1 = 0
      have hq2 : q 2 = 0 := by omega
      exact Or.inr (Or.inl (eq_qOf q 1 0 0 h0 hq1 hq2))
    have hq1 := hfin1
    -- q 1 = 1
    have hfin2 : q 2 = 0 ∨ q 2 = 1 := by omega
    rcases hfin2 with hq2 | hfin2
    · exact Or.inr (Or.inr (Or.inr (Or.inl (eq_qOf q 1 1 0 h0 hq1 hq2))))
    have hq2 := hfin2
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (eq_qOf q 1 1 1 h0 hq1 hq2)))))))
  rcases hfin0 with h0 | hfin0
  · -- q 0 = 2
    have hfin1 : q 1 = 0 ∨ q 1 = 1 ∨ q 1 = 2 := by omega
    rcases hfin1 with hq1 | hfin1
    · -- q 1 = 0
      have hq2 : q 2 = 0 := by omega
      exact Or.inr (Or.inr (Or.inl (eq_qOf q 2 0 0 h0 hq1 hq2)))
    rcases hfin1 with hq1 | hfin1
    · -- q 1 = 1
      have hfin2 : q 2 = 0 ∨ q 2 = 1 := by omega
      rcases hfin2 with hq2 | hfin2
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (eq_qOf q 2 1 0 h0 hq1 hq2))))))
      have hq2 := hfin2
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (eq_qOf q 2 1 1 h0 hq1 hq2)))))))))))
    have hq1 := hfin1
    -- q 1 = 2
    have hfin2 : q 2 = 0 ∨ q 2 = 1 ∨ q 2 = 2 := by omega
    rcases hfin2 with hq2 | hfin2
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (eq_qOf q 2 2 0 h0 hq1 hq2))))))))))
    rcases hfin2 with hq2 | hfin2
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (eq_qOf q 2 2 1 h0 hq1 hq2))))))))))))))))
    have hq2 := hfin2
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (eq_qOf q 2 2 2 h0 hq1 hq2)))))))))))))))))))))))
  rcases hfin0 with h0 | hfin0
  · -- q 0 = 3
    have hfin1 : q 1 = 0 ∨ q 1 = 1 ∨ q 1 = 2 ∨ q 1 = 3 := by omega
    rcases hfin1 with hq1 | hfin1
    · -- q 1 = 0
      have hq2 : q 2 = 0 := by omega
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (eq_qOf q 3 0 0 h0 hq1 hq2)))))
    rcases hfin1 with hq1 | hfin1
    · -- q 1 = 1
      have hfin2 : q 2 = 0 ∨ q 2 = 1 := by omega
      rcases hfin2 with hq2 | hfin2
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (eq_qOf q 3 1 0 h0 hq1 hq2)))))))))
      have hq2 := hfin2
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (eq_qOf q 3 1 1 h0 hq1 hq2)))))))))))))))
    rcases hfin1 with hq1 | hfin1
    · -- q 1 = 2
      have hfin2 : q 2 = 0 ∨ q 2 = 1 ∨ q 2 = 2 := by omega
      rcases hfin2 with hq2 | hfin2
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (eq_qOf q 3 2 0 h0 hq1 hq2))))))))))))))
      rcases hfin2 with hq2 | hfin2
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (eq_qOf q 3 2 1 h0 hq1 hq2))))))))))))))))))))))
      have hq2 := hfin2
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (eq_qOf q 3 2 2 h0 hq1 hq2))))))))))))))))))))))))))))))
    have hq1 := hfin1
    -- q 1 = 3
    have hfin2 : q 2 = 0 ∨ q 2 = 1 := by omega
    rcases hfin2 with hq2 | hfin2
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (eq_qOf q 3 3 0 h0 hq1 hq2)))))))))))))))))))))
    have hq2 := hfin2
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (eq_qOf q 3 3 1 h0 hq1 hq2))))))))))))))))))))))))))))))
  rcases hfin0 with h0 | hfin0
  · -- q 0 = 4
    have hfin1 : q 1 = 0 ∨ q 1 = 1 ∨ q 1 = 2 ∨ q 1 = 3 := by omega
    rcases hfin1 with hq1 | hfin1
    · -- q 1 = 0
      have hq2 : q 2 = 0 := by omega
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (eq_qOf q 4 0 0 h0 hq1 hq2))))))))
    rcases hfin1 with hq1 | hfin1
    · -- q 1 = 1
      have hfin2 : q 2 = 0 ∨ q 2 = 1 := by omega
      rcases hfin2 with hq2 | hfin2
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (eq_qOf q 4 1 0 h0 hq1 hq2)))))))))))))
      have hq2 := hfin2
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (eq_qOf q 4 1 1 h0 hq1 hq2))))))))))))))))))))
    rcases hfin1 with hq1 | hfin1
    · -- q 1 = 2
      have hfin2 : q 2 = 0 ∨ q 2 = 1 := by omega
      rcases hfin2 with hq2 | hfin2
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (eq_qOf q 4 2 0 h0 hq1 hq2)))))))))))))))))))
      have hq2 := hfin2
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (eq_qOf q 4 2 1 h0 hq1 hq2)))))))))))))))))))))))))))))
    have hq1 := hfin1
    -- q 1 = 3
    have hq2 : q 2 = 0 := by omega
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (eq_qOf q 4 3 0 h0 hq1 hq2))))))))))))))))))))))))))))
  rcases hfin0 with h0 | hfin0
  · -- q 0 = 5
    have hfin1 : q 1 = 0 ∨ q 1 = 1 ∨ q 1 = 2 := by omega
    rcases hfin1 with hq1 | hfin1
    · -- q 1 = 0
      have hq2 : q 2 = 0 := by omega
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (eq_qOf q 5 0 0 h0 hq1 hq2))))))))))))
    rcases hfin1 with hq1 | hfin1
    · -- q 1 = 1
      have hfin2 : q 2 = 0 ∨ q 2 = 1 := by omega
      rcases hfin2 with hq2 | hfin2
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (eq_qOf q 5 1 0 h0 hq1 hq2))))))))))))))))))
      have hq2 := hfin2
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (eq_qOf q 5 1 1 h0 hq1 hq2)))))))))))))))))))))))))))
    have hq1 := hfin1
    -- q 1 = 2
    have hq2 : q 2 = 0 := by omega
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (eq_qOf q 5 2 0 h0 hq1 hq2))))))))))))))))))))))))))
  rcases hfin0 with h0 | hfin0
  · -- q 0 = 6
    have hfin1 : q 1 = 0 ∨ q 1 = 1 := by omega
    rcases hfin1 with hq1 | hfin1
    · -- q 1 = 0
      have hq2 : q 2 = 0 := by omega
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (eq_qOf q 6 0 0 h0 hq1 hq2)))))))))))))))))
    have hq1 := hfin1
    -- q 1 = 1
    have hq2 : q 2 = 0 := by omega
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (eq_qOf q 6 1 0 h0 hq1 hq2)))))))))))))))))))))))))
  have h0 := hfin0
  -- q 0 = 7
  have hq1 : q 1 = 0 := by omega
  have hq2 : q 2 = 0 := by omega
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (eq_qOf q 7 0 0 h0 hq1 hq2))))))))))))))))))))))))

lemma residueSet_sortedRep {q : Fin 3 → ℤ} (h : isSortedRep q) :
    residueSet q = Finset.univ ↔ q = qZ321 ∨ q = qZ421 := by
  have hlist := sortedRep_is_list h
  constructor
  · intro hR
    rcases hlist with h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h'
      | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h'
      | h' | h' | h' | h' | h' | h'
    · subst h'; exact (miss_000 (hR.symm ▸ Finset.mem_univ _)).elim
    · subst h'; exact (miss_100 (hR.symm ▸ Finset.mem_univ _)).elim
    · subst h'; exact (miss_200 (hR.symm ▸ Finset.mem_univ _)).elim
    · subst h'; exact (miss_110 (hR.symm ▸ Finset.mem_univ _)).elim
    · subst h'; exact (miss_300 (hR.symm ▸ Finset.mem_univ _)).elim
    · subst h'; exact (miss_210 (hR.symm ▸ Finset.mem_univ _)).elim
    · subst h'; exact (miss_111 (hR.symm ▸ Finset.mem_univ _)).elim
    · subst h'; exact (miss_400 (hR.symm ▸ Finset.mem_univ _)).elim
    · subst h'; exact (miss_310 (hR.symm ▸ Finset.mem_univ _)).elim
    · subst h'; exact (miss_220 (hR.symm ▸ Finset.mem_univ _)).elim
    · subst h'; exact (miss_211 (hR.symm ▸ Finset.mem_univ _)).elim
    · subst h'; exact (miss_500 (hR.symm ▸ Finset.mem_univ _)).elim
    · subst h'; exact (miss_410 (hR.symm ▸ Finset.mem_univ _)).elim
    · subst h'; exact (miss_320 (hR.symm ▸ Finset.mem_univ _)).elim
    · subst h'; exact (miss_311 (hR.symm ▸ Finset.mem_univ _)).elim
    · subst h'; exact (miss_221 (hR.symm ▸ Finset.mem_univ _)).elim
    · subst h'; exact (miss_600 (hR.symm ▸ Finset.mem_univ _)).elim
    · subst h'; exact (miss_510 (hR.symm ▸ Finset.mem_univ _)).elim
    · subst h'; exact (miss_420 (hR.symm ▸ Finset.mem_univ _)).elim
    · subst h'; exact (miss_411 (hR.symm ▸ Finset.mem_univ _)).elim
    · subst h'; exact (miss_330 (hR.symm ▸ Finset.mem_univ _)).elim
    · subst h'; exact Or.inl rfl
    · subst h'; exact (miss_222 (hR.symm ▸ Finset.mem_univ _)).elim
    · subst h'; exact (miss_700 (hR.symm ▸ Finset.mem_univ _)).elim
    · subst h'; exact (miss_610 (hR.symm ▸ Finset.mem_univ _)).elim
    · subst h'; exact (miss_520 (hR.symm ▸ Finset.mem_univ _)).elim
    · subst h'; exact (miss_511 (hR.symm ▸ Finset.mem_univ _)).elim
    · subst h'; exact (miss_430 (hR.symm ▸ Finset.mem_univ _)).elim
    · subst h'; exact Or.inr qZ421_eq.symm
    · subst h'; exact (miss_331 (hR.symm ▸ Finset.mem_univ _)).elim
    · subst h'; exact (miss_322 (hR.symm ▸ Finset.mem_univ _)).elim
  · intro hq
    rcases hq with hq | hq
    · rw [hq]; exact residueSet_321
    · rw [hq]; exact residueSet_421

theorem classification_L1_le_seven (q : Fin 3 → ℤ) (hq : qL1 q ≤ 7) :
    (∀ {N : ℕ} (_hN : 1 ≤ N) (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
        (_hs : ∀ k j, s k j = 1 ∨ s k j = -1),
      structureFactor (fun k => centroidPoint (n k) (s k)) (qReal q) ≠ 0 ∧
        (1 : ℝ) / (N : ℝ) ^ 6 ≤
          ‖structureFactor (fun k => centroidPoint (n k) (s k)) (qReal q)‖) ∨
    ((∃ σ eps, (∀ j, eps j = 1 ∨ eps j = -1) ∧ orbitQ qZ321 σ eps = q) ∨
      (∃ σ eps, (∀ j, eps j = 1 ∨ eps j = -1) ∧ orbitQ qZ421 σ eps = q)) ∧
    ∃ (n : Fin 7 → Fin 3 → ℤ) (s : Fin 7 → Fin 3 → ℤ)
      (_hs : ∀ k j, s k j = 1 ∨ s k j = -1),
      structureFactor (fun k => centroidPoint (n k) (s k)) (qReal q) = 0 := by
  obtain ⟨σ, hσ⟩ := exists_sort_perm q
  have hcanon : isSortedRep (canon q σ) := isSortedRep_canon hq hσ
  have horbit : orbitQ (canon q σ) σ.symm (fun j => signZ (q j)) = q :=
    orbit_canon q σ
  have heps : ∀ j, signZ (q j) = 1 ∨ signZ (q j) = -1 :=
    fun j => signZ_is_sign (q j)
  by_cases hR : residueSet (canon q σ) = Finset.univ
  · right
    have hv := (residueSet_sortedRep hcanon).mp hR
    constructor
    · rcases hv with hv | hv
      · left; exact ⟨σ.symm, fun j => signZ (q j), heps, by rw [← hv, horbit]⟩
      · right; exact ⟨σ.symm, fun j => signZ (q j), heps, by rw [← hv, horbit]⟩
    · exact exists_box_structureFactor_eq_zero_of_orbit_321_or_421 q (by
        rcases hv with hv | hv
        · exact Or.inl ⟨σ.symm, fun j => signZ (q j), heps, by rw [← hv, horbit]⟩
        · exact Or.inr ⟨σ.symm, fun j => signZ (q j), heps, by rw [← hv, horbit]⟩)
  · left
    intro N hN n s hs
    have hF :
        structureFactor (fun k => centroidPoint (n k) (s k)) (qReal q) ≠ 0 := by
      have hpull := structureFactor_orbit_pull (canon q σ) σ.symm
        (fun j => signZ (q j)) heps n s
      rw [horbit] at hpull
      intro hz
      exact structureFactor_ne_zero_of_residueSet_ne_univ hN (canon q σ)
        (fun k => pullVec σ.symm (fun j => signZ (q j)) (n k))
        (fun k => pullVec σ.symm (fun j => signZ (q j)) (s k))
        (fun k => pullVec_is_sign σ.symm (fun j => signZ (q j)) heps (s k) (hs k))
        hR (hpull.symm ▸ hz)
    exact ⟨hF, norm_structureFactor_ge_inv_N_pow_six hN n s hs q hF⟩

#print axioms structureFactor_ne_zero_at_000
#print axioms structureFactor_ne_zero_at_100
#print axioms structureFactor_ne_zero_at_200
#print axioms structureFactor_ne_zero_at_110
#print axioms structureFactor_ne_zero_at_300
#print axioms structureFactor_ne_zero_at_210
#print axioms structureFactor_ne_zero_at_111
#print axioms structureFactor_ne_zero_at_400
#print axioms structureFactor_ne_zero_at_310
#print axioms structureFactor_ne_zero_at_220
#print axioms structureFactor_ne_zero_at_211
#print axioms structureFactor_ne_zero_at_500
#print axioms structureFactor_ne_zero_at_410
#print axioms structureFactor_ne_zero_at_320
#print axioms structureFactor_ne_zero_at_311
#print axioms structureFactor_ne_zero_at_221
#print axioms structureFactor_ne_zero_at_600
#print axioms structureFactor_ne_zero_at_510
#print axioms structureFactor_ne_zero_at_420
#print axioms structureFactor_ne_zero_at_411
#print axioms structureFactor_ne_zero_at_330
#print axioms structureFactor_ne_zero_at_222
#print axioms structureFactor_ne_zero_at_700
#print axioms structureFactor_ne_zero_at_610
#print axioms structureFactor_ne_zero_at_520
#print axioms structureFactor_ne_zero_at_511
#print axioms structureFactor_ne_zero_at_430
#print axioms structureFactor_ne_zero_at_331
#print axioms structureFactor_ne_zero_at_322
#print axioms structureFactor_ne_zero_of_missing_phaseRes
#print axioms exists_box_structureFactor_eq_zero_at_321
#print axioms exists_box_structureFactor_eq_zero_of_orbit_321_or_421
#print axioms classification_L1_le_seven

end LeanLab.Scratch.LemmaDL1SevenClassification
