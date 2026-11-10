import LeanLab.Scratch.LemmaDOddL1Seven
import LeanLab.Scratch.LemmaDNoZero310211

/-!
# Further L¹ = 7 non-vanishing, and an exact zero at (4,2,1)
(public-screen)

Public-screen v2 copy of LeanLab.Scratch.LemmaDL1SevenMore (official pin src
`51a3e9f7e40e8c3cf1eb4ccaa5bdfb741636fadb93f197ed5f63b58895185408`).
Header redacted; theorem bodies are unchanged. This copy is not a
replacement pin.

**[P, Lean]**

* (A1) For every nonempty finite equal-weight D-form box, `F ≠ 0`
  (and `|F|² > 0`) at `q ∈ {(3,3,1), (4,3,0), (5,2,0)}` and on their
  full coordinate-permutation / coordinate-sign orbits.
* (A2) There exists a 7-point equal-weight D-form box at `q = (4,2,1)`
  (all origins `n_k = 0`) with `F = 0` exactly, and likewise at the
  relabelled wavevector `q = (1,2,4)`. This does not contradict (A1),
  which concerns different `q`.

**Orientation.** Odd `t = q·s`. As in LemmaDOddL1Seven / LemmaDIntVec,
`exp(−iπ t/7) = −ζ^k` whenever `t = 7 − 2k − 14m`, i.e.
`k ≡ (7−t)/2 (mod 7)`, via `resOdd7` and `exp_neg_pi_odd7_eq_neg_zeta`.
The convention `(t+7)/2` is the `k ↔ 7−k` flip of the Lean residues
(0 fixed); missed *sets* are stable under the flip. Non-vanishing uses
`structureFactor_ne_zero_of_missing_residue_neg`.

**Residue tables** (Lean orientation):

* `(3,3,1)`: `t ∈ {±7,±5,±1}` → residues `{0,1,3,4,6}`, miss `{2,5}`.
* `(4,3,0)`: `t ∈ {±7,±1}` → residues `{0,3,4}`, miss `{1,2,5,6}`.
* `(5,2,0)`: `t ∈ {±7,±3}` → residues `{0,2,5}`, miss `{1,3,4,6}`.
* `(4,2,1)`: `t ∈ {±7,±5,±3,±1}` hits all 7 residues (t=±7 both give 0).

Proofs use missed residues `2`, `1`, `1` respectively.

**Exact zero (A2).** Seven sign vectors with
`t ∈ {7,5,3,1,−1,−3,−5}` (the Lean-7 split: include `t=+7`, exclude
`t=−7`) give residues `0,1,2,3,4,5,6` once each. Each summand is
`−ζ^k`, so the phase sum is `−(1+ζ+⋯+ζ⁶)=0`, hence `F=0`.

**Not proved / out of scope:**
* No lower bound. `(6,1,0)` and `(7,0,0)` not formalized.
* `(3,2,2)` and `(5,1,1)` already treated in LemmaDOddL1Seven.
* D-form class only. Scratch; not a Lake target; not peer reviewed.
  The infimum at `(3,3,0)` stays `[X]` in this file.

This file is source-only and is not a Lake package. It claims nothing
beyond the theorems stated below.

Dated 2026-11-10.
-/

namespace LeanLab.Scratch.LemmaDL1SevenMore

open Complex Finset
open LeanLab.Scratch.LemmaD4 (dot3 structureFactor centroidPoint)
open LeanLab.Scratch.LemmaDIntVec
  (qReal signedWeight zeta7 exp_centroid_int_q isPrimitiveRoot_zeta7)
open LeanLab.Scratch.LemmaDOrbitNoZero
  (structureFactor_ne_zero_of_missing_residue_neg
    structureFactor_ne_zero_orbit_transfer orbitQ
    structureFactor_orbit_pull pullVec)
open LeanLab.Scratch.LemmaDOddL1Seven
  (resOdd7 exp_neg_pi_odd7_eq_neg_zeta)

/-! ## q = (3,3,1) -/

def qZ331 : Fin 3 → ℤ
  | ⟨0, _⟩ => 3
  | ⟨1, _⟩ => 3
  | ⟨2, _⟩ => 1

lemma signedWeight_qZ331_mem (s : Fin 3 → ℤ) (hs : ∀ j, s j = 1 ∨ s j = -1) :
    signedWeight qZ331 s = 7 ∨ signedWeight qZ331 s = 5 ∨
      signedWeight qZ331 s = 1 ∨ signedWeight qZ331 s = -1 ∨
        signedWeight qZ331 s = -5 ∨ signedWeight qZ331 s = -7 := by
  have h0 := hs 0; have h1 := hs 1; have h2 := hs 2
  simp only [signedWeight, qZ331, Fin.sum_univ_three]
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
    simp [h0, h1, h2]

lemma signedWeight_qZ331_mem7 (s : Fin 3 → ℤ) (hs : ∀ j, s j = 1 ∨ s j = -1) :
    signedWeight qZ331 s = 7 ∨ signedWeight qZ331 s = 5 ∨
      signedWeight qZ331 s = 3 ∨ signedWeight qZ331 s = 1 ∨
        signedWeight qZ331 s = -1 ∨ signedWeight qZ331 s = -3 ∨
          signedWeight qZ331 s = -5 ∨ signedWeight qZ331 s = -7 := by
  rcases signedWeight_qZ331_mem s hs with h | h | h | h | h | h <;> simp [h]

def res331 (s : Fin 3 → ℤ) : Fin 7 := resOdd7 (signedWeight qZ331 s)

lemma res331_ne_two (s : Fin 3 → ℤ) (hs : ∀ j, s j = 1 ∨ s j = -1) :
    res331 s ≠ ⟨2, by omega⟩ := by
  rcases signedWeight_qZ331_mem s hs with h | h | h | h | h | h
    <;> simp [res331, resOdd7, h]

lemma exp_centroid_331_eq_neg_zeta (n s : Fin 3 → ℤ)
    (hs : ∀ j, s j = 1 ∨ s j = -1) :
    exp (2 * Real.pi * I * dot3 (qReal qZ331) (centroidPoint n s)) =
      -(zeta7 ^ (res331 s).val) := by
  rw [exp_centroid_int_q]
  exact exp_neg_pi_odd7_eq_neg_zeta _ (signedWeight_qZ331_mem7 s hs)

/-- `[P, Lean]` No nonempty finite equal-weight D-form box has `F = 0` at
`q = (3,3,1)`. -/
theorem structureFactor_ne_zero_at_331 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    structureFactor (fun k => centroidPoint (n k) (s k)) (qReal qZ331) ≠ 0 :=
  structureFactor_ne_zero_of_missing_residue_neg hN qZ331 n s hs res331
    (fun k => exp_centroid_331_eq_neg_zeta (n k) (s k) (hs k))
    ⟨2, by omega⟩ res331_ne_two

theorem normSq_structureFactor_ne_zero_at_331 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    ‖structureFactor (fun k => centroidPoint (n k) (s k)) (qReal qZ331)‖ ^ 2 ≠ 0 := by
  intro hz
  have : structureFactor (fun k => centroidPoint (n k) (s k)) (qReal qZ331) = 0 :=
    norm_eq_zero.mp (sq_eq_zero_iff.mp hz)
  exact structureFactor_ne_zero_at_331 hN n s hs this

theorem normSq_structureFactor_pos_at_331 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    0 < ‖structureFactor (fun k => centroidPoint (n k) (s k)) (qReal qZ331)‖ ^ 2 :=
  lt_of_le_of_ne (sq_nonneg _)
    (normSq_structureFactor_ne_zero_at_331 hN n s hs).symm

theorem structureFactor_ne_zero_orbit_331 {N : ℕ} (hN : 1 ≤ N)
    (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    structureFactor (fun k => centroidPoint (n k) (s k))
      (qReal (orbitQ qZ331 σ eps)) ≠ 0 :=
  structureFactor_ne_zero_orbit_transfer hN qZ331
    (fun {_N'} hN' n' s' hs' => structureFactor_ne_zero_at_331 hN' n' s' hs')
    σ eps heps n s hs

theorem normSq_structureFactor_pos_orbit_331 {N : ℕ} (hN : 1 ≤ N)
    (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    0 < ‖structureFactor (fun k => centroidPoint (n k) (s k))
      (qReal (orbitQ qZ331 σ eps))‖ ^ 2 :=
  lt_of_le_of_ne (sq_nonneg _) (by
    intro hz
    exact structureFactor_ne_zero_orbit_331 hN σ eps heps n s hs
      (norm_eq_zero.mp (sq_eq_zero_iff.mp hz.symm)))

/-! ## q = (4,3,0) -/

def qZ430 : Fin 3 → ℤ
  | ⟨0, _⟩ => 4
  | ⟨1, _⟩ => 3
  | ⟨2, _⟩ => 0

lemma signedWeight_qZ430_mem (s : Fin 3 → ℤ) (hs : ∀ j, s j = 1 ∨ s j = -1) :
    signedWeight qZ430 s = 7 ∨ signedWeight qZ430 s = 1 ∨
      signedWeight qZ430 s = -1 ∨ signedWeight qZ430 s = -7 := by
  have h0 := hs 0; have h1 := hs 1
  simp only [signedWeight, qZ430, Fin.sum_univ_three]
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> simp [h0, h1]

lemma signedWeight_qZ430_mem7 (s : Fin 3 → ℤ) (hs : ∀ j, s j = 1 ∨ s j = -1) :
    signedWeight qZ430 s = 7 ∨ signedWeight qZ430 s = 5 ∨
      signedWeight qZ430 s = 3 ∨ signedWeight qZ430 s = 1 ∨
        signedWeight qZ430 s = -1 ∨ signedWeight qZ430 s = -3 ∨
          signedWeight qZ430 s = -5 ∨ signedWeight qZ430 s = -7 := by
  rcases signedWeight_qZ430_mem s hs with h | h | h | h <;> simp [h]

def res430 (s : Fin 3 → ℤ) : Fin 7 := resOdd7 (signedWeight qZ430 s)

lemma res430_ne_one (s : Fin 3 → ℤ) (hs : ∀ j, s j = 1 ∨ s j = -1) :
    res430 s ≠ ⟨1, by omega⟩ := by
  rcases signedWeight_qZ430_mem s hs with h | h | h | h
    <;> simp [res430, resOdd7, h]

lemma exp_centroid_430_eq_neg_zeta (n s : Fin 3 → ℤ)
    (hs : ∀ j, s j = 1 ∨ s j = -1) :
    exp (2 * Real.pi * I * dot3 (qReal qZ430) (centroidPoint n s)) =
      -(zeta7 ^ (res430 s).val) := by
  rw [exp_centroid_int_q]
  exact exp_neg_pi_odd7_eq_neg_zeta _ (signedWeight_qZ430_mem7 s hs)

/-- `[P, Lean]` No nonempty finite equal-weight D-form box has `F = 0` at
`q = (4,3,0)`. -/
theorem structureFactor_ne_zero_at_430 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    structureFactor (fun k => centroidPoint (n k) (s k)) (qReal qZ430) ≠ 0 :=
  structureFactor_ne_zero_of_missing_residue_neg hN qZ430 n s hs res430
    (fun k => exp_centroid_430_eq_neg_zeta (n k) (s k) (hs k))
    ⟨1, by omega⟩ res430_ne_one

theorem normSq_structureFactor_ne_zero_at_430 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    ‖structureFactor (fun k => centroidPoint (n k) (s k)) (qReal qZ430)‖ ^ 2 ≠ 0 := by
  intro hz
  have : structureFactor (fun k => centroidPoint (n k) (s k)) (qReal qZ430) = 0 :=
    norm_eq_zero.mp (sq_eq_zero_iff.mp hz)
  exact structureFactor_ne_zero_at_430 hN n s hs this

theorem normSq_structureFactor_pos_at_430 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    0 < ‖structureFactor (fun k => centroidPoint (n k) (s k)) (qReal qZ430)‖ ^ 2 :=
  lt_of_le_of_ne (sq_nonneg _)
    (normSq_structureFactor_ne_zero_at_430 hN n s hs).symm

theorem structureFactor_ne_zero_orbit_430 {N : ℕ} (hN : 1 ≤ N)
    (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    structureFactor (fun k => centroidPoint (n k) (s k))
      (qReal (orbitQ qZ430 σ eps)) ≠ 0 :=
  structureFactor_ne_zero_orbit_transfer hN qZ430
    (fun {_N'} hN' n' s' hs' => structureFactor_ne_zero_at_430 hN' n' s' hs')
    σ eps heps n s hs

theorem normSq_structureFactor_pos_orbit_430 {N : ℕ} (hN : 1 ≤ N)
    (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    0 < ‖structureFactor (fun k => centroidPoint (n k) (s k))
      (qReal (orbitQ qZ430 σ eps))‖ ^ 2 :=
  lt_of_le_of_ne (sq_nonneg _) (by
    intro hz
    exact structureFactor_ne_zero_orbit_430 hN σ eps heps n s hs
      (norm_eq_zero.mp (sq_eq_zero_iff.mp hz.symm)))

/-! ## q = (5,2,0) -/

def qZ520 : Fin 3 → ℤ
  | ⟨0, _⟩ => 5
  | ⟨1, _⟩ => 2
  | ⟨2, _⟩ => 0

lemma signedWeight_qZ520_mem (s : Fin 3 → ℤ) (hs : ∀ j, s j = 1 ∨ s j = -1) :
    signedWeight qZ520 s = 7 ∨ signedWeight qZ520 s = 3 ∨
      signedWeight qZ520 s = -3 ∨ signedWeight qZ520 s = -7 := by
  have h0 := hs 0; have h1 := hs 1
  simp only [signedWeight, qZ520, Fin.sum_univ_three]
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> simp [h0, h1]

lemma signedWeight_qZ520_mem7 (s : Fin 3 → ℤ) (hs : ∀ j, s j = 1 ∨ s j = -1) :
    signedWeight qZ520 s = 7 ∨ signedWeight qZ520 s = 5 ∨
      signedWeight qZ520 s = 3 ∨ signedWeight qZ520 s = 1 ∨
        signedWeight qZ520 s = -1 ∨ signedWeight qZ520 s = -3 ∨
          signedWeight qZ520 s = -5 ∨ signedWeight qZ520 s = -7 := by
  rcases signedWeight_qZ520_mem s hs with h | h | h | h <;> simp [h]

def res520 (s : Fin 3 → ℤ) : Fin 7 := resOdd7 (signedWeight qZ520 s)

lemma res520_ne_one (s : Fin 3 → ℤ) (hs : ∀ j, s j = 1 ∨ s j = -1) :
    res520 s ≠ ⟨1, by omega⟩ := by
  rcases signedWeight_qZ520_mem s hs with h | h | h | h
    <;> simp [res520, resOdd7, h]

lemma exp_centroid_520_eq_neg_zeta (n s : Fin 3 → ℤ)
    (hs : ∀ j, s j = 1 ∨ s j = -1) :
    exp (2 * Real.pi * I * dot3 (qReal qZ520) (centroidPoint n s)) =
      -(zeta7 ^ (res520 s).val) := by
  rw [exp_centroid_int_q]
  exact exp_neg_pi_odd7_eq_neg_zeta _ (signedWeight_qZ520_mem7 s hs)

/-- `[P, Lean]` No nonempty finite equal-weight D-form box has `F = 0` at
`q = (5,2,0)`. -/
theorem structureFactor_ne_zero_at_520 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    structureFactor (fun k => centroidPoint (n k) (s k)) (qReal qZ520) ≠ 0 :=
  structureFactor_ne_zero_of_missing_residue_neg hN qZ520 n s hs res520
    (fun k => exp_centroid_520_eq_neg_zeta (n k) (s k) (hs k))
    ⟨1, by omega⟩ res520_ne_one

theorem normSq_structureFactor_ne_zero_at_520 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    ‖structureFactor (fun k => centroidPoint (n k) (s k)) (qReal qZ520)‖ ^ 2 ≠ 0 := by
  intro hz
  have : structureFactor (fun k => centroidPoint (n k) (s k)) (qReal qZ520) = 0 :=
    norm_eq_zero.mp (sq_eq_zero_iff.mp hz)
  exact structureFactor_ne_zero_at_520 hN n s hs this

theorem normSq_structureFactor_pos_at_520 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    0 < ‖structureFactor (fun k => centroidPoint (n k) (s k)) (qReal qZ520)‖ ^ 2 :=
  lt_of_le_of_ne (sq_nonneg _)
    (normSq_structureFactor_ne_zero_at_520 hN n s hs).symm

theorem structureFactor_ne_zero_orbit_520 {N : ℕ} (hN : 1 ≤ N)
    (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    structureFactor (fun k => centroidPoint (n k) (s k))
      (qReal (orbitQ qZ520 σ eps)) ≠ 0 :=
  structureFactor_ne_zero_orbit_transfer hN qZ520
    (fun {_N'} hN' n' s' hs' => structureFactor_ne_zero_at_520 hN' n' s' hs')
    σ eps heps n s hs

theorem normSq_structureFactor_pos_orbit_520 {N : ℕ} (hN : 1 ≤ N)
    (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    0 < ‖structureFactor (fun k => centroidPoint (n k) (s k))
      (qReal (orbitQ qZ520 σ eps))‖ ^ 2 :=
  lt_of_le_of_ne (sq_nonneg _) (by
    intro hz
    exact structureFactor_ne_zero_orbit_520 hN σ eps heps n s hs
      (norm_eq_zero.mp (sq_eq_zero_iff.mp hz.symm)))

/-! ## (A2) Exact zero witness at q = (4,2,1), N = 7 -/

def qZ421 : Fin 3 → ℤ
  | ⟨0, _⟩ => 4
  | ⟨1, _⟩ => 2
  | ⟨2, _⟩ => 1

/-- Lean-7 split: the seven sign vectors with
`t ∈ {7,5,3,1,−1,−3,−5}` (include `t=+7`, exclude `t=−7`). -/
def s421 : Fin 7 → Fin 3 → ℤ :=
  ![![1, 1, 1], ![1, 1, -1], ![1, -1, 1], ![1, -1, -1],
    ![-1, 1, 1], ![-1, 1, -1], ![-1, -1, 1]]

def n421 : Fin 7 → Fin 3 → ℤ := fun _ _ => 0

lemma hs421 (k : Fin 7) (j : Fin 3) : s421 k j = 1 ∨ s421 k j = -1 := by
  fin_cases k <;> fin_cases j <;> simp [s421]

lemma signedWeight_s421 :
    signedWeight qZ421 (s421 0) = 7 ∧
    signedWeight qZ421 (s421 1) = 5 ∧
    signedWeight qZ421 (s421 2) = 3 ∧
    signedWeight qZ421 (s421 3) = 1 ∧
    signedWeight qZ421 (s421 4) = -1 ∧
    signedWeight qZ421 (s421 5) = -3 ∧
    signedWeight qZ421 (s421 6) = -5 := by
  simp [signedWeight, qZ421, s421, Fin.sum_univ_three]

lemma resOdd7_s421 (k : Fin 7) : resOdd7 (signedWeight qZ421 (s421 k)) = k := by
  fin_cases k <;> simp [resOdd7, signedWeight_s421]

lemma sum_zeta7_fin : (∑ k : Fin 7, zeta7 ^ k.val) = 0 := by
  have hrange : (∑ i ∈ range 7, zeta7 ^ i) = 0 :=
    IsPrimitiveRoot.geom_sum_eq_zero isPrimitiveRoot_zeta7 (by decide)
  rw [Fin.sum_univ_eq_sum_range (fun i => zeta7 ^ i), hrange]

lemma sum_phase_s421 :
    (∑ k : Fin 7,
        exp (2 * Real.pi * I *
          dot3 (qReal qZ421) (centroidPoint (n421 k) (s421 k)))) = 0 := by
  have hphase : ∀ k : Fin 7,
      exp (2 * Real.pi * I *
          dot3 (qReal qZ421) (centroidPoint (n421 k) (s421 k))) =
        -(zeta7 ^ k.val) := by
    intro k
    rw [exp_centroid_int_q]
    have ht :
        signedWeight qZ421 (s421 k) = 7 ∨ signedWeight qZ421 (s421 k) = 5 ∨
          signedWeight qZ421 (s421 k) = 3 ∨ signedWeight qZ421 (s421 k) = 1 ∨
            signedWeight qZ421 (s421 k) = -1 ∨ signedWeight qZ421 (s421 k) = -3 ∨
              signedWeight qZ421 (s421 k) = -5 ∨
                signedWeight qZ421 (s421 k) = -7 := by
      fin_cases k <;> simp [signedWeight_s421]
    have := exp_neg_pi_odd7_eq_neg_zeta _ ht
    simpa [resOdd7_s421 k] using this
  calc
    (∑ k : Fin 7,
        exp (2 * Real.pi * I *
          dot3 (qReal qZ421) (centroidPoint (n421 k) (s421 k))))
        = ∑ k : Fin 7, -(zeta7 ^ k.val) := sum_congr rfl fun k _ => hphase k
    _ = -∑ k : Fin 7, zeta7 ^ k.val := by
        rw [← Finset.sum_neg_distrib]
    _ = 0 := by rw [sum_zeta7_fin, neg_zero]

/-- `[P, Lean]` There is a 7-point equal-weight D-form box at `q = (4,2,1)`
with `F = 0` exactly. (Not a contradiction with the nonvanishing theorems
above, which concern different wavevectors.) -/
theorem exists_box_structureFactor_eq_zero_at_421 :
    ∃ (n : Fin 7 → Fin 3 → ℤ) (s : Fin 7 → Fin 3 → ℤ)
      (_hs : ∀ k j, s k j = 1 ∨ s k j = -1),
      structureFactor (fun k => centroidPoint (n k) (s k)) (qReal qZ421) = 0 := by
  refine ⟨n421, s421, hs421, ?_⟩
  unfold structureFactor
  rw [sum_phase_s421, mul_zero]

theorem exists_box_normSq_eq_zero_at_421 :
    ∃ (n : Fin 7 → Fin 3 → ℤ) (s : Fin 7 → Fin 3 → ℤ)
      (_hs : ∀ k j, s k j = 1 ∨ s k j = -1),
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) (qReal qZ421)‖ ^ 2 = 0 := by
  obtain ⟨n, s, hs, hF⟩ := exists_box_structureFactor_eq_zero_at_421
  refine ⟨n, s, hs, ?_⟩
  simp [hF]

/-! ### Relabelled witness at q = (1,2,4) -/

def qZ124 : Fin 3 → ℤ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 2
  | ⟨2, _⟩ => 4

def σ124 : Equiv.Perm (Fin 3) := Equiv.swap 0 2
def eps1 : Fin 3 → ℤ := fun _ => 1

lemma heps1 : ∀ j, eps1 j = 1 ∨ eps1 j = -1 := fun _ => Or.inl rfl

lemma orbitQ_421_to_124 : orbitQ qZ421 σ124 eps1 = qZ124 := by
  ext j
  fin_cases j
  · simp [orbitQ, qZ124, σ124, eps1, Equiv.swap_apply_left, qZ421]
  · simp [orbitQ, qZ124, σ124, eps1,
      Equiv.swap_apply_of_ne_of_ne (by decide : (1 : Fin 3) ≠ 0)
        (by decide : (1 : Fin 3) ≠ 2), qZ421]
  · simp [orbitQ, qZ124, σ124, eps1, Equiv.swap_apply_right, qZ421]

/-- Push the (4,2,1) sign pattern forward along the coordinate swap. -/
def s124 (k : Fin 7) : Fin 3 → ℤ := fun j => s421 k (σ124 j)
def n124 : Fin 7 → Fin 3 → ℤ := fun _ _ => 0

lemma hs124 (k : Fin 7) (j : Fin 3) : s124 k j = 1 ∨ s124 k j = -1 :=
  hs421 k (σ124 j)

lemma pull_s124 (k : Fin 7) : pullVec σ124 eps1 (s124 k) = s421 k := by
  ext i
  simp [pullVec, s124, eps1, σ124, Equiv.symm_swap, Equiv.swap_apply_self]

lemma pull_n124 (k : Fin 7) : pullVec σ124 eps1 (n124 k) = n421 k := by
  ext i
  simp [pullVec, n124, n421, eps1]

/-- `[P, Lean]` The same 7-point construction, after swapping coordinates
0 and 2, gives `F = 0` at `q = (1,2,4)`. -/
theorem exists_box_structureFactor_eq_zero_at_124 :
    ∃ (n : Fin 7 → Fin 3 → ℤ) (s : Fin 7 → Fin 3 → ℤ)
      (_hs : ∀ k j, s k j = 1 ∨ s k j = -1),
      structureFactor (fun k => centroidPoint (n k) (s k)) (qReal qZ124) = 0 := by
  refine ⟨n124, s124, hs124, ?_⟩
  have hpull := structureFactor_orbit_pull qZ421 σ124 eps1 heps1 n124 s124
  have hL :
      structureFactor
          (fun k => centroidPoint (pullVec σ124 eps1 (n124 k))
            (pullVec σ124 eps1 (s124 k)))
          (qReal qZ421) = 0 := by
    have : (fun k => centroidPoint (pullVec σ124 eps1 (n124 k))
        (pullVec σ124 eps1 (s124 k))) =
        fun k => centroidPoint (n421 k) (s421 k) := by
      funext k; rw [pull_n124, pull_s124]
    rw [this]
    unfold structureFactor
    rw [sum_phase_s421, mul_zero]
  have hR :
      structureFactor (fun k => centroidPoint (n124 k) (s124 k))
        (qReal (orbitQ qZ421 σ124 eps1)) = 0 := by
    rw [← hpull]; exact hL
  simpa [orbitQ_421_to_124] using hR

theorem exists_box_normSq_eq_zero_at_124 :
    ∃ (n : Fin 7 → Fin 3 → ℤ) (s : Fin 7 → Fin 3 → ℤ)
      (_hs : ∀ k j, s k j = 1 ∨ s k j = -1),
      ‖structureFactor (fun k => centroidPoint (n k) (s k)) (qReal qZ124)‖ ^ 2 = 0 := by
  obtain ⟨n, s, hs, hF⟩ := exists_box_structureFactor_eq_zero_at_124
  refine ⟨n, s, hs, ?_⟩
  simp [hF]

#print axioms structureFactor_ne_zero_at_331
#print axioms structureFactor_ne_zero_at_430
#print axioms structureFactor_ne_zero_at_520
#print axioms normSq_structureFactor_pos_at_331
#print axioms structureFactor_ne_zero_orbit_331
#print axioms structureFactor_ne_zero_orbit_430
#print axioms structureFactor_ne_zero_orbit_520
#print axioms exists_box_structureFactor_eq_zero_at_421
#print axioms exists_box_structureFactor_eq_zero_at_124

end LeanLab.Scratch.LemmaDL1SevenMore
