import LeanLab.Scratch.LemmaDOrbitNoZero

/-!
# Chair44 D-form: no equal-weight zero at q = (3,2,2) and q = (5,1,1) (scratch)

**[P, Lean]** For every nonempty finite equal-weight D-form box, `F ≠ 0`
(and `|F|² > 0`) at the integer wavevectors `q = (3,2,2)` and `q = (5,1,1)`,
and likewise on their full coordinate-permutation / coordinate-sign orbits
(via `structureFactor_ne_zero_orbit_transfer`).

**Argument.** `t = q·s` is odd. As in LemmaDIntVec,
`exp(−iπ t/7) = −ζ^k` whenever `t = 7 − 2k − 14m` (orientation of
`exp_neg_pi_t_eq_neg_zeta`). The residue `k mod 7` for `|t| ≤ 7` is
`k ≡ (7 − t)/2 (mod 7)`. Direct evaluation on all eight sign vectors:

* `(3,2,2)`: `t ∈ {±7, ±3, ±1}`, residues `{0,2,3,4,5}`, missing `1` and `6`.
* `(5,1,1)`: `t ∈ {±7, ±5, ±3}`, residues `{0,1,2,5,6}`, missing `3` and `4`.

The global sign `−1` does not affect vanishing; the existing
`structureFactor_ne_zero_of_missing_residue_neg` applies.

**Not proved / out of scope:**
* No uniform positive lower bound on `|F|²` (`[X]`).
* Nothing for other `‖q‖₁ = 7` vectors beyond these two orbits.
* D-form hypothesis class only. Scratch; not a Lake target; not peer
  reviewed. Licenses nothing about ETH (false stays `[X]`), R2/R4/R5,
  ScaleLiftToRAM, PrimToRAM, CH-V-020, or Theorem F.
-/

namespace LeanLab.Scratch.LemmaDOddL1Seven

open Complex Finset
open LeanLab.Scratch.LemmaD4 (dot3 structureFactor centroidPoint)
open LeanLab.Scratch.LemmaDIntVec
  (qReal signedWeight exp_centroid_int_q zeta7 exp_neg_pi_t_eq_neg_zeta)
open LeanLab.Scratch.LemmaDOrbitNoZero
  (structureFactor_ne_zero_of_missing_residue_neg
    structureFactor_ne_zero_orbit_transfer orbitQ)

/-! ## Residues for odd |t| ≤ 7 (including ±7) -/

/-- Residue `k` with `t = 7 − 2k − 14m`, so `exp(−iπ t/7) = −ζ^k`. -/
def resOdd7 (t : ℤ) : Fin 7 :=
  if t = 7 then ⟨0, by omega⟩
  else if t = 5 then ⟨1, by omega⟩
  else if t = 3 then ⟨2, by omega⟩
  else if t = 1 then ⟨3, by omega⟩
  else if t = -1 then ⟨4, by omega⟩
  else if t = -3 then ⟨5, by omega⟩
  else if t = -5 then ⟨6, by omega⟩
  else if t = -7 then ⟨0, by omega⟩
  else ⟨0, by omega⟩

lemma exp_neg_pi_odd7_eq_neg_zeta (t : ℤ)
    (h : t = 7 ∨ t = 5 ∨ t = 3 ∨ t = 1 ∨
      t = -1 ∨ t = -3 ∨ t = -5 ∨ t = -7) :
    exp (((-(Real.pi * (t : ℝ) / 7) : ℝ) : ℂ) * I) =
      -(zeta7 ^ (resOdd7 t).val) := by
  rcases h with h | h | h | h | h | h | h | h
  · subst h; change _ = -(zeta7 ^ 0); exact exp_neg_pi_t_eq_neg_zeta 7 0 0 (by norm_num)
  · subst h; change _ = -(zeta7 ^ 1); exact exp_neg_pi_t_eq_neg_zeta 5 1 0 (by norm_num)
  · subst h; change _ = -(zeta7 ^ 2); exact exp_neg_pi_t_eq_neg_zeta 3 2 0 (by norm_num)
  · subst h; change _ = -(zeta7 ^ 3); exact exp_neg_pi_t_eq_neg_zeta 1 3 0 (by norm_num)
  · subst h; change _ = -(zeta7 ^ 4); exact exp_neg_pi_t_eq_neg_zeta (-1) 4 0 (by norm_num)
  · subst h; change _ = -(zeta7 ^ 5); exact exp_neg_pi_t_eq_neg_zeta (-3) 5 0 (by norm_num)
  · subst h; change _ = -(zeta7 ^ 6); exact exp_neg_pi_t_eq_neg_zeta (-5) 6 0 (by norm_num)
  · -- t = -7 = 7 - 2*0 - 14*1
    subst h; change _ = -(zeta7 ^ 0); exact exp_neg_pi_t_eq_neg_zeta (-7) 0 1 (by norm_num)

/-! ## q = (3, 2, 2) -/

def qZ322 : Fin 3 → ℤ
  | ⟨0, _⟩ => 3
  | ⟨1, _⟩ => 2
  | ⟨2, _⟩ => 2

lemma signedWeight_qZ322_mem (s : Fin 3 → ℤ) (hs : ∀ j, s j = 1 ∨ s j = -1) :
    signedWeight qZ322 s = 7 ∨ signedWeight qZ322 s = 3 ∨
      signedWeight qZ322 s = 1 ∨ signedWeight qZ322 s = -1 ∨
        signedWeight qZ322 s = -3 ∨ signedWeight qZ322 s = -7 := by
  have h0 := hs 0
  have h1 := hs 1
  have h2 := hs 2
  simp only [signedWeight, qZ322, Fin.sum_univ_three]
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
    simp [h0, h1, h2]

lemma signedWeight_qZ322_mem7 (s : Fin 3 → ℤ) (hs : ∀ j, s j = 1 ∨ s j = -1) :
    signedWeight qZ322 s = 7 ∨ signedWeight qZ322 s = 5 ∨
      signedWeight qZ322 s = 3 ∨ signedWeight qZ322 s = 1 ∨
        signedWeight qZ322 s = -1 ∨ signedWeight qZ322 s = -3 ∨
          signedWeight qZ322 s = -5 ∨ signedWeight qZ322 s = -7 := by
  rcases signedWeight_qZ322_mem s hs with h | h | h | h | h | h <;> simp [h]

def res322 (s : Fin 3 → ℤ) : Fin 7 := resOdd7 (signedWeight qZ322 s)

/-- Direct evaluation: residues at (3,2,2) never hit 1. -/
lemma res322_ne_one (s : Fin 3 → ℤ) (hs : ∀ j, s j = 1 ∨ s j = -1) :
    res322 s ≠ ⟨1, by omega⟩ := by
  rcases signedWeight_qZ322_mem s hs with h | h | h | h | h | h
    <;> simp [res322, resOdd7, h]

/-- Direct evaluation: residues at (3,2,2) never hit 6. -/
lemma res322_ne_six (s : Fin 3 → ℤ) (hs : ∀ j, s j = 1 ∨ s j = -1) :
    res322 s ≠ ⟨6, by omega⟩ := by
  rcases signedWeight_qZ322_mem s hs with h | h | h | h | h | h
    <;> simp [res322, resOdd7, h]

lemma exp_centroid_322_eq_neg_zeta (n s : Fin 3 → ℤ)
    (hs : ∀ j, s j = 1 ∨ s j = -1) :
    exp (2 * Real.pi * I * dot3 (qReal qZ322) (centroidPoint n s)) =
      -(zeta7 ^ (res322 s).val) := by
  rw [exp_centroid_int_q]
  exact exp_neg_pi_odd7_eq_neg_zeta _ (signedWeight_qZ322_mem7 s hs)

/-- `[P, Lean]` No nonempty finite equal-weight D-form box has `F = 0` at
`q = (3,2,2)`. -/
theorem structureFactor_ne_zero_at_322 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    structureFactor (fun k => centroidPoint (n k) (s k)) (qReal qZ322) ≠ 0 :=
  structureFactor_ne_zero_of_missing_residue_neg hN qZ322 n s hs res322
    (fun k => exp_centroid_322_eq_neg_zeta (n k) (s k) (hs k))
    ⟨1, by omega⟩ res322_ne_one

theorem normSq_structureFactor_ne_zero_at_322 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    ‖structureFactor (fun k => centroidPoint (n k) (s k)) (qReal qZ322)‖ ^ 2 ≠ 0 := by
  intro hz
  have : structureFactor (fun k => centroidPoint (n k) (s k)) (qReal qZ322) = 0 :=
    norm_eq_zero.mp (sq_eq_zero_iff.mp hz)
  exact structureFactor_ne_zero_at_322 hN n s hs this

theorem normSq_structureFactor_pos_at_322 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    0 < ‖structureFactor (fun k => centroidPoint (n k) (s k)) (qReal qZ322)‖ ^ 2 :=
  lt_of_le_of_ne (sq_nonneg _)
    (normSq_structureFactor_ne_zero_at_322 hN n s hs).symm

theorem structureFactor_ne_zero_orbit_322 {N : ℕ} (hN : 1 ≤ N)
    (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    structureFactor (fun k => centroidPoint (n k) (s k))
      (qReal (orbitQ qZ322 σ eps)) ≠ 0 :=
  structureFactor_ne_zero_orbit_transfer hN qZ322
    (fun {_N'} hN' n' s' hs' => structureFactor_ne_zero_at_322 hN' n' s' hs')
    σ eps heps n s hs

/-! ## q = (5, 1, 1) -/

def qZ511 : Fin 3 → ℤ
  | ⟨0, _⟩ => 5
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 1

lemma signedWeight_qZ511_mem (s : Fin 3 → ℤ) (hs : ∀ j, s j = 1 ∨ s j = -1) :
    signedWeight qZ511 s = 7 ∨ signedWeight qZ511 s = 5 ∨
      signedWeight qZ511 s = 3 ∨ signedWeight qZ511 s = -3 ∨
        signedWeight qZ511 s = -5 ∨ signedWeight qZ511 s = -7 := by
  have h0 := hs 0
  have h1 := hs 1
  have h2 := hs 2
  simp only [signedWeight, qZ511, Fin.sum_univ_three]
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
    simp [h0, h1, h2]

lemma signedWeight_qZ511_mem7 (s : Fin 3 → ℤ) (hs : ∀ j, s j = 1 ∨ s j = -1) :
    signedWeight qZ511 s = 7 ∨ signedWeight qZ511 s = 5 ∨
      signedWeight qZ511 s = 3 ∨ signedWeight qZ511 s = 1 ∨
        signedWeight qZ511 s = -1 ∨ signedWeight qZ511 s = -3 ∨
          signedWeight qZ511 s = -5 ∨ signedWeight qZ511 s = -7 := by
  rcases signedWeight_qZ511_mem s hs with h | h | h | h | h | h <;> simp [h]

def res511 (s : Fin 3 → ℤ) : Fin 7 := resOdd7 (signedWeight qZ511 s)

/-- Direct evaluation: residues at (5,1,1) never hit 3. -/
lemma res511_ne_three (s : Fin 3 → ℤ) (hs : ∀ j, s j = 1 ∨ s j = -1) :
    res511 s ≠ ⟨3, by omega⟩ := by
  rcases signedWeight_qZ511_mem s hs with h | h | h | h | h | h
    <;> simp [res511, resOdd7, h]

/-- Direct evaluation: residues at (5,1,1) never hit 4. -/
lemma res511_ne_four (s : Fin 3 → ℤ) (hs : ∀ j, s j = 1 ∨ s j = -1) :
    res511 s ≠ ⟨4, by omega⟩ := by
  rcases signedWeight_qZ511_mem s hs with h | h | h | h | h | h
    <;> simp [res511, resOdd7, h]

lemma exp_centroid_511_eq_neg_zeta (n s : Fin 3 → ℤ)
    (hs : ∀ j, s j = 1 ∨ s j = -1) :
    exp (2 * Real.pi * I * dot3 (qReal qZ511) (centroidPoint n s)) =
      -(zeta7 ^ (res511 s).val) := by
  rw [exp_centroid_int_q]
  exact exp_neg_pi_odd7_eq_neg_zeta _ (signedWeight_qZ511_mem7 s hs)

/-- `[P, Lean]` No nonempty finite equal-weight D-form box has `F = 0` at
`q = (5,1,1)`. -/
theorem structureFactor_ne_zero_at_511 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    structureFactor (fun k => centroidPoint (n k) (s k)) (qReal qZ511) ≠ 0 :=
  structureFactor_ne_zero_of_missing_residue_neg hN qZ511 n s hs res511
    (fun k => exp_centroid_511_eq_neg_zeta (n k) (s k) (hs k))
    ⟨3, by omega⟩ res511_ne_three

theorem normSq_structureFactor_ne_zero_at_511 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    ‖structureFactor (fun k => centroidPoint (n k) (s k)) (qReal qZ511)‖ ^ 2 ≠ 0 := by
  intro hz
  have : structureFactor (fun k => centroidPoint (n k) (s k)) (qReal qZ511) = 0 :=
    norm_eq_zero.mp (sq_eq_zero_iff.mp hz)
  exact structureFactor_ne_zero_at_511 hN n s hs this

theorem normSq_structureFactor_pos_at_511 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    0 < ‖structureFactor (fun k => centroidPoint (n k) (s k)) (qReal qZ511)‖ ^ 2 :=
  lt_of_le_of_ne (sq_nonneg _)
    (normSq_structureFactor_ne_zero_at_511 hN n s hs).symm

theorem structureFactor_ne_zero_orbit_511 {N : ℕ} (hN : 1 ≤ N)
    (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    structureFactor (fun k => centroidPoint (n k) (s k))
      (qReal (orbitQ qZ511 σ eps)) ≠ 0 :=
  structureFactor_ne_zero_orbit_transfer hN qZ511
    (fun {_N'} hN' n' s' hs' => structureFactor_ne_zero_at_511 hN' n' s' hs')
    σ eps heps n s hs

#print axioms structureFactor_ne_zero_at_322
#print axioms structureFactor_ne_zero_at_511
#print axioms normSq_structureFactor_pos_at_322
#print axioms normSq_structureFactor_pos_at_511
#print axioms structureFactor_ne_zero_orbit_322
#print axioms structureFactor_ne_zero_orbit_511

end LeanLab.Scratch.LemmaDOddL1Seven
