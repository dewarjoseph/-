import LeanLab.Scratch.LemmaDNoZero310211
import LeanLab.Scratch.LemmaDOrbitNoZero

/-!
# Non-vanishing at L¹ = 6 even-t orbits (scratch)

**[P, Lean]** For every nonempty finite equal-weight D-form box,
`F(q) ≠ 0` (hence `|F|² > 0`) at the integer vectors
`q ∈ {(2,2,2), (3,3,0), (4,1,1), (4,2,0)}` and along their full
coordinate-permutation / coordinate-sign orbits.

All four representatives have even `t = q·s`. Phases are
`exp(−iπ t/7) = ζ₇^k` with the existing Lean orientation
`t = −2k − 14m`, i.e. `k ≡ (−t/2) (mod 7)`, via
`LemmaDNoZero310211.exp_neg_pi_t_eq_zeta`. A missed residue and
`structureFactor_ne_zero_of_missing_residue` give `F ≠ 0`.
Orbit transfer is `structureFactor_ne_zero_orbit_transfer`.

**Residue tables** (Lean orientation), checked against QIS note
`/home/box/shared/qis-eth/lean/kg-dform-l1eq6-map-2026-11-09.md`
(sha256 `7827eeac4731791de922561ef92de8b19b951643d8a022b023ca888e430a32a6`)
and against the parent derivation:

* `(2,2,2)`: `t ∈ {±6,±2}` → residues `{4,3,6,1}`, miss `{0,2,5}`.
* `(3,3,0)`: `t ∈ {±6,0}` → residues `{4,3,0}`, miss `{1,2,5,6}`.
* `(4,1,1)`: `t ∈ {±6,±4,±2}` (`t=0` impossible) → `{4,3,5,2,6,1}`, miss `{0}`.
* `(4,2,0)`: `t ∈ {±6,±2}` → `{4,3,6,1}`, miss `{0,2,5}`.

QIS lists the same t-sets. QIS residues use `r = (t/2) mod 7` for
`exp(+iπ t/7)`, which is the k ↔ 7−k flip of the Lean convention
`k ≡ (−t/2) mod 7` for `exp(−iπ t/7)`. The residue *sets* (and the
missed sets, which are stable under the flip) agree on all four
orbits. No mismatch. The proofs use one missed residue each
(`0` at `(2,2,2)`, `(4,1,1)`, `(4,2,0)`; `1` at `(3,3,0)`).

**Not proved / out of scope:**
* `(3,2,1)` is a known equal-weight `F=0` exception (hits all 7
  residues) and is not formalized here.
* `(5,1,0)` and `(6,0,0)` (would-cover PP orbits in the QIS map)
  are not formalized here.
* No lower bound; nonvanishing only.
* D-form class only. Scratch; not a Lake target; not peer reviewed.
  Licenses nothing about ETH (false stays `[X]`), R2/R4/R5,
  ScaleLiftToRAM, PrimToRAM, CH-V-020, or Theorem F.
-/

namespace LeanLab.Scratch.LemmaDL1Six

open Complex Finset
open LeanLab.Scratch.LemmaD4 (dot3 structureFactor centroidPoint)
open LeanLab.Scratch.LemmaDIntVec
  (qReal signedWeight zeta7 exp_centroid_int_q)
open LeanLab.Scratch.LemmaDNoZero310211
  (exp_neg_pi_t_eq_zeta structureFactor_ne_zero_of_missing_residue)
open LeanLab.Scratch.LemmaDOrbitNoZero
  (orbitQ structureFactor_ne_zero_orbit_transfer)

/-! ## Even-t residue (Lean orientation `k ≡ (−t/2) mod 7`) -/

/-- Residue of an even `t` with `|t| ≤ 6`. Unreachable default `0`. -/
def resEvenT (t : ℤ) : Fin 7 :=
  if t = 6 then ⟨4, by omega⟩
  else if t = 4 then ⟨5, by omega⟩
  else if t = 2 then ⟨6, by omega⟩
  else if t = 0 then ⟨0, by omega⟩
  else if t = -2 then ⟨1, by omega⟩
  else if t = -4 then ⟨2, by omega⟩
  else if t = -6 then ⟨3, by omega⟩
  else ⟨0, by omega⟩

lemma resEvenT_of_six (h : t = 6) : resEvenT t = ⟨4, by omega⟩ := by
  simp [resEvenT, h]
lemma resEvenT_of_four (h : t = 4) : resEvenT t = ⟨5, by omega⟩ := by
  simp [resEvenT, h]
lemma resEvenT_of_two (h : t = 2) : resEvenT t = ⟨6, by omega⟩ := by
  simp [resEvenT, h]
lemma resEvenT_of_zero (h : t = 0) : resEvenT t = ⟨0, by omega⟩ := by
  simp [resEvenT, h]
lemma resEvenT_of_neg_two (h : t = -2) : resEvenT t = ⟨1, by omega⟩ := by
  simp [resEvenT, h]
lemma resEvenT_of_neg_four (h : t = -4) : resEvenT t = ⟨2, by omega⟩ := by
  simp [resEvenT, h]
lemma resEvenT_of_neg_six (h : t = -6) : resEvenT t = ⟨3, by omega⟩ := by
  simp [resEvenT, h]

lemma exp_neg_pi_even6_eq_zeta (t : ℤ)
    (ht : t = 6 ∨ t = 4 ∨ t = 2 ∨ t = 0 ∨ t = -2 ∨ t = -4 ∨ t = -6) :
    exp (((-(Real.pi * (t : ℝ) / 7) : ℝ) : ℂ) * I) =
      zeta7 ^ (resEvenT t).val := by
  rcases ht with h | h | h | h | h | h | h
  · subst h; rw [resEvenT_of_six rfl]; exact exp_neg_pi_t_eq_zeta 6 4 (-1) (by norm_num)
  · subst h; rw [resEvenT_of_four rfl]; exact exp_neg_pi_t_eq_zeta 4 5 (-1) (by norm_num)
  · subst h; rw [resEvenT_of_two rfl]; exact exp_neg_pi_t_eq_zeta 2 6 (-1) (by norm_num)
  · subst h; rw [resEvenT_of_zero rfl]; exact exp_neg_pi_t_eq_zeta 0 0 0 (by norm_num)
  · subst h; rw [resEvenT_of_neg_two rfl]; exact exp_neg_pi_t_eq_zeta (-2) 1 0 (by norm_num)
  · subst h; rw [resEvenT_of_neg_four rfl]; exact exp_neg_pi_t_eq_zeta (-4) 2 0 (by norm_num)
  · subst h; rw [resEvenT_of_neg_six rfl]; exact exp_neg_pi_t_eq_zeta (-6) 3 0 (by norm_num)

/-! ## q = (2,2,2) -/

def qZ222 : Fin 3 → ℤ
  | ⟨0, _⟩ => 2
  | ⟨1, _⟩ => 2
  | ⟨2, _⟩ => 2

noncomputable def q222 : Fin 3 → ℝ := qReal qZ222

def res222 (s : Fin 3 → ℤ) : Fin 7 := resEvenT (signedWeight qZ222 s)

lemma signedWeight_qZ222_mem (s : Fin 3 → ℤ)
    (hs : ∀ j, s j = 1 ∨ s j = -1) :
    signedWeight qZ222 s = 6 ∨ signedWeight qZ222 s = 2 ∨
      signedWeight qZ222 s = -2 ∨ signedWeight qZ222 s = -6 := by
  have h0 := hs 0; have h1 := hs 1; have h2 := hs 2
  simp only [signedWeight, qZ222, Fin.sum_univ_three]
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
    simp [h0, h1, h2]

lemma signedWeight_qZ222_mem7 (s : Fin 3 → ℤ)
    (hs : ∀ j, s j = 1 ∨ s j = -1) :
    signedWeight qZ222 s = 6 ∨ signedWeight qZ222 s = 4 ∨
      signedWeight qZ222 s = 2 ∨ signedWeight qZ222 s = 0 ∨
      signedWeight qZ222 s = -2 ∨ signedWeight qZ222 s = -4 ∨
      signedWeight qZ222 s = -6 := by
  rcases signedWeight_qZ222_mem s hs with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))

lemma res222_ne_zero (s : Fin 3 → ℤ) (hs : ∀ j, s j = 1 ∨ s j = -1) :
    res222 s ≠ ⟨0, by omega⟩ := by
  rcases signedWeight_qZ222_mem s hs with h | h | h | h
  · simp [res222, resEvenT_of_six h]
  · simp [res222, resEvenT_of_two h]
  · simp [res222, resEvenT_of_neg_two h]
  · simp [res222, resEvenT_of_neg_six h]

lemma exp_centroid_222_eq_zeta (n s : Fin 3 → ℤ)
    (hs : ∀ j, s j = 1 ∨ s j = -1) :
    exp (2 * Real.pi * I * dot3 (qReal qZ222) (centroidPoint n s)) =
      zeta7 ^ (res222 s).val := by
  rw [exp_centroid_int_q]
  simpa [res222] using exp_neg_pi_even6_eq_zeta _ (signedWeight_qZ222_mem7 s hs)

/-- `[P, Lean]` `F ≠ 0` at `q = (2,2,2)`. -/
theorem structureFactor_ne_zero_at_222 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    structureFactor (fun k => centroidPoint (n k) (s k)) q222 ≠ 0 := by
  simpa [q222] using
    structureFactor_ne_zero_of_missing_residue hN qZ222 n s hs res222
      (fun k => exp_centroid_222_eq_zeta (n k) (s k) (hs k))
      ⟨0, by omega⟩ res222_ne_zero

theorem normSq_structureFactor_ne_zero_at_222 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    ‖structureFactor (fun k => centroidPoint (n k) (s k)) q222‖ ^ 2 ≠ 0 := by
  intro hz
  have : structureFactor (fun k => centroidPoint (n k) (s k)) q222 = 0 :=
    norm_eq_zero.mp (sq_eq_zero_iff.mp hz)
  exact structureFactor_ne_zero_at_222 hN n s hs this

theorem normSq_structureFactor_pos_at_222 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    0 < ‖structureFactor (fun k => centroidPoint (n k) (s k)) q222‖ ^ 2 :=
  lt_of_le_of_ne (sq_nonneg _)
    (normSq_structureFactor_ne_zero_at_222 hN n s hs).symm

theorem structureFactor_ne_zero_orbit_222 {N : ℕ} (hN : 1 ≤ N)
    (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    structureFactor (fun k => centroidPoint (n k) (s k))
      (qReal (orbitQ qZ222 σ eps)) ≠ 0 :=
  structureFactor_ne_zero_orbit_transfer hN qZ222
    (fun {_N'} hN' n' s' hs' => structureFactor_ne_zero_at_222 hN' n' s' hs')
    σ eps heps n s hs

theorem normSq_structureFactor_pos_orbit_222 {N : ℕ} (hN : 1 ≤ N)
    (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    0 < ‖structureFactor (fun k => centroidPoint (n k) (s k))
      (qReal (orbitQ qZ222 σ eps))‖ ^ 2 :=
  lt_of_le_of_ne (sq_nonneg _) (by
    intro hz
    exact structureFactor_ne_zero_orbit_222 hN σ eps heps n s hs
      (norm_eq_zero.mp (sq_eq_zero_iff.mp hz.symm)))

/-! ## q = (3,3,0) -/

def qZ330 : Fin 3 → ℤ
  | ⟨0, _⟩ => 3
  | ⟨1, _⟩ => 3
  | ⟨2, _⟩ => 0

noncomputable def q330 : Fin 3 → ℝ := qReal qZ330

def res330 (s : Fin 3 → ℤ) : Fin 7 := resEvenT (signedWeight qZ330 s)

lemma signedWeight_qZ330_mem (s : Fin 3 → ℤ)
    (hs : ∀ j, s j = 1 ∨ s j = -1) :
    signedWeight qZ330 s = 6 ∨ signedWeight qZ330 s = 0 ∨
      signedWeight qZ330 s = -6 := by
  have h0 := hs 0; have h1 := hs 1
  simp only [signedWeight, qZ330, Fin.sum_univ_three]
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> simp [h0, h1]

lemma signedWeight_qZ330_mem7 (s : Fin 3 → ℤ)
    (hs : ∀ j, s j = 1 ∨ s j = -1) :
    signedWeight qZ330 s = 6 ∨ signedWeight qZ330 s = 4 ∨
      signedWeight qZ330 s = 2 ∨ signedWeight qZ330 s = 0 ∨
      signedWeight qZ330 s = -2 ∨ signedWeight qZ330 s = -4 ∨
      signedWeight qZ330 s = -6 := by
  rcases signedWeight_qZ330_mem s hs with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))

lemma res330_ne_one (s : Fin 3 → ℤ) (hs : ∀ j, s j = 1 ∨ s j = -1) :
    res330 s ≠ ⟨1, by omega⟩ := by
  rcases signedWeight_qZ330_mem s hs with h | h | h
  · simp [res330, resEvenT_of_six h]
  · simp [res330, resEvenT_of_zero h]
  · simp [res330, resEvenT_of_neg_six h]

lemma exp_centroid_330_eq_zeta (n s : Fin 3 → ℤ)
    (hs : ∀ j, s j = 1 ∨ s j = -1) :
    exp (2 * Real.pi * I * dot3 (qReal qZ330) (centroidPoint n s)) =
      zeta7 ^ (res330 s).val := by
  rw [exp_centroid_int_q]
  simpa [res330] using exp_neg_pi_even6_eq_zeta _ (signedWeight_qZ330_mem7 s hs)

/-- `[P, Lean]` `F ≠ 0` at `q = (3,3,0)`. -/
theorem structureFactor_ne_zero_at_330 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    structureFactor (fun k => centroidPoint (n k) (s k)) q330 ≠ 0 := by
  simpa [q330] using
    structureFactor_ne_zero_of_missing_residue hN qZ330 n s hs res330
      (fun k => exp_centroid_330_eq_zeta (n k) (s k) (hs k))
      ⟨1, by omega⟩ res330_ne_one

theorem normSq_structureFactor_ne_zero_at_330 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    ‖structureFactor (fun k => centroidPoint (n k) (s k)) q330‖ ^ 2 ≠ 0 := by
  intro hz
  have : structureFactor (fun k => centroidPoint (n k) (s k)) q330 = 0 :=
    norm_eq_zero.mp (sq_eq_zero_iff.mp hz)
  exact structureFactor_ne_zero_at_330 hN n s hs this

theorem normSq_structureFactor_pos_at_330 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    0 < ‖structureFactor (fun k => centroidPoint (n k) (s k)) q330‖ ^ 2 :=
  lt_of_le_of_ne (sq_nonneg _)
    (normSq_structureFactor_ne_zero_at_330 hN n s hs).symm

theorem structureFactor_ne_zero_orbit_330 {N : ℕ} (hN : 1 ≤ N)
    (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    structureFactor (fun k => centroidPoint (n k) (s k))
      (qReal (orbitQ qZ330 σ eps)) ≠ 0 :=
  structureFactor_ne_zero_orbit_transfer hN qZ330
    (fun {_N'} hN' n' s' hs' => structureFactor_ne_zero_at_330 hN' n' s' hs')
    σ eps heps n s hs

theorem normSq_structureFactor_pos_orbit_330 {N : ℕ} (hN : 1 ≤ N)
    (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    0 < ‖structureFactor (fun k => centroidPoint (n k) (s k))
      (qReal (orbitQ qZ330 σ eps))‖ ^ 2 :=
  lt_of_le_of_ne (sq_nonneg _) (by
    intro hz
    exact structureFactor_ne_zero_orbit_330 hN σ eps heps n s hs
      (norm_eq_zero.mp (sq_eq_zero_iff.mp hz.symm)))

/-! ## q = (4,1,1) -/

def qZ411 : Fin 3 → ℤ
  | ⟨0, _⟩ => 4
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 1

noncomputable def q411 : Fin 3 → ℝ := qReal qZ411

def res411 (s : Fin 3 → ℤ) : Fin 7 := resEvenT (signedWeight qZ411 s)

lemma signedWeight_qZ411_mem (s : Fin 3 → ℤ)
    (hs : ∀ j, s j = 1 ∨ s j = -1) :
    signedWeight qZ411 s = 6 ∨ signedWeight qZ411 s = 4 ∨
      signedWeight qZ411 s = 2 ∨ signedWeight qZ411 s = -2 ∨
      signedWeight qZ411 s = -4 ∨ signedWeight qZ411 s = -6 := by
  have h0 := hs 0; have h1 := hs 1; have h2 := hs 2
  simp only [signedWeight, qZ411, Fin.sum_univ_three]
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
    simp [h0, h1, h2]

lemma signedWeight_qZ411_mem7 (s : Fin 3 → ℤ)
    (hs : ∀ j, s j = 1 ∨ s j = -1) :
    signedWeight qZ411 s = 6 ∨ signedWeight qZ411 s = 4 ∨
      signedWeight qZ411 s = 2 ∨ signedWeight qZ411 s = 0 ∨
      signedWeight qZ411 s = -2 ∨ signedWeight qZ411 s = -4 ∨
      signedWeight qZ411 s = -6 := by
  rcases signedWeight_qZ411_mem s hs with h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))

lemma res411_ne_zero (s : Fin 3 → ℤ) (hs : ∀ j, s j = 1 ∨ s j = -1) :
    res411 s ≠ ⟨0, by omega⟩ := by
  rcases signedWeight_qZ411_mem s hs with h | h | h | h | h | h
  · simp [res411, resEvenT_of_six h]
  · simp [res411, resEvenT_of_four h]
  · simp [res411, resEvenT_of_two h]
  · simp [res411, resEvenT_of_neg_two h]
  · simp [res411, resEvenT_of_neg_four h]
  · simp [res411, resEvenT_of_neg_six h]

lemma exp_centroid_411_eq_zeta (n s : Fin 3 → ℤ)
    (hs : ∀ j, s j = 1 ∨ s j = -1) :
    exp (2 * Real.pi * I * dot3 (qReal qZ411) (centroidPoint n s)) =
      zeta7 ^ (res411 s).val := by
  rw [exp_centroid_int_q]
  simpa [res411] using exp_neg_pi_even6_eq_zeta _ (signedWeight_qZ411_mem7 s hs)

/-- `[P, Lean]` `F ≠ 0` at `q = (4,1,1)`. -/
theorem structureFactor_ne_zero_at_411 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    structureFactor (fun k => centroidPoint (n k) (s k)) q411 ≠ 0 := by
  simpa [q411] using
    structureFactor_ne_zero_of_missing_residue hN qZ411 n s hs res411
      (fun k => exp_centroid_411_eq_zeta (n k) (s k) (hs k))
      ⟨0, by omega⟩ res411_ne_zero

theorem normSq_structureFactor_ne_zero_at_411 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    ‖structureFactor (fun k => centroidPoint (n k) (s k)) q411‖ ^ 2 ≠ 0 := by
  intro hz
  have : structureFactor (fun k => centroidPoint (n k) (s k)) q411 = 0 :=
    norm_eq_zero.mp (sq_eq_zero_iff.mp hz)
  exact structureFactor_ne_zero_at_411 hN n s hs this

theorem normSq_structureFactor_pos_at_411 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    0 < ‖structureFactor (fun k => centroidPoint (n k) (s k)) q411‖ ^ 2 :=
  lt_of_le_of_ne (sq_nonneg _)
    (normSq_structureFactor_ne_zero_at_411 hN n s hs).symm

theorem structureFactor_ne_zero_orbit_411 {N : ℕ} (hN : 1 ≤ N)
    (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    structureFactor (fun k => centroidPoint (n k) (s k))
      (qReal (orbitQ qZ411 σ eps)) ≠ 0 :=
  structureFactor_ne_zero_orbit_transfer hN qZ411
    (fun {_N'} hN' n' s' hs' => structureFactor_ne_zero_at_411 hN' n' s' hs')
    σ eps heps n s hs

theorem normSq_structureFactor_pos_orbit_411 {N : ℕ} (hN : 1 ≤ N)
    (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    0 < ‖structureFactor (fun k => centroidPoint (n k) (s k))
      (qReal (orbitQ qZ411 σ eps))‖ ^ 2 :=
  lt_of_le_of_ne (sq_nonneg _) (by
    intro hz
    exact structureFactor_ne_zero_orbit_411 hN σ eps heps n s hs
      (norm_eq_zero.mp (sq_eq_zero_iff.mp hz.symm)))

/-! ## q = (4,2,0) -/

def qZ420 : Fin 3 → ℤ
  | ⟨0, _⟩ => 4
  | ⟨1, _⟩ => 2
  | ⟨2, _⟩ => 0

noncomputable def q420 : Fin 3 → ℝ := qReal qZ420

def res420 (s : Fin 3 → ℤ) : Fin 7 := resEvenT (signedWeight qZ420 s)

lemma signedWeight_qZ420_mem (s : Fin 3 → ℤ)
    (hs : ∀ j, s j = 1 ∨ s j = -1) :
    signedWeight qZ420 s = 6 ∨ signedWeight qZ420 s = 2 ∨
      signedWeight qZ420 s = -2 ∨ signedWeight qZ420 s = -6 := by
  have h0 := hs 0; have h1 := hs 1
  simp only [signedWeight, qZ420, Fin.sum_univ_three]
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> simp [h0, h1]

lemma signedWeight_qZ420_mem7 (s : Fin 3 → ℤ)
    (hs : ∀ j, s j = 1 ∨ s j = -1) :
    signedWeight qZ420 s = 6 ∨ signedWeight qZ420 s = 4 ∨
      signedWeight qZ420 s = 2 ∨ signedWeight qZ420 s = 0 ∨
      signedWeight qZ420 s = -2 ∨ signedWeight qZ420 s = -4 ∨
      signedWeight qZ420 s = -6 := by
  rcases signedWeight_qZ420_mem s hs with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))

lemma res420_ne_zero (s : Fin 3 → ℤ) (hs : ∀ j, s j = 1 ∨ s j = -1) :
    res420 s ≠ ⟨0, by omega⟩ := by
  rcases signedWeight_qZ420_mem s hs with h | h | h | h
  · simp [res420, resEvenT_of_six h]
  · simp [res420, resEvenT_of_two h]
  · simp [res420, resEvenT_of_neg_two h]
  · simp [res420, resEvenT_of_neg_six h]

lemma exp_centroid_420_eq_zeta (n s : Fin 3 → ℤ)
    (hs : ∀ j, s j = 1 ∨ s j = -1) :
    exp (2 * Real.pi * I * dot3 (qReal qZ420) (centroidPoint n s)) =
      zeta7 ^ (res420 s).val := by
  rw [exp_centroid_int_q]
  simpa [res420] using exp_neg_pi_even6_eq_zeta _ (signedWeight_qZ420_mem7 s hs)

/-- `[P, Lean]` `F ≠ 0` at `q = (4,2,0)`. -/
theorem structureFactor_ne_zero_at_420 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    structureFactor (fun k => centroidPoint (n k) (s k)) q420 ≠ 0 := by
  simpa [q420] using
    structureFactor_ne_zero_of_missing_residue hN qZ420 n s hs res420
      (fun k => exp_centroid_420_eq_zeta (n k) (s k) (hs k))
      ⟨0, by omega⟩ res420_ne_zero

theorem normSq_structureFactor_ne_zero_at_420 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    ‖structureFactor (fun k => centroidPoint (n k) (s k)) q420‖ ^ 2 ≠ 0 := by
  intro hz
  have : structureFactor (fun k => centroidPoint (n k) (s k)) q420 = 0 :=
    norm_eq_zero.mp (sq_eq_zero_iff.mp hz)
  exact structureFactor_ne_zero_at_420 hN n s hs this

theorem normSq_structureFactor_pos_at_420 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    0 < ‖structureFactor (fun k => centroidPoint (n k) (s k)) q420‖ ^ 2 :=
  lt_of_le_of_ne (sq_nonneg _)
    (normSq_structureFactor_ne_zero_at_420 hN n s hs).symm

theorem structureFactor_ne_zero_orbit_420 {N : ℕ} (hN : 1 ≤ N)
    (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    structureFactor (fun k => centroidPoint (n k) (s k))
      (qReal (orbitQ qZ420 σ eps)) ≠ 0 :=
  structureFactor_ne_zero_orbit_transfer hN qZ420
    (fun {_N'} hN' n' s' hs' => structureFactor_ne_zero_at_420 hN' n' s' hs')
    σ eps heps n s hs

theorem normSq_structureFactor_pos_orbit_420 {N : ℕ} (hN : 1 ≤ N)
    (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    0 < ‖structureFactor (fun k => centroidPoint (n k) (s k))
      (qReal (orbitQ qZ420 σ eps))‖ ^ 2 :=
  lt_of_le_of_ne (sq_nonneg _) (by
    intro hz
    exact structureFactor_ne_zero_orbit_420 hN σ eps heps n s hs
      (norm_eq_zero.mp (sq_eq_zero_iff.mp hz.symm)))

#print axioms structureFactor_ne_zero_at_222
#print axioms structureFactor_ne_zero_at_330
#print axioms structureFactor_ne_zero_at_411
#print axioms structureFactor_ne_zero_at_420
#print axioms normSq_structureFactor_pos_at_222
#print axioms normSq_structureFactor_pos_at_330
#print axioms normSq_structureFactor_pos_at_411
#print axioms normSq_structureFactor_pos_at_420
#print axioms structureFactor_ne_zero_orbit_222
#print axioms structureFactor_ne_zero_orbit_330
#print axioms structureFactor_ne_zero_orbit_411
#print axioms structureFactor_ne_zero_orbit_420
#print axioms normSq_structureFactor_pos_orbit_222
#print axioms normSq_structureFactor_pos_orbit_330
#print axioms normSq_structureFactor_pos_orbit_411
#print axioms normSq_structureFactor_pos_orbit_420

end LeanLab.Scratch.LemmaDL1Six
