import LeanLab.Scratch.LemmaDOrbitNoZero
import LeanLab.Scratch.LemmaDLowerBound220
import LeanLab.Scratch.LemmaDLowerBound330Sharper
import LeanLab.Scratch.LemmaDLowerBoundL1SevenCubic
import LeanLab.Scratch.LemmaDL1SevenClassification

/-!
# Full-orbit cubic N⁻³ bounds at the six one-conjugate-pair reps (scratch)

**[P, Lean]** The explicit `‖F‖ ≥ c0 / N³` bounds already proved at the
six one-conjugate-pair representatives transfer to every
coordinate-permutation / coordinate-sign image `orbitQ (qOf a b c) σ eps`
(`epsⱼ = ±1`), with the *same* rational `c0`, for every nonempty
equal-weight D-form box:

* `(2,2,0)`: `c0 = 1/30` (LemmaDLowerBound220)
* `(3,3,0)`: `c0 = 1/34` (LemmaDLowerBound330Sharper)
* `(1,1,0)`: `c0 = 1/38` (LemmaDLowerBoundL1SevenCubic)
* `(6,1,0)`: `c0 = 1/38` (LemmaDLowerBoundL1SevenCubic)
* `(5,2,0)`: `c0 = 1/30` (LemmaDLowerBoundL1SevenCubic)
* `(4,3,0)`: `c0 = 1/34` (LemmaDLowerBoundL1SevenCubic)

Named theorems `norm_structureFactor_ge_c0_div_N_pow_three_orbit_<tag>`
and the squared forms `normSq_structureFactor_ge_c0_sq_div_N_pow_six_orbit_<tag>`
are given for each. The transfer is the same relabeling used in
LemmaDOrbitNormSqPos: `structureFactor_orbit_pull` identifies `F` at
the orbit wavevector with `F` of the pulled box at the representative,
and `pullVec` preserves the equal-weight sign condition.

The exponent 3 is what the method gives, not claimed sharp. Infima stay
`[X]`. No orbit failed; there is no obstacle note.

D-form class only. Scratch; not a Lake target; not peer reviewed.
Licenses nothing about ETH (false stays `[X]`), R2/R4/R5,
ScaleLiftToRAM, PrimToRAM, CH-V-020, or Theorem F.

Dated 2026-11-09.
-/

namespace LeanLab.Scratch.LemmaDOrbitLowerBoundCubic

open Complex Equiv
open LeanLab.Scratch.LemmaD4 (structureFactor centroidPoint)
open LeanLab.Scratch.LemmaDIntVec (qReal)
open LeanLab.Scratch.LemmaDOrbitNoZero
  (orbitQ pullVec pullVec_is_sign structureFactor_orbit_pull)
open LeanLab.Scratch.LemmaDL1SevenClassification (qOf)
open LeanLab.Scratch.LemmaDNoZero220 (qZ220 q220)
open LeanLab.Scratch.LemmaDL1Six (qZ330 q330)
open LeanLab.Scratch.LemmaDLowerBound220 (c0)
open LeanLab.Scratch.LemmaDLowerBound330Sharper (c0')
open LeanLab.Scratch.LemmaDLowerBoundL1SevenCubic
  (qZ110 q110 c0_110 qZ610 q610 c0_610 qZ520 q520 c0_520 qZ430 q430 c0_430)

/-- The bound at a representative transfers along the signed-permutation
orbit, with the same `c0`. -/
lemma norm_structureFactor_ge_c0_div_N3_orbit_transfer
    {N : ℕ} (hN : 1 ≤ N)
    (qZ : Fin 3 → ℤ) (c0 : ℝ)
    (hq : ∀ {N' : ℕ} (_hN' : 1 ≤ N') (n : Fin N' → Fin 3 → ℤ)
      (s : Fin N' → Fin 3 → ℤ), (∀ k j, s k j = 1 ∨ s k j = -1) →
      c0 / (N' : ℝ) ^ 3 ≤
        ‖structureFactor (fun k => centroidPoint (n k) (s k)) (qReal qZ)‖)
    (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n' : Fin N → Fin 3 → ℤ) (s' : Fin N → Fin 3 → ℤ)
    (hs' : ∀ k j, s' k j = 1 ∨ s' k j = -1) :
    c0 / (N : ℝ) ^ 3 ≤
      ‖structureFactor (fun k => centroidPoint (n' k) (s' k))
        (qReal (orbitQ qZ σ eps))‖ := by
  have hs_pull : ∀ k j,
      pullVec σ eps (s' k) j = 1 ∨ pullVec σ eps (s' k) j = -1 :=
    fun k => pullVec_is_sign σ eps heps (s' k) (hs' k)
  have hEq := structureFactor_orbit_pull qZ σ eps heps n' s'
  have hbound :=
    hq hN (fun k => pullVec σ eps (n' k)) (fun k => pullVec σ eps (s' k))
      hs_pull
  rwa [hEq] at hbound

lemma normSq_of_norm_ge_c0_div_N3 {N : ℕ} {c0 : ℝ} (hc0 : 0 ≤ c0)
    (F : ℂ) (h : c0 / (N : ℝ) ^ 3 ≤ ‖F‖) :
    c0 ^ 2 / (N : ℝ) ^ 6 ≤ ‖F‖ ^ 2 := by
  have hNpow : (0 : ℝ) ≤ (N : ℝ) ^ 3 := by positivity
  have hnn : 0 ≤ c0 / (N : ℝ) ^ 3 := div_nonneg hc0 hNpow
  have hF : 0 ≤ ‖F‖ := norm_nonneg _
  have hsq := mul_le_mul h h hnn hF
  have hL : (c0 / (N : ℝ) ^ 3) * (c0 / (N : ℝ) ^ 3) =
      c0 ^ 2 / (N : ℝ) ^ 6 := by field_simp
  have hR : ‖F‖ * ‖F‖ = ‖F‖ ^ 2 := by ring
  rwa [hL, hR] at hsq

lemma qZ220_eq_qOf : qZ220 = qOf 2 2 0 := by
  ext i; fin_cases i <;> rfl

lemma qZ330_eq_qOf : qZ330 = qOf 3 3 0 := by
  ext i; fin_cases i <;> rfl

lemma qZ110_eq_qOf : qZ110 = qOf 1 1 0 := rfl
lemma qZ610_eq_qOf : qZ610 = qOf 6 1 0 := rfl
lemma qZ520_eq_qOf : qZ520 = qOf 5 2 0 := rfl
lemma qZ430_eq_qOf : qZ430 = qOf 4 3 0 := rfl

/-! ## (2,2,0), c0 = 1/30 -/

/-- `[P, Lean]` `‖F‖ ≥ (1/30) / N³` on the full signed-permutation orbit of `(2,2,0)`. -/
theorem norm_structureFactor_ge_c0_div_N_pow_three_orbit_220
    {N : ℕ} (hN : 1 ≤ N)
    (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    c0 / (N : ℝ) ^ 3 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (orbitQ (qOf 2 2 0) σ eps))‖ := by
  have h :=
    norm_structureFactor_ge_c0_div_N3_orbit_transfer hN qZ220 c0
      (fun {N'} hN' n' s' hs' => by
        simpa [show q220 = qReal qZ220 from rfl] using
          LeanLab.Scratch.LemmaDLowerBound220.norm_structureFactor_ge_c0_div_N_pow_three
            hN' n' s' hs')
      σ eps heps n s hs
  simpa [qZ220_eq_qOf] using h

theorem normSq_structureFactor_ge_c0_sq_div_N_pow_six_orbit_220
    {N : ℕ} (hN : 1 ≤ N)
    (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    c0 ^ 2 / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (orbitQ (qOf 2 2 0) σ eps))‖ ^ 2 :=
  normSq_of_norm_ge_c0_div_N3
    LeanLab.Scratch.LemmaDLowerBound220.c0_pos.le
    _ (norm_structureFactor_ge_c0_div_N_pow_three_orbit_220 hN σ eps heps n s hs)

/-! ## (3,3,0), c0 = 1/34 -/

/-- `[P, Lean]` `‖F‖ ≥ (1/34) / N³` on the full signed-permutation orbit of `(3,3,0)`. -/
theorem norm_structureFactor_ge_c0_div_N_pow_three_orbit_330
    {N : ℕ} (hN : 1 ≤ N)
    (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    c0' / (N : ℝ) ^ 3 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (orbitQ (qOf 3 3 0) σ eps))‖ := by
  have h :=
    norm_structureFactor_ge_c0_div_N3_orbit_transfer hN qZ330 c0'
      (fun {N'} hN' n' s' hs' => by
        simpa [show q330 = qReal qZ330 from rfl] using
          LeanLab.Scratch.LemmaDLowerBound330Sharper.norm_structureFactor_ge_c0'_div_N_pow_three
            hN' n' s' hs')
      σ eps heps n s hs
  simpa [qZ330_eq_qOf] using h

theorem normSq_structureFactor_ge_c0_sq_div_N_pow_six_orbit_330
    {N : ℕ} (hN : 1 ≤ N)
    (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    c0' ^ 2 / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (orbitQ (qOf 3 3 0) σ eps))‖ ^ 2 :=
  normSq_of_norm_ge_c0_div_N3
    LeanLab.Scratch.LemmaDLowerBound330Sharper.c0'_pos.le
    _ (norm_structureFactor_ge_c0_div_N_pow_three_orbit_330 hN σ eps heps n s hs)

/-! ## (1,1,0), c0 = 1/38 -/

/-- `[P, Lean]` `‖F‖ ≥ (1/38) / N³` on the full signed-permutation orbit of `(1,1,0)`. -/
theorem norm_structureFactor_ge_c0_div_N_pow_three_orbit_110
    {N : ℕ} (hN : 1 ≤ N)
    (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    c0_110 / (N : ℝ) ^ 3 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (orbitQ (qOf 1 1 0) σ eps))‖ := by
  have h :=
    norm_structureFactor_ge_c0_div_N3_orbit_transfer hN qZ110 c0_110
      (fun {N'} hN' n' s' hs' => by
        simpa [show q110 = qReal qZ110 from rfl] using
          LeanLab.Scratch.LemmaDLowerBoundL1SevenCubic.norm_structureFactor_ge_c0_div_N_pow_three_at_110
            hN' n' s' hs')
      σ eps heps n s hs
  simpa [qZ110_eq_qOf] using h

theorem normSq_structureFactor_ge_c0_sq_div_N_pow_six_orbit_110
    {N : ℕ} (hN : 1 ≤ N)
    (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    c0_110 ^ 2 / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (orbitQ (qOf 1 1 0) σ eps))‖ ^ 2 :=
  normSq_of_norm_ge_c0_div_N3 (by unfold c0_110; norm_num)
    _ (norm_structureFactor_ge_c0_div_N_pow_three_orbit_110 hN σ eps heps n s hs)

/-! ## (6,1,0), c0 = 1/38 -/

/-- `[P, Lean]` `‖F‖ ≥ (1/38) / N³` on the full signed-permutation orbit of `(6,1,0)`. -/
theorem norm_structureFactor_ge_c0_div_N_pow_three_orbit_610
    {N : ℕ} (hN : 1 ≤ N)
    (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    c0_610 / (N : ℝ) ^ 3 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (orbitQ (qOf 6 1 0) σ eps))‖ := by
  have h :=
    norm_structureFactor_ge_c0_div_N3_orbit_transfer hN qZ610 c0_610
      (fun {N'} hN' n' s' hs' => by
        simpa [show q610 = qReal qZ610 from rfl] using
          LeanLab.Scratch.LemmaDLowerBoundL1SevenCubic.norm_structureFactor_ge_c0_div_N_pow_three_at_610
            hN' n' s' hs')
      σ eps heps n s hs
  simpa [qZ610_eq_qOf] using h

theorem normSq_structureFactor_ge_c0_sq_div_N_pow_six_orbit_610
    {N : ℕ} (hN : 1 ≤ N)
    (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    c0_610 ^ 2 / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (orbitQ (qOf 6 1 0) σ eps))‖ ^ 2 :=
  normSq_of_norm_ge_c0_div_N3 (by unfold c0_610; norm_num)
    _ (norm_structureFactor_ge_c0_div_N_pow_three_orbit_610 hN σ eps heps n s hs)

/-! ## (5,2,0), c0 = 1/30 -/

/-- `[P, Lean]` `‖F‖ ≥ (1/30) / N³` on the full signed-permutation orbit of `(5,2,0)`. -/
theorem norm_structureFactor_ge_c0_div_N_pow_three_orbit_520
    {N : ℕ} (hN : 1 ≤ N)
    (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    c0_520 / (N : ℝ) ^ 3 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (orbitQ (qOf 5 2 0) σ eps))‖ := by
  have h :=
    norm_structureFactor_ge_c0_div_N3_orbit_transfer hN qZ520 c0_520
      (fun {N'} hN' n' s' hs' => by
        simpa [show q520 = qReal qZ520 from rfl] using
          LeanLab.Scratch.LemmaDLowerBoundL1SevenCubic.norm_structureFactor_ge_c0_div_N_pow_three_at_520
            hN' n' s' hs')
      σ eps heps n s hs
  simpa [qZ520_eq_qOf] using h

theorem normSq_structureFactor_ge_c0_sq_div_N_pow_six_orbit_520
    {N : ℕ} (hN : 1 ≤ N)
    (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    c0_520 ^ 2 / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (orbitQ (qOf 5 2 0) σ eps))‖ ^ 2 :=
  normSq_of_norm_ge_c0_div_N3 (by unfold c0_520; norm_num)
    _ (norm_structureFactor_ge_c0_div_N_pow_three_orbit_520 hN σ eps heps n s hs)

/-! ## (4,3,0), c0 = 1/34 -/

/-- `[P, Lean]` `‖F‖ ≥ (1/34) / N³` on the full signed-permutation orbit of `(4,3,0)`. -/
theorem norm_structureFactor_ge_c0_div_N_pow_three_orbit_430
    {N : ℕ} (hN : 1 ≤ N)
    (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    c0_430 / (N : ℝ) ^ 3 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (orbitQ (qOf 4 3 0) σ eps))‖ := by
  have h :=
    norm_structureFactor_ge_c0_div_N3_orbit_transfer hN qZ430 c0_430
      (fun {N'} hN' n' s' hs' => by
        simpa [show q430 = qReal qZ430 from rfl] using
          LeanLab.Scratch.LemmaDLowerBoundL1SevenCubic.norm_structureFactor_ge_c0_div_N_pow_three_at_430
            hN' n' s' hs')
      σ eps heps n s hs
  simpa [qZ430_eq_qOf] using h

theorem normSq_structureFactor_ge_c0_sq_div_N_pow_six_orbit_430
    {N : ℕ} (hN : 1 ≤ N)
    (σ : Equiv.Perm (Fin 3)) (eps : Fin 3 → ℤ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    c0_430 ^ 2 / (N : ℝ) ^ 6 ≤
      ‖structureFactor (fun k => centroidPoint (n k) (s k))
        (qReal (orbitQ (qOf 4 3 0) σ eps))‖ ^ 2 :=
  normSq_of_norm_ge_c0_div_N3 (by unfold c0_430; norm_num)
    _ (norm_structureFactor_ge_c0_div_N_pow_three_orbit_430 hN σ eps heps n s hs)

#print axioms norm_structureFactor_ge_c0_div_N3_orbit_transfer
#print axioms norm_structureFactor_ge_c0_div_N_pow_three_orbit_220
#print axioms normSq_structureFactor_ge_c0_sq_div_N_pow_six_orbit_220
#print axioms norm_structureFactor_ge_c0_div_N_pow_three_orbit_330
#print axioms normSq_structureFactor_ge_c0_sq_div_N_pow_six_orbit_330
#print axioms norm_structureFactor_ge_c0_div_N_pow_three_orbit_110
#print axioms normSq_structureFactor_ge_c0_sq_div_N_pow_six_orbit_110
#print axioms norm_structureFactor_ge_c0_div_N_pow_three_orbit_610
#print axioms normSq_structureFactor_ge_c0_sq_div_N_pow_six_orbit_610
#print axioms norm_structureFactor_ge_c0_div_N_pow_three_orbit_520
#print axioms normSq_structureFactor_ge_c0_sq_div_N_pow_six_orbit_520
#print axioms norm_structureFactor_ge_c0_div_N_pow_three_orbit_430
#print axioms normSq_structureFactor_ge_c0_sq_div_N_pow_six_orbit_430

end LeanLab.Scratch.LemmaDOrbitLowerBoundCubic
