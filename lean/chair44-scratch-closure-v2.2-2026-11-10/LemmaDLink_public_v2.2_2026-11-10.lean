import LeanLab.Scratch.LemmaAInt
import LeanLab.Scratch.LemmaD4
import LeanLab.Scratch.LemmaD

/-!
# Chair44 link: LemmaAInt integer-origin lo-form ↔ Lemma D4
(public-screen)

Public-screen v2 copy of LeanLab.Scratch.LemmaDLink (official pin src
`5db448f9f66b023b17edff40114ca4fff3bdb75c3207acace9e46a618749e9b7`).
Header redacted; theorem bodies are unchanged. This copy is not a
replacement pin.

Reuses (does not re-duplicate) the D4 development's `centroidPoint` / `lemma_D4` and
LemmaAInt's `averagedIntensity_lo_dForm_int`.

**Result label:** `[P, Lean] D4 bound for the section 1 lo_B-form average with integer
lo_B, q = e_a only, D-form n − s/14, equal box weights; finite scratch, not a Lake
target, not peer reviewed`.

Fidelity:
* Integer `lo_B` only; q = e_a only; equal box weights.
* Does not restate a general-q lower bound (see LemmaSevenBox / LemmaDAxisMultiple).
* Scratch only; not a Lake target; not peer reviewed. The real 13/14 centroid
  geometry is not encoded.

This file is source-only and is not a Lake package. It claims nothing
beyond the theorems stated below.

Dated 2026-11-10.
-/

namespace LeanLab.Scratch.LemmaDLink

open Complex Finset
open LeanLab.Scratch.LemmaAInt (dForm intOrigin averagedIntensity averagedIntensity_lo
  boxStructureFactor averagedIntensity_lo_dForm_int)
open LeanLab.Scratch.LemmaD4 (centroidPoint structureFactor eVec lemma_D4)

/-! ## (a) dForm ↔ centroidPoint identity -/

/-- LemmaAInt's `dForm` is definitionally the same point family as LemmaD4's `centroidPoint`. -/
theorem dForm_eq_centroidPoint_D4 (n s : Fin 3 → ℤ) :
    dForm n s = LemmaD4.centroidPoint n s := by
  funext j
  rfl

/-- Same identity against the original LemmaD `centroidPoint`. -/
theorem dForm_eq_centroidPoint_D (n s : Fin 3 → ℤ) :
    dForm n s = LemmaD.centroidPoint n s := by
  funext j
  rfl

/-- Direct equality of the two D4 / D centroidPoint definitions. -/
theorem centroidPoint_D4_eq_D (n s : Fin 3 → ℤ) :
    LemmaD4.centroidPoint n s = LemmaD.centroidPoint n s := by
  funext j
  rfl

/-! ## (b) Bridge AInt intensity ↔ D4 structureFactor -/

/-- The two standalone `dot3` definitions agree. -/
theorem dot3_AInt_eq_D4 (q x : Fin 3 → ℝ) :
    LemmaAInt.dot3 q x = LemmaD4.dot3 q x := by
  rfl

/-- `boxStructureFactor` (AInt) equals `structureFactor` (D4) at the same points. -/
theorem boxStructureFactor_eq_structureFactor {N : ℕ}
    (r : Fin N → Fin 3 → ℝ) (q : Fin 3 → ℝ) :
    boxStructureFactor r q = structureFactor r q := by
  -- Both unfold to `(N:ℂ)⁻¹ * Σ exp(2π i · ·)` with identical `dot3` bodies.
  unfold boxStructureFactor structureFactor LemmaAInt.dot3 LemmaD4.dot3
  rfl

/-- Bridge: AInt equal-weight average equals the D4-shaped average of `‖structureFactor‖²`. -/
theorem averagedIntensity_eq_avg_normSq_structureFactor {M : ℕ} {N : Fin M → ℕ}
    (r : (B : Fin M) → Fin (N B) → Fin 3 → ℝ) (q : Fin 3 → ℝ) :
    averagedIntensity r q =
      (M : ℝ)⁻¹ * ∑ B : Fin M, ‖structureFactor (r B) q‖ ^ 2 := by
  unfold averagedIntensity
  simp_rw [boxStructureFactor_eq_structureFactor]

/-! ## (c) Headline: D4 bound at integer origins in AInt lo-form -/

/-- Combining `averagedIntensity_lo_dForm_int`, the intensity bridge, and `lemma_D4`
gives the D4 two-sided bound for the §1 `lo_B`-form average with integer origins,
at `q = e_a`, on D-form points `n − s/14`. The caller no longer instantiates the
shift `n ↦ n − lo` by hand. -/
theorem lemma_D4_lo_int {M : ℕ} (hM : 1 ≤ M)
    (N : Fin M → ℕ) (hN : ∀ B, 1 ≤ N B)
    (n : (B : Fin M) → Fin (N B) → Fin 3 → ℤ)
    (s : (B : Fin M) → Fin (N B) → Fin 3 → ℤ)
    (hs : ∀ B k j, s B k j = 1 ∨ s B k j = -1)
    (lo : Fin M → Fin 3 → ℤ)
    (a : Fin 3) :
    Real.cos (Real.pi / 7) ^ 2 ≤
        averagedIntensity_lo
          (fun B k => centroidPoint (n B k) (s B k)) (intOrigin lo) (eVec a) ∧
      averagedIntensity_lo
          (fun B k => centroidPoint (n B k) (s B k)) (intOrigin lo) (eVec a) ≤ 1 := by
  -- Rewrite centroidPoint as dForm so averagedIntensity_lo_dForm_int applies.
  have hpts : (fun B k => centroidPoint (n B k) (s B k)) =
      (fun B k => dForm (n B k) (s B k)) := by
    funext B k; exact (dForm_eq_centroidPoint_D4 (n B k) (s B k)).symm
  rw [hpts, averagedIntensity_lo_dForm_int n s lo (eVec a)]
  -- Bridge to D4-shaped average of ‖structureFactor‖².
  rw [averagedIntensity_eq_avg_normSq_structureFactor]
  -- dForm and centroidPoint reduce to the same λ, so the goal matches lemma_D4
  -- at the shifted integer parts n − lo (signs unchanged).
  exact lemma_D4 hM N hN (fun B k => n B k - lo B) s hs a

#print axioms dForm_eq_centroidPoint_D4
#print axioms dForm_eq_centroidPoint_D
#print axioms centroidPoint_D4_eq_D
#print axioms dot3_AInt_eq_D4
#print axioms boxStructureFactor_eq_structureFactor
#print axioms averagedIntensity_eq_avg_normSq_structureFactor
#print axioms lemma_D4_lo_int

end LeanLab.Scratch.LemmaDLink
