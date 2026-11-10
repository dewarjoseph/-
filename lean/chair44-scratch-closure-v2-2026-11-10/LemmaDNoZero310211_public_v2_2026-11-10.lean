import LeanLab.Scratch.LemmaAInt
import LeanLab.Scratch.LemmaD4
import LeanLab.Scratch.LemmaDLink
import LeanLab.Scratch.LemmaDIntVec
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-!
# Chair44 D-form: no equal-weight zero at q = (3,1,0) and q = (2,1,1)
(public-screen)

Public-screen v2 copy of LeanLab.Scratch.LemmaDNoZero310211 (official pin src
`5ff6fcae83ea327b6e1b7a20351f97451a7e0254974b759ce1189d9d094ee62b`).
Header redacted; theorem bodies are unchanged. This copy is not a
replacement pin.

At the integer wavevectors
`q = (3,1,0)` and `q = (2,1,1)`, every finite nonempty equal-weight D-form
box has structure factor `F(q) ≠ 0`.

**Setup.** Points `r_k = n_k − s_k/14` with `n_k ∈ ℤ³`, `s_k ∈ {±1}³`, equal
weights. At integer `q` the lattice part drops and
`exp(2πi q·r_k) = exp(−iπ t_k/7)` with `t_k = q·s_k`. When `t` is even,
`exp(−iπ t/7) = ζ^{k}` for `ζ = exp(2πi/7)` and `t = −2k − 14m`
(`LemmaDL1Ge4.exp_neg_pi_t_eq_zeta`, inlined below).

**Residues.**
* `q = (3,1,0)`: `t = 3 s₀ + s₁ ∈ {4,2,−2,−4}`, so phases are
  `ζ^5, ζ^6, ζ^1, ζ^2` (residues `{1,2,5,6}`; miss `0,3,4`).
* `q = (2,1,1)`: `t = 2 s₀ + s₁ + s₂ ∈ {4,2,0,−2,−4}`, so phases are
  `ζ^5, ζ^6, ζ^0, ζ^1, ζ^2` (residues `{0,1,2,5,6}`; miss `3,4`).

**Key lemma [P, Lean] (Mathlib).** For a prime `p` and primitive `p`-th root
`ζ`, and integer coefficients `α : Fin p → ℤ`,
`∑ᵢ αᵢ ζⁱ = 0 ↔ ∀ i j, αᵢ = αⱼ`
(`IsPrimitiveRoot.sum_eq_zero_iff_forall_eq_int`). Applied at `p = 7`,
`ζ = ζ₇`: if `F(q) = 0` then all residue counts are equal. But a missing
residue has count `0` while `N ≥ 1` forces some count `≥ 1`, contradiction.

**Also [P, Lean].** `|F|² > 0` at both wavevectors. A reusable general
non-vanishing criterion: if every admissible sign vector's phase residue
misses a fixed `r₀ ∈ Fin 7`, then no nonempty equal-weight D-form box has
`F(q) = 0`.

**Remark [P, Lean].** By the key lemma, `F(q) = 0` at an integer `q` with
even `t = q·s` forces all residues mod 7 to occur equally often among the
box's phases. This is consistent with the earlier `F = 0` witnesses at
`(1,2,4)` and `(3,2,1)` (LemmaDIntVec / LemmaDL1Ge4), where all seven
residues appear once.

**Not proved / out of scope:**
* Orbit transfer (coordinate permutations and sign flips of `q`) is **not**
  formalized (`[X]`): the reduction "sign-change/permute `q` ≡ relabel `s`"
  is left as a remark; only the two named vectors are proved.
* No uniform positive lower bound on `|F|²`: the infimum over all box sizes
  may be `0` (`[X]`/`[E]` remark only; not claimed).
* Nothing off these two vectors; D-form hypothesis class only.
* Scratch; not a Lake target; not peer reviewed.

This file is source-only and is not a Lake package. It claims nothing
beyond the theorems stated below.

Dated 2026-11-10.
-/

namespace LeanLab.Scratch.LemmaDNoZero310211

open Complex Finset
open LeanLab.Scratch.LemmaD4 (dot3 structureFactor centroidPoint exp_two_pi_I_int)
open LeanLab.Scratch.LemmaDIntVec (qReal signedWeight exp_centroid_int_q
  zeta7 zeta7_pow isPrimitiveRoot_zeta7)

/-! ## Shared phase identity (from LemmaDL1Ge4, inlined) -/

/-- If `t = −2k − 14m` then `exp(−(π t/7) I) = ζ^k`. -/
lemma exp_neg_pi_t_eq_zeta (t : ℤ) (k : ℕ) (m : ℤ)
    (h : t = -2 * (k : ℤ) - 14 * m) :
    exp (((-(Real.pi * (t : ℝ) / 7) : ℝ) : ℂ) * I) = zeta7 ^ k := by
  have hrhs : zeta7 ^ k = exp ((((↑(2 * k) * Real.pi / 7) : ℝ) : ℂ) * I) := by
    rw [zeta7_pow]
    congr 1
    push_cast
    ring
  rw [hrhs]
  have hθ : (-(Real.pi * (t : ℝ) / 7) : ℝ) =
      (↑(2 * k) * Real.pi / 7) + 2 * Real.pi * (m : ℝ) := by
    have ht : (t : ℝ) = -2 * (k : ℝ) - 14 * (m : ℝ) := by exact_mod_cast h
    rw [ht]; push_cast; ring
  have hform :
      (((-(Real.pi * (t : ℝ) / 7) : ℝ) : ℂ) * I) =
        ((((↑(2 * k) * Real.pi / 7) : ℝ) : ℂ) * I) +
          ((((2 * Real.pi * (m : ℝ)) : ℝ) : ℂ) * I) := by
    rw [hθ, ofReal_add, add_mul]
  rw [hform, exp_add]
  have hper : exp ((((2 * Real.pi * (m : ℝ)) : ℝ) : ℂ) * I) = 1 := by
    convert exp_two_pi_I_int m using 2
    push_cast; ring
  rw [hper, mul_one]

/-! ## Key cyclotomic lemma (Mathlib wrapper) -/

/-- `[P, Lean]` Integer linear combination of `{1,ζ,…,ζ⁶}` vanishes iff all
coefficients are equal. -/
theorem zeta7_sum_eq_zero_iff_forall_eq (α : Fin 7 → ℤ) :
    (∑ i : Fin 7, (α i : ℂ) * zeta7 ^ i.val) = 0 ↔ ∀ i j : Fin 7, α i = α j := by
  simpa using
    (IsPrimitiveRoot.sum_eq_zero_iff_forall_eq_int (p := 7) Nat.prime_seven
      isPrimitiveRoot_zeta7 α)

/-! ## Fiberwise count of phases -/

/-- Count of box indices whose phase residue is `r`. -/
noncomputable def countRes {N : ℕ} (φ : Fin N → Fin 7) (r : Fin 7) : ℕ :=
  #{k : Fin N | φ k = r}

lemma countRes_sum_eq_card {N : ℕ} (φ : Fin N → Fin 7) :
    ∑ r : Fin 7, countRes φ r = N := by
  classical
  have h := card_eq_sum_card_fiberwise (f := φ) (s := (univ : Finset (Fin N)))
    (t := (univ : Finset (Fin 7))) (H := fun _ _ => mem_univ _)
  simpa [countRes, card_univ, Fintype.card_fin, eq_comm] using h

lemma sum_zeta_eq_countRes {N : ℕ} (φ : Fin N → Fin 7) :
    (∑ k : Fin N, zeta7 ^ (φ k).val) =
      ∑ r : Fin 7, (countRes φ r : ℂ) * zeta7 ^ r.val := by
  classical
  have h :=
    (sum_fiberwise' (univ : Finset (Fin N)) φ (fun r : Fin 7 => zeta7 ^ r.val)).symm
  -- ∑ k ∈ univ, ζ^(φ k) = ∑ r, ∑ k ∈ filter (φ=r), ζ^r
  have h1 :
      (∑ k : Fin N, zeta7 ^ (φ k).val) =
        ∑ r : Fin 7, ∑ k ∈ univ.filter (fun k => φ k = r), zeta7 ^ r.val := by
    simpa using h
  have h2 : ∀ r : Fin 7,
      (∑ k ∈ univ.filter (fun k => φ k = r), zeta7 ^ r.val) =
        (countRes φ r : ℂ) * zeta7 ^ r.val := by
    intro r
    simp only [sum_const, nsmul_eq_mul, countRes]
  simp only [h1, h2]

/-! ## General non-vanishing from a missing residue -/

lemma sum_eq_zero_of_structureFactor_eq_zero {N : ℕ} (hN : 1 ≤ N)
    (pts : Fin N → Fin 3 → ℝ) (q : Fin 3 → ℝ)
    (hF : structureFactor pts q = 0) :
    (∑ k : Fin N, exp (2 * Real.pi * I * dot3 q (pts k))) = 0 := by
  unfold structureFactor at hF
  have hNne : (N : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (Nat.zero_lt_of_lt hN))
  have h := congr_arg (fun z : ℂ => (N : ℂ) * z) hF
  simp only [mul_zero] at h
  rwa [mul_inv_cancel_left₀ hNne] at h

/-- `[P, Lean]` Reusable criterion: if every admissible sign vector maps to a
phase residue in a proper subset of `Fin 7` (equivalently, some `r₀` is never
hit), then no nonempty equal-weight D-form box has `F(q) = 0` at that `q`. -/
theorem structureFactor_ne_zero_of_missing_residue {N : ℕ} (hN : 1 ≤ N)
    (qZ : Fin 3 → ℤ)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1)
    (φ : (Fin 3 → ℤ) → Fin 7)
    (hphase : ∀ k,
      exp (2 * Real.pi * I * dot3 (qReal qZ) (centroidPoint (n k) (s k))) =
        zeta7 ^ (φ (s k)).val)
    (r0 : Fin 7)
    (hmiss : ∀ (s' : Fin 3 → ℤ), (∀ j, s' j = 1 ∨ s' j = -1) → φ s' ≠ r0) :
    structureFactor (fun k => centroidPoint (n k) (s k)) (qReal qZ) ≠ 0 := by
  intro hF
  have hsum0 :=
    sum_eq_zero_of_structureFactor_eq_zero hN
      (fun k => centroidPoint (n k) (s k)) (qReal qZ) hF
  set φN : Fin N → Fin 7 := fun k => φ (s k)
  have hsumζ :
      (∑ k : Fin N,
          exp (2 * Real.pi * I * dot3 (qReal qZ) (centroidPoint (n k) (s k)))) =
        ∑ k : Fin N, zeta7 ^ (φN k).val := by
    apply sum_congr rfl; intro k _; exact hphase k
  have hcounts :
      (∑ k : Fin N, zeta7 ^ (φN k).val) =
        ∑ r : Fin 7, (countRes φN r : ℂ) * zeta7 ^ r.val :=
    sum_zeta_eq_countRes φN
  have hα :
      (∑ r : Fin 7, ((countRes φN r : ℤ) : ℂ) * zeta7 ^ r.val) = 0 := by
    have : (∑ k : Fin N, zeta7 ^ (φN k).val) = 0 := by
      rw [← hsumζ]; exact hsum0
    rw [← this, hcounts]
    refine sum_congr rfl fun r _ => ?_
    simp
  have hall : ∀ i j : Fin 7, (countRes φN i : ℤ) = (countRes φN j : ℤ) :=
    (zeta7_sum_eq_zero_iff_forall_eq (fun r => (countRes φN r : ℤ))).mp hα
  have hr0 : countRes φN r0 = 0 := by
    classical
    refine card_eq_zero.mpr ?_
    apply eq_empty_iff_forall_notMem.mpr
    intro k hk
    simp only [mem_filter, mem_univ, true_and, φN] at hk
    exact hmiss (s k) (hs k) hk
  have hNcard : ∑ r : Fin 7, countRes φN r = N := countRes_sum_eq_card φN
  have hall0 : ∀ r, countRes φN r = 0 := by
    intro r
    have hzi : (countRes φN r : ℤ) = (countRes φN r0 : ℤ) := hall r r0
    have : (countRes φN r : ℤ) = 0 := by simp [hzi, hr0]
    exact_mod_cast this
  have hN0 : N = 0 := by
    rw [← hNcard]
    simp [hall0]
  exact absurd hN0 (ne_of_gt (Nat.zero_lt_of_lt hN))

/-! ## q = (3, 1, 0) -/

def qZ310 : Fin 3 → ℤ
  | ⟨0, _⟩ => 3
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 0

noncomputable def q310 : Fin 3 → ℝ := qReal qZ310

/-- Phase residue for `q = (3,1,0)`: maps `t ∈ {4,2,−2,−4}` to
`{5,6,1,2}` respectively. Default `0` is unreachable under sign hypotheses. -/
def res310 (s : Fin 3 → ℤ) : Fin 7 :=
  let t := signedWeight qZ310 s
  if t = 4 then ⟨5, by omega⟩
  else if t = 2 then ⟨6, by omega⟩
  else if t = -2 then ⟨1, by omega⟩
  else if t = -4 then ⟨2, by omega⟩
  else ⟨0, by omega⟩

lemma signedWeight_qZ310_mem (s : Fin 3 → ℤ) (hs : ∀ j, s j = 1 ∨ s j = -1) :
    signedWeight qZ310 s = 4 ∨ signedWeight qZ310 s = 2 ∨
      signedWeight qZ310 s = -2 ∨ signedWeight qZ310 s = -4 := by
  have h0 := hs 0
  have h1 := hs 1
  -- s 2 does not appear (q₂ = 0)
  simp only [signedWeight, qZ310, Fin.sum_univ_three]
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> simp [h0, h1]

lemma res310_eq_of_t4 (s : Fin 3 → ℤ) (ht : signedWeight qZ310 s = 4) :
    res310 s = ⟨5, by omega⟩ := by
  simp [res310, ht]

lemma res310_eq_of_t2 (s : Fin 3 → ℤ) (ht : signedWeight qZ310 s = 2) :
    res310 s = ⟨6, by omega⟩ := by
  simp [res310, ht]

lemma res310_eq_of_tneg2 (s : Fin 3 → ℤ) (ht : signedWeight qZ310 s = -2) :
    res310 s = ⟨1, by omega⟩ := by
  simp [res310, ht]

lemma res310_eq_of_tneg4 (s : Fin 3 → ℤ) (ht : signedWeight qZ310 s = -4) :
    res310 s = ⟨2, by omega⟩ := by
  simp [res310, ht]

lemma res310_ne_zero (s : Fin 3 → ℤ) (hs : ∀ j, s j = 1 ∨ s j = -1) :
    res310 s ≠ ⟨0, by omega⟩ := by
  rcases signedWeight_qZ310_mem s hs with h | h | h | h
  · simp [res310_eq_of_t4 s h]
  · simp [res310_eq_of_t2 s h]
  · simp [res310_eq_of_tneg2 s h]
  · simp [res310_eq_of_tneg4 s h]

lemma res310_ne_three (s : Fin 3 → ℤ) (hs : ∀ j, s j = 1 ∨ s j = -1) :
    res310 s ≠ ⟨3, by omega⟩ := by
  rcases signedWeight_qZ310_mem s hs with h | h | h | h
  · simp [res310_eq_of_t4 s h]
  · simp [res310_eq_of_t2 s h]
  · simp [res310_eq_of_tneg2 s h]
  · simp [res310_eq_of_tneg4 s h]

lemma res310_ne_four (s : Fin 3 → ℤ) (hs : ∀ j, s j = 1 ∨ s j = -1) :
    res310 s ≠ ⟨4, by omega⟩ := by
  rcases signedWeight_qZ310_mem s hs with h | h | h | h
  · simp [res310_eq_of_t4 s h]
  · simp [res310_eq_of_t2 s h]
  · simp [res310_eq_of_tneg2 s h]
  · simp [res310_eq_of_tneg4 s h]

lemma exp_centroid_310_eq_zeta (n s : Fin 3 → ℤ)
    (hs : ∀ j, s j = 1 ∨ s j = -1) :
    exp (2 * Real.pi * I * dot3 (qReal qZ310) (centroidPoint n s)) =
      zeta7 ^ (res310 s).val := by
  rw [exp_centroid_int_q]
  rcases signedWeight_qZ310_mem s hs with h | h | h | h
  · -- t = 4 = -2*5 - 14*(-1)
    rw [h, res310_eq_of_t4 s h]
    exact exp_neg_pi_t_eq_zeta 4 5 (-1) (by norm_num)
  · -- t = 2 = -2*6 - 14*(-1)
    rw [h, res310_eq_of_t2 s h]
    exact exp_neg_pi_t_eq_zeta 2 6 (-1) (by norm_num)
  · -- t = -2 = -2*1 - 14*0
    rw [h, res310_eq_of_tneg2 s h]
    exact exp_neg_pi_t_eq_zeta (-2) 1 0 (by norm_num)
  · -- t = -4 = -2*2 - 14*0
    rw [h, res310_eq_of_tneg4 s h]
    exact exp_neg_pi_t_eq_zeta (-4) 2 0 (by norm_num)

/-- `[P, Lean]` No finite nonempty equal-weight D-form box has `F = 0` at
`q = (3,1,0)`. -/
theorem structureFactor_ne_zero_at_310 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    structureFactor (fun k => centroidPoint (n k) (s k)) q310 ≠ 0 := by
  simpa [q310] using
    structureFactor_ne_zero_of_missing_residue hN qZ310 n s hs res310
      (fun k => exp_centroid_310_eq_zeta (n k) (s k) (hs k))
      ⟨3, by omega⟩ res310_ne_three

/-- Intensity form: `|F|² ≠ 0` at `q = (3,1,0)`. -/
theorem normSq_structureFactor_ne_zero_at_310 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    ‖structureFactor (fun k => centroidPoint (n k) (s k)) q310‖ ^ 2 ≠ 0 := by
  intro hz
  have : structureFactor (fun k => centroidPoint (n k) (s k)) q310 = 0 :=
    norm_eq_zero.mp (sq_eq_zero_iff.mp hz)
  exact structureFactor_ne_zero_at_310 hN n s hs this

/-- Intensity is strictly positive at `q = (3,1,0)`. -/
theorem normSq_structureFactor_pos_at_310 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    0 < ‖structureFactor (fun k => centroidPoint (n k) (s k)) q310‖ ^ 2 :=
  lt_of_le_of_ne (sq_nonneg _)
    (normSq_structureFactor_ne_zero_at_310 hN n s hs).symm

/-! ## q = (2, 1, 1) -/

def qZ211 : Fin 3 → ℤ
  | ⟨0, _⟩ => 2
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 1

noncomputable def q211 : Fin 3 → ℝ := qReal qZ211

/-- Phase residue for `q = (2,1,1)`: maps `t ∈ {4,2,0,−2,−4}` to
`{5,6,0,1,2}` respectively. Default `3` is unreachable under sign hypotheses. -/
def res211 (s : Fin 3 → ℤ) : Fin 7 :=
  let t := signedWeight qZ211 s
  if t = 4 then ⟨5, by omega⟩
  else if t = 2 then ⟨6, by omega⟩
  else if t = 0 then ⟨0, by omega⟩
  else if t = -2 then ⟨1, by omega⟩
  else if t = -4 then ⟨2, by omega⟩
  else ⟨3, by omega⟩

lemma signedWeight_qZ211_mem (s : Fin 3 → ℤ) (hs : ∀ j, s j = 1 ∨ s j = -1) :
    signedWeight qZ211 s = 4 ∨ signedWeight qZ211 s = 2 ∨
      signedWeight qZ211 s = 0 ∨ signedWeight qZ211 s = -2 ∨
        signedWeight qZ211 s = -4 := by
  have h0 := hs 0
  have h1 := hs 1
  have h2 := hs 2
  simp only [signedWeight, qZ211, Fin.sum_univ_three]
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
    simp [h0, h1, h2]

lemma res211_eq_of_t4 (s : Fin 3 → ℤ) (ht : signedWeight qZ211 s = 4) :
    res211 s = ⟨5, by omega⟩ := by
  simp [res211, ht]

lemma res211_eq_of_t2 (s : Fin 3 → ℤ) (ht : signedWeight qZ211 s = 2) :
    res211 s = ⟨6, by omega⟩ := by
  simp [res211, ht]

lemma res211_eq_of_t0 (s : Fin 3 → ℤ) (ht : signedWeight qZ211 s = 0) :
    res211 s = ⟨0, by omega⟩ := by
  simp [res211, ht]

lemma res211_eq_of_tneg2 (s : Fin 3 → ℤ) (ht : signedWeight qZ211 s = -2) :
    res211 s = ⟨1, by omega⟩ := by
  simp [res211, ht]

lemma res211_eq_of_tneg4 (s : Fin 3 → ℤ) (ht : signedWeight qZ211 s = -4) :
    res211 s = ⟨2, by omega⟩ := by
  simp [res211, ht]

lemma res211_ne_three (s : Fin 3 → ℤ) (hs : ∀ j, s j = 1 ∨ s j = -1) :
    res211 s ≠ ⟨3, by omega⟩ := by
  rcases signedWeight_qZ211_mem s hs with h | h | h | h | h
  · simp [res211_eq_of_t4 s h]
  · simp [res211_eq_of_t2 s h]
  · simp [res211_eq_of_t0 s h]
  · simp [res211_eq_of_tneg2 s h]
  · simp [res211_eq_of_tneg4 s h]

lemma res211_ne_four (s : Fin 3 → ℤ) (hs : ∀ j, s j = 1 ∨ s j = -1) :
    res211 s ≠ ⟨4, by omega⟩ := by
  rcases signedWeight_qZ211_mem s hs with h | h | h | h | h
  · simp [res211_eq_of_t4 s h]
  · simp [res211_eq_of_t2 s h]
  · simp [res211_eq_of_t0 s h]
  · simp [res211_eq_of_tneg2 s h]
  · simp [res211_eq_of_tneg4 s h]

lemma exp_centroid_211_eq_zeta (n s : Fin 3 → ℤ)
    (hs : ∀ j, s j = 1 ∨ s j = -1) :
    exp (2 * Real.pi * I * dot3 (qReal qZ211) (centroidPoint n s)) =
      zeta7 ^ (res211 s).val := by
  rw [exp_centroid_int_q]
  rcases signedWeight_qZ211_mem s hs with h | h | h | h | h
  · rw [h, res211_eq_of_t4 s h]
    exact exp_neg_pi_t_eq_zeta 4 5 (-1) (by norm_num)
  · rw [h, res211_eq_of_t2 s h]
    exact exp_neg_pi_t_eq_zeta 2 6 (-1) (by norm_num)
  · rw [h, res211_eq_of_t0 s h]
    exact exp_neg_pi_t_eq_zeta 0 0 0 (by norm_num)
  · rw [h, res211_eq_of_tneg2 s h]
    exact exp_neg_pi_t_eq_zeta (-2) 1 0 (by norm_num)
  · rw [h, res211_eq_of_tneg4 s h]
    exact exp_neg_pi_t_eq_zeta (-4) 2 0 (by norm_num)

/-- `[P, Lean]` No finite nonempty equal-weight D-form box has `F = 0` at
`q = (2,1,1)`. -/
theorem structureFactor_ne_zero_at_211 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    structureFactor (fun k => centroidPoint (n k) (s k)) q211 ≠ 0 := by
  simpa [q211] using
    structureFactor_ne_zero_of_missing_residue hN qZ211 n s hs res211
      (fun k => exp_centroid_211_eq_zeta (n k) (s k) (hs k))
      ⟨3, by omega⟩ res211_ne_three

/-- Intensity form: `|F|² ≠ 0` at `q = (2,1,1)`. -/
theorem normSq_structureFactor_ne_zero_at_211 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    ‖structureFactor (fun k => centroidPoint (n k) (s k)) q211‖ ^ 2 ≠ 0 := by
  intro hz
  have : structureFactor (fun k => centroidPoint (n k) (s k)) q211 = 0 :=
    norm_eq_zero.mp (sq_eq_zero_iff.mp hz)
  exact structureFactor_ne_zero_at_211 hN n s hs this

/-- Intensity is strictly positive at `q = (2,1,1)`. -/
theorem normSq_structureFactor_pos_at_211 {N : ℕ} (hN : 1 ≤ N)
    (n : Fin N → Fin 3 → ℤ) (s : Fin N → Fin 3 → ℤ)
    (hs : ∀ k j, s k j = 1 ∨ s k j = -1) :
    0 < ‖structureFactor (fun k => centroidPoint (n k) (s k)) q211‖ ^ 2 :=
  lt_of_le_of_ne (sq_nonneg _)
    (normSq_structureFactor_ne_zero_at_211 hN n s hs).symm

#print axioms zeta7_sum_eq_zero_iff_forall_eq
#print axioms structureFactor_ne_zero_of_missing_residue
#print axioms structureFactor_ne_zero_at_310
#print axioms structureFactor_ne_zero_at_211
#print axioms normSq_structureFactor_ne_zero_at_310
#print axioms normSq_structureFactor_ne_zero_at_211
#print axioms normSq_structureFactor_pos_at_310
#print axioms normSq_structureFactor_pos_at_211

end LeanLab.Scratch.LemmaDNoZero310211
