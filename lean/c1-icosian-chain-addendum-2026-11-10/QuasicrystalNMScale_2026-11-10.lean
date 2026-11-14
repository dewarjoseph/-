/-
  QuasicrystalNMScale_2026-11-10.lean (scratch, 2026-11-10)

  The exact (N, M) scale identity of `ico_NM` in `qc/cutproject.py`
  (sha256 84663d07…), for every n ∈ ℤ^6:
    ∑_j (∑_i n_i (A_ij + τ B_ij))^2 = N + τ M,   |n @ par|^2 = (N + τ M) / (2 (2 + τ)),
  plus the Galois-conjugate twins (τ ↦ 1 − τ) for `perp`.
  Statement text was frozen before proving.
  Imports `QuasicrystalCutProject6D_2026-11-10` unchanged.
-/
import «QuasicrystalCutProject6D_2026-11-10»
import Mathlib.Tactic.LinearCombination

open Equiv Matrix

/-- `n @ ICO_A` in `ico_NM` of `cutproject.py`. -/
def icoNa (n : Fin 6 → ℤ) : Fin 3 → ℤ := fun j => ∑ i, n i * icoA i j

/-- `n @ ICO_B` in `ico_NM` of `cutproject.py`. -/
def icoNb (n : Fin 6 → ℤ) : Fin 3 → ℤ := fun j => ∑ i, n i * icoB i j

/-- `N = sum h^2 + sum h'^2` of `ico_NM`. -/
def icoN (n : Fin 6 → ℤ) : ℤ := ∑ j, icoNa n j ^ 2 + ∑ j, icoNb n j ^ 2

/-- `M = sum h'^2 + 2 sum h h'` of `ico_NM`. -/
def icoM (n : Fin 6 → ℤ) : ℤ := ∑ j, icoNb n j ^ 2 + 2 * ∑ j, icoNa n j * icoNb n j

theorem sum_sq_combo_of_sq_eq (a b : Fin 3 → ℝ) {x : ℝ} (hx : x ^ 2 = x + 1) :
    ∑ j, (a j + x * b j) ^ 2 = (∑ j, a j ^ 2 + ∑ j, b j ^ 2) + x * (∑ j, b j ^ 2 + 2 * ∑ j, a j * b j) := by
  simp only [Fin.sum_univ_three]
  linear_combination (b 0 ^ 2 + b 1 ^ 2 + b 2 ^ 2) * hx

theorem tauR_sq : tauR ^ 2 = tauR + 1 := by
  rw [tauR]; ring_nf; rw [sqrt5_sq]; ring

theorem one_sub_tauR_sq : (1 - tauR) ^ 2 = (1 - tauR) + 1 := by
  linear_combination tauR_sq

theorem combo_eq (n : Fin 6 → ℤ) (x : ℝ) (j : Fin 3) :
    ∑ i, (n i : ℝ) * ((icoA i j : ℝ) + x * icoB i j) = (icoNa n j : ℝ) + x * (icoNb n j : ℝ) := by
  simp only [icoNa, icoNb, Int.cast_sum, Int.cast_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem combo_norm_sq (n : Fin 6 → ℤ) {x : ℝ} (hx : x ^ 2 = x + 1) :
    ∑ j, (∑ i, (n i : ℝ) * ((icoA i j : ℝ) + x * icoB i j)) ^ 2 = icoN n + x * icoM n := by
  simp only [combo_eq]
  rw [sum_sq_combo_of_sq_eq _ _ hx]
  simp only [icoN, icoM]; push_cast; ring

theorem icoNM_norm_sq (n : Fin 6 → ℤ) :
    ∑ j, (∑ i, (n i : ℝ) * ((icoA i j : ℝ) + tauR * icoB i j)) ^ 2 = icoN n + tauR * icoM n :=
  combo_norm_sq n tauR_sq

theorem icoNM_norm_sq_conj (n : Fin 6 → ℤ) :
    ∑ j, (∑ i, (n i : ℝ) * ((icoA i j : ℝ) + (1 - tauR) * icoB i j)) ^ 2 =
      icoN n + (1 - tauR) * icoM n :=
  combo_norm_sq n one_sub_tauR_sq

theorem vecMul_dot_of_rows (n : Fin 6 → ℤ) (x c : ℝ) (P : Matrix (Fin 6) (Fin 3) ℝ)
    (hP : ∀ i j, P i j = ((icoA i j : ℝ) + x * icoB i j) / c) :
    Matrix.vecMul (fun i => (n i : ℝ)) P ⬝ᵥ Matrix.vecMul (fun i => (n i : ℝ)) P =
      (∑ j, (∑ i, (n i : ℝ) * ((icoA i j : ℝ) + x * icoB i j)) ^ 2) / c ^ 2 := by
  have hv : ∀ j, Matrix.vecMul (fun i => (n i : ℝ)) P j =
      (∑ i, (n i : ℝ) * ((icoA i j : ℝ) + x * icoB i j)) * c⁻¹ := by
    intro j
    simp only [Matrix.vecMul, dotProduct, hP, div_eq_mul_inv, Finset.sum_mul, mul_assoc]
  simp only [dotProduct, hv]
  rw [div_eq_mul_inv, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem icoPar_vecMul_dot (n : Fin 6 → ℤ) :
    Matrix.vecMul (fun i => (n i : ℝ)) icoPar ⬝ᵥ Matrix.vecMul (fun i => (n i : ℝ)) icoPar =
      (icoN n + tauR * icoM n) / (2 * (2 + tauR)) := by
  rw [vecMul_dot_of_rows n tauR (Real.sqrt (20 + 4 * Real.sqrt 5) / 2) icoPar
    (fun i j => by rw [icoPar, par_rowsum, div_div, sqrt_norm_aux nPar_pos]), icoNM_norm_sq,
    div_pow, Real.sq_sqrt nPar_pos.le, tauR]
  have h5 : (0 : ℝ) < 5 + Real.sqrt 5 := by positivity
  field_simp
  ring

theorem icoPerp_vecMul_dot (n : Fin 6 → ℤ) :
    Matrix.vecMul (fun i => (n i : ℝ)) icoPerp ⬝ᵥ Matrix.vecMul (fun i => (n i : ℝ)) icoPerp =
      (icoN n + (1 - tauR) * icoM n) / (2 * (3 - tauR)) := by
  rw [vecMul_dot_of_rows n (1 - tauR) (Real.sqrt (20 - 4 * Real.sqrt 5) / 2) icoPerp
    (fun i j => by rw [icoPerp, perp_rowsum, div_div, sqrt_norm_aux nPerp_pos]), icoNM_norm_sq_conj,
    div_pow, Real.sq_sqrt nPerp_pos.le]
  have h5 : (0 : ℝ) < 5 - Real.sqrt 5 := by linarith [sqrt5_lt_five]
  rw [show (2 : ℝ) * (3 - tauR) = 5 - Real.sqrt 5 by rw [tauR]; ring,
    show (20 - 4 * Real.sqrt 5) / 2 ^ 2 = 5 - Real.sqrt 5 by ring]

#print axioms sum_sq_combo_of_sq_eq
#print axioms tauR_sq
#print axioms one_sub_tauR_sq
#print axioms icoNM_norm_sq
#print axioms icoNM_norm_sq_conj
#print axioms icoPar_vecMul_dot
#print axioms icoPerp_vecMul_dot
