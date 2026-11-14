/-
Scratch file, dated 2026-11-10. Not a Lake target. Not peer reviewed.

Exact 6D cut-and-project identities and a signed-permutation representation of the official
icosahedral rotation group. Statement text and definitions were frozen before proving.

Sources: `qc/cutproject.py` (sha256 84663d07…; `ICO_A`, `ICO_B`, `TAU`, `ico_basis()` transcribed)
and the exact projector identities for the icosahedral cut-and-project basis (the four
identities below). Imports
`IcosahedralAbstractions_2026-11-10` (src dc045da6…) unchanged. No existing file is edited.

(a) `zsqrt5ConjToReal` (√5 ↦ −√5) and its injectivity. (b) The four identities over `ℤ[√5]` by
`decide +kernel` on doubled rows, transferred to the real `icoPar` / `icoPerp`. (c) `sixDRep`,
`g ↦ P∥ R P∥ᵀ + P⊥ R′ P⊥ᵀ` with `R′` the Galois-conjugate rotation: a hom into 6×6 matrices whose
values are signed permutation matrices of `Fin 6`, injective, commuting with the split.
-/
import «IcosahedralAbstractions_2026-11-10»

open Equiv Matrix

/-! ### Data transcribed from `qc/cutproject.py` (`ICO_A`, `ICO_B`, `ico_basis`) -/

/-- `ICO_A` of `cutproject.py`. -/
def icoA : Matrix (Fin 6) (Fin 3) ℤ :=
  !![1, 0, 0; -1, 0, 0; 0, 1, 0; 0, -1, 0; 0, 0, 1; 0, 0, 1]

/-- `ICO_B` of `cutproject.py`. -/
def icoB : Matrix (Fin 6) (Fin 3) ℤ :=
  !![0, 1, 0; 0, 1, 0; 0, 0, 1; 0, 0, 1; 1, 0, 0; -1, 0, 0]

/-- `TAU` of `cutproject.py`. -/
noncomputable def tauR : ℝ := (1 + Real.sqrt 5) / 2

/-- `par` of `ico_basis()`: row `i` is `(A_i + τ B_i) / ‖A_i + τ B_i‖ / √2`. -/
noncomputable def icoPar : Matrix (Fin 6) (Fin 3) ℝ := fun i j =>
  ((icoA i j : ℝ) + tauR * icoB i j) /
    Real.sqrt (∑ k, ((icoA i k : ℝ) + tauR * icoB i k) ^ 2) / Real.sqrt 2

/-- `perp` of `ico_basis()`: row `i` is `(A_i + (1 − τ) B_i) / ‖A_i + (1 − τ) B_i‖ / √2`. -/
noncomputable def icoPerp : Matrix (Fin 6) (Fin 3) ℝ := fun i j =>
  ((icoA i j : ℝ) + (1 - tauR) * icoB i j) /
    Real.sqrt (∑ k, ((icoA i k : ℝ) + (1 - tauR) * icoB i k) ^ 2) / Real.sqrt 2

/-- The Galois-conjugate ring map `ℤ[√5] → ℝ`, `√5 ↦ −√5`. -/
noncomputable def zsqrt5ConjToReal : Zsqrt5 →+* ℝ :=
  Zsqrtd.lift ⟨-Real.sqrt 5, by rw [neg_mul_neg, Real.mul_self_sqrt (by norm_num)]; norm_num⟩

/-- Doubled `par` rows over `ℤ[√5]`: `2 A + (1 + √5) B` (`= 2 (A + τ B)`). -/
def icoW : Matrix (Fin 6) (Fin 3) Zsqrt5 := fun i j => ⟨2 * icoA i j + icoB i j, icoB i j⟩

/-- Their Galois conjugates: `2 A + (1 − √5) B` (`= 2 (A + (1 − τ) B)`). -/
def icoWc : Matrix (Fin 6) (Fin 3) Zsqrt5 := fun i j => ⟨2 * icoA i j + icoB i j, -icoB i j⟩

/-- The Galois-conjugate rotation of `g`: the conjugate of its scaled matrix, divided by `4`. -/
noncomputable def icoRotConj (g : icosahedralRotationGroup) : Matrix (Fin 3) (Fin 3) ℝ :=
  (1 / 4 : ℝ) • (toM3 g).toMatrix.map zsqrt5ConjToReal

/-- The 6D matrix of `g`: `P_∥ R P_∥ᵀ + P_⊥ R' P_⊥ᵀ`. -/
noncomputable def sixDRepMat (g : icosahedralRotationGroup) : Matrix (Fin 6) (Fin 6) ℝ :=
  icoPar * ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) * icoParᵀ +
    icoPerp * icoRotConj g * icoPerpᵀ

/-- The signed permutation of the six rows read off from a scaled rotation `A`:
entry `(i, j)` is `±1` if `A w_j = ±4 w_i` (rows `w` of `icoW`), else `0`. -/
def signedPermOf (A : M3) : Matrix (Fin 6) (Fin 6) ℤ := fun i j =>
  if A.mulVec (fun k => icoW j k) = (4 : Zsqrt5) • (fun k => icoW i k) then 1
  else if A.mulVec (fun k => icoW j k) = (-4 : Zsqrt5) • (fun k => icoW i k) then -1 else 0

/-- The row index that column `j` of `signedPermOf A` points to. -/
def signedPermIdx (A : M3) (j : Fin 6) : Fin 6 :=
  ((List.finRange 6).find? (fun i => signedPermOf A i j ≠ 0)).getD 0

/-! ## (a) The Galois-conjugate ring map -/

theorem zsqrt5ConjToReal_apply (z : Zsqrt5) :
    zsqrt5ConjToReal z = (z.re : ℝ) - (z.im : ℝ) * Real.sqrt 5 := by
  simp [zsqrt5ConjToReal, sub_eq_add_neg]

theorem zsqrt5ConjToReal_injective : Function.Injective zsqrt5ConjToReal :=
  Zsqrtd.lift_injective _ five_ne_sq

theorem zsqrt5ConjToReal_eq_star (z : Zsqrt5) : zsqrt5ConjToReal z = zsqrt5ToReal (star z) := by
  rw [zsqrt5ConjToReal_apply, zsqrt5ToReal_apply, Zsqrtd.re_star, Zsqrtd.im_star]
  push_cast; ring

theorem zsqrt5ConjToReal_tau : zsqrt5ConjToReal ⟨1, 1⟩ / 2 = 1 - tauR := by
  rw [zsqrt5ConjToReal_apply, tauR]; push_cast; ring

/-! ## (b) Exact identities over `ℤ[√5]` -/

theorem icoW_gram : icoWᵀ * icoW = (⟨20, 4⟩ : Zsqrt5) • (1 : Matrix (Fin 3) (Fin 3) Zsqrt5) := by
  decide +kernel

theorem icoWc_gram : icoWcᵀ * icoWc = (⟨20, -4⟩ : Zsqrt5) • (1 : Matrix (Fin 3) (Fin 3) Zsqrt5) := by
  decide +kernel

theorem icoW_cross : icoWᵀ * icoWc = 0 := by decide +kernel

theorem icoW_complete :
    (⟨5, -1⟩ : Zsqrt5) • (icoW * icoWᵀ) + (⟨5, 1⟩ : Zsqrt5) • (icoWc * icoWcᵀ) =
      (80 : Zsqrt5) • (1 : Matrix (Fin 6) (Fin 6) Zsqrt5) := by decide +kernel

theorem icoWc_eq_star : icoWc = icoW.map star := by decide +kernel

/-! ### Transfer to the real `ico_basis()` -/

theorem sqrt5_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)

theorem sqrt5_lt_five : Real.sqrt 5 < 5 := by
  rw [Real.sqrt_lt' (by norm_num)]; norm_num

theorem nPar_pos : (0 : ℝ) < 20 + 4 * Real.sqrt 5 := by positivity

theorem nPerp_pos : (0 : ℝ) < 20 - 4 * Real.sqrt 5 := by linarith [sqrt5_lt_five]

theorem par_rowsum (i : Fin 6) :
    ∑ k, ((icoA i k : ℝ) + tauR * icoB i k) ^ 2 = (20 + 4 * Real.sqrt 5) / 8 := by
  fin_cases i <;> simp [icoA, icoB, Fin.sum_univ_three, tauR] <;> rw [Real.goldenRatio] <;> ring

theorem perp_rowsum (i : Fin 6) :
    ∑ k, ((icoA i k : ℝ) + (1 - tauR) * icoB i k) ^ 2 = (20 - 4 * Real.sqrt 5) / 8 := by
  fin_cases i <;> simp [icoA, icoB, Fin.sum_univ_three, tauR] <;> nlinarith [sqrt5_sq]

theorem sqrt_norm_aux {n : ℝ} (hn : 0 < n) : Real.sqrt (n / 8) * Real.sqrt 2 = Real.sqrt n / 2 := by
  rw [← Real.sqrt_mul (by positivity)]
  rw [show n / 8 * 2 = (Real.sqrt n / 2) ^ 2 by rw [div_pow, Real.sq_sqrt hn.le]; ring]
  exact Real.sqrt_sq (by positivity)

theorem icoPar_eq : icoPar = (Real.sqrt (20 + 4 * Real.sqrt 5))⁻¹ • icoW.map zsqrt5ToReal := by
  ext i j
  have hs := Real.sqrt_pos.mpr nPar_pos
  simp only [icoPar, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, icoW]
  rw [par_rowsum, div_div, sqrt_norm_aux nPar_pos, zsqrt5ToReal_apply]
  field_simp
  push_cast
  simp only [tauR]
  ring

theorem icoPerp_eq : icoPerp = (Real.sqrt (20 - 4 * Real.sqrt 5))⁻¹ • icoW.map zsqrt5ConjToReal := by
  ext i j
  have hs := Real.sqrt_pos.mpr nPerp_pos
  simp only [icoPerp, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, icoW]
  rw [perp_rowsum, div_div, sqrt_norm_aux nPerp_pos, zsqrt5ConjToReal_apply]
  field_simp
  push_cast
  simp only [tauR]
  ring

theorem icoW_map_conj : icoW.map zsqrt5ConjToReal = icoWc.map zsqrt5ToReal := by
  rw [icoWc_eq_star]; ext i j; simp [zsqrt5ConjToReal_eq_star]

theorem icoPerp_eq' : icoPerp = (Real.sqrt (20 - 4 * Real.sqrt 5))⁻¹ • icoWc.map zsqrt5ToReal := by
  rw [icoPerp_eq, icoW_map_conj]

theorem map_smul_hom {m n : Type*} (f : Zsqrt5 →+* ℝ) (c : Zsqrt5) (M : Matrix m n Zsqrt5) :
    (c • M).map f = f c • M.map f := by
  ext i j; simp

theorem map_one_hom {n : Type*} [DecidableEq n] (f : Zsqrt5 →+* ℝ) :
    (1 : Matrix n n Zsqrt5).map f = 1 := by
  ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem gram_aux {m n : Type*} [Fintype m] (a : ℝ) (M N : Matrix m n Zsqrt5) :
    (a • M.map zsqrt5ToReal)ᵀ * (a • N.map zsqrt5ToReal) =
      (a * a) • (Mᵀ * N).map zsqrt5ToReal := by
  rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.map_mul,
    Matrix.transpose_map]

theorem gram_aux' {m n : Type*} [Fintype n] (a : ℝ) (M : Matrix m n Zsqrt5) :
    (a • M.map zsqrt5ToReal) * (a • M.map zsqrt5ToReal)ᵀ =
      (a * a) • (M * Mᵀ).map zsqrt5ToReal := by
  rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.map_mul,
    Matrix.transpose_map]

theorem inv_sqrt_mul_self {n : ℝ} (hn : 0 < n) : (Real.sqrt n)⁻¹ * (Real.sqrt n)⁻¹ = n⁻¹ := by
  rw [← mul_inv, Real.mul_self_sqrt hn.le]

theorem f_20_4 : zsqrt5ToReal ⟨20, 4⟩ = 20 + 4 * Real.sqrt 5 := by
  rw [zsqrt5ToReal_apply]; push_cast; ring

theorem f_20_m4 : zsqrt5ToReal ⟨20, -4⟩ = 20 - 4 * Real.sqrt 5 := by
  rw [zsqrt5ToReal_apply]; push_cast; ring

theorem icoPar_transpose_mul_self : icoParᵀ * icoPar = 1 := by
  rw [icoPar_eq, gram_aux, icoW_gram, map_smul_hom, map_one_hom, smul_smul, f_20_4,
    inv_sqrt_mul_self nPar_pos, inv_mul_cancel₀ nPar_pos.ne', one_smul]

theorem icoPerp_transpose_mul_self : icoPerpᵀ * icoPerp = 1 := by
  rw [icoPerp_eq', gram_aux, icoWc_gram, map_smul_hom, map_one_hom, smul_smul, f_20_m4,
    inv_sqrt_mul_self nPerp_pos, inv_mul_cancel₀ nPerp_pos.ne', one_smul]

theorem icoPar_transpose_mul_icoPerp : icoParᵀ * icoPerp = 0 := by
  rw [icoPar_eq, icoPerp_eq', Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul,
    ← Matrix.transpose_map, ← Matrix.map_mul, icoW_cross, Matrix.map_zero _ (map_zero _),
    smul_zero, smul_zero]

theorem inv_nPar : (20 + 4 * Real.sqrt 5)⁻¹ = zsqrt5ToReal ⟨5, -1⟩ / 80 := by
  rw [zsqrt5ToReal_apply]
  have h := nPar_pos
  field_simp
  push_cast
  nlinarith [sqrt5_sq]

theorem inv_nPerp : (20 - 4 * Real.sqrt 5)⁻¹ = zsqrt5ToReal ⟨5, 1⟩ / 80 := by
  rw [zsqrt5ToReal_apply]
  have h := nPerp_pos
  field_simp
  push_cast
  nlinarith [sqrt5_sq]

theorem icoPar_mul_transpose_add : icoPar * icoParᵀ + icoPerp * icoPerpᵀ = 1 := by
  rw [icoPar_eq, icoPerp_eq', gram_aux', gram_aux', inv_sqrt_mul_self nPar_pos,
    inv_sqrt_mul_self nPerp_pos, inv_nPar, inv_nPerp]
  ext i j
  have h := congrArg (fun M => zsqrt5ToReal (M i j)) icoW_complete
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul,
    Matrix.map_apply] at h ⊢
  calc zsqrt5ToReal ⟨5, -1⟩ / 80 * zsqrt5ToReal ((icoW * icoWᵀ) i j) +
        zsqrt5ToReal ⟨5, 1⟩ / 80 * zsqrt5ToReal ((icoWc * icoWcᵀ) i j)
      = (zsqrt5ToReal ⟨5, -1⟩ * zsqrt5ToReal ((icoW * icoWᵀ) i j) +
          zsqrt5ToReal ⟨5, 1⟩ * zsqrt5ToReal ((icoWc * icoWcᵀ) i j)) / 80 := by ring
    _ = (1 : Matrix (Fin 6) (Fin 6) ℝ) i j := by
        rw [h]
        by_cases hij : i = j <;> simp [Matrix.one_apply, hij, map_ofNat]

/-! ## (c) The 6D representation -/

theorem toM3_toMatrix_mem (g : icosahedralRotationGroup) :
    (toM3 g).toMatrix ∈ scaledIcosahedralRotations :=
  mem_scaledIcosahedralRotations.mpr ⟨toM3 g, toM3_mem g, rfl⟩

theorem coe_eq_realQuarter_toM3' (g : icosahedralRotationGroup) :
    ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) =
      realQuarter (toM3 g).toMatrix :=
  coe_eq_realQuarter_repM3 g

theorem realQuarter_mul' (A B : Matrix (Fin 3) (Fin 3) Zsqrt5) :
    realQuarter (A * B) = (4 : ℝ) • (realQuarter A * realQuarter B) := by
  rw [realQuarter, realQuarter, realQuarter, Matrix.map_mul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, smul_smul]
  norm_num

theorem realQuarter_smul_four (C : Matrix (Fin 3) (Fin 3) Zsqrt5) :
    realQuarter ((4 : Zsqrt5) • C) = (4 : ℝ) • realQuarter C := by
  rw [realQuarter, realQuarter, map_smul_hom, map_ofNat, smul_smul, smul_smul]
  norm_num

theorem coe_mul_matrix (g h : icosahedralRotationGroup) :
    (((g * h : icosahedralRotationGroup) : specialOrthogonalGroup (Fin 3) ℝ) :
      Matrix (Fin 3) (Fin 3) ℝ) =
    ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *
      ((h : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) := rfl

theorem toM3_mul_toMatrix (g h : icosahedralRotationGroup) :
    (toM3 g).toMatrix * (toM3 h).toMatrix = (4 : Zsqrt5) • (toM3 (g * h)).toMatrix := by
  apply realQuarter_injective
  rw [realQuarter_mul', realQuarter_smul_four, ← coe_eq_realQuarter_toM3',
    ← coe_eq_realQuarter_toM3', ← coe_eq_realQuarter_toM3', coe_mul_matrix]

theorem icoRotConj_mul (g h : icosahedralRotationGroup) :
    icoRotConj (g * h) = icoRotConj g * icoRotConj h := by
  rw [icoRotConj, icoRotConj, icoRotConj, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    ← Matrix.map_mul, toM3_mul_toMatrix, map_smul_hom, map_ofNat, smul_smul]
  norm_num

theorem icoRotConj_orthogonal (g : icosahedralRotationGroup) :
    (icoRotConj g)ᵀ * icoRotConj g = 1 ∧ (icoRotConj g).det = 1 := by
  obtain ⟨h1, h2⟩ := scaledIcosahedralRotations_isScaledRotation _ (toM3_toMatrix_mem g)
  constructor
  · rw [icoRotConj, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      ← Matrix.transpose_map, ← Matrix.map_mul, h1, map_smul_hom, map_one_hom, map_ofNat,
      smul_smul]
    norm_num
  · rw [icoRotConj, Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h2,
      map_ofNat]
    norm_num

theorem PtP_mul {k : Type*} (X : Matrix (Fin 3) k ℝ) : icoParᵀ * (icoPar * X) = X := by
  rw [← Matrix.mul_assoc, icoPar_transpose_mul_self, Matrix.one_mul]

theorem QtQ_mul {k : Type*} (X : Matrix (Fin 3) k ℝ) : icoPerpᵀ * (icoPerp * X) = X := by
  rw [← Matrix.mul_assoc, icoPerp_transpose_mul_self, Matrix.one_mul]

theorem icoPerp_transpose_mul_icoPar : icoPerpᵀ * icoPar = 0 := by
  have h := congrArg Matrix.transpose icoPar_transpose_mul_icoPerp
  rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] at h
  exact h

theorem PtQ_mul {k : Type*} (X : Matrix (Fin 3) k ℝ) : icoParᵀ * (icoPerp * X) = 0 := by
  rw [← Matrix.mul_assoc, icoPar_transpose_mul_icoPerp, Matrix.zero_mul]

theorem QtP_mul {k : Type*} (X : Matrix (Fin 3) k ℝ) : icoPerpᵀ * (icoPar * X) = 0 := by
  rw [← Matrix.mul_assoc, icoPerp_transpose_mul_icoPar, Matrix.zero_mul]

theorem icoRotConj_one : icoRotConj 1 = 1 := by
  have h := icoRotConj_mul 1 1
  rw [mul_one] at h
  obtain ⟨ho, -⟩ := icoRotConj_orthogonal 1
  calc icoRotConj 1 = (icoRotConj 1)ᵀ * icoRotConj 1 * icoRotConj 1 := by
        rw [ho, Matrix.one_mul]
    _ = (icoRotConj 1)ᵀ * icoRotConj 1 := by rw [Matrix.mul_assoc, ← h]
    _ = 1 := ho

theorem sixDRepMat_one : sixDRepMat 1 = 1 := by
  rw [sixDRepMat, icoRotConj_one]
  have h1 : (((1 : icosahedralRotationGroup) : specialOrthogonalGroup (Fin 3) ℝ) :
      Matrix (Fin 3) (Fin 3) ℝ) = 1 := rfl
  rw [h1, Matrix.mul_one, Matrix.mul_one, icoPar_mul_transpose_add]

theorem sixDRepMat_mul (g h : icosahedralRotationGroup) :
    sixDRepMat (g * h) = sixDRepMat g * sixDRepMat h := by
  simp only [sixDRepMat, coe_mul_matrix, icoRotConj_mul, Matrix.add_mul, Matrix.mul_add,
    Matrix.mul_assoc, PtP_mul, QtQ_mul, PtQ_mul, QtP_mul, Matrix.mul_zero, add_zero, zero_add]

noncomputable def sixDRep : icosahedralRotationGroup →* Matrix (Fin 6) (Fin 6) ℝ where
  toFun := sixDRepMat
  map_one' := sixDRepMat_one
  map_mul' := sixDRepMat_mul

theorem sixDRep_apply (g : icosahedralRotationGroup) : sixDRep g = sixDRepMat g := rfl

theorem sixDRep_mul_icoPar (g : icosahedralRotationGroup) :
    sixDRep g * icoPar = icoPar * ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) := by
  rw [sixDRep_apply, sixDRepMat]
  simp only [Matrix.add_mul, Matrix.mul_assoc, icoPar_transpose_mul_self,
    icoPerp_transpose_mul_icoPar, Matrix.mul_one, Matrix.mul_zero, add_zero]

theorem sixDRep_mul_icoPerp (g : icosahedralRotationGroup) :
    sixDRep g * icoPerp = icoPerp * icoRotConj g := by
  rw [sixDRep_apply, sixDRepMat]
  simp only [Matrix.add_mul, Matrix.mul_assoc, icoPerp_transpose_mul_self,
    icoPar_transpose_mul_icoPerp, Matrix.mul_one, Matrix.mul_zero, zero_add]

theorem sixDRep_commute_parProj (g : icosahedralRotationGroup) :
    sixDRep g * (icoPar * icoParᵀ) = (icoPar * icoParᵀ) * sixDRep g := by
  rw [← Matrix.mul_assoc, sixDRep_mul_icoPar, sixDRep_apply, sixDRepMat]
  simp only [Matrix.mul_add, Matrix.mul_assoc, PtP_mul, PtQ_mul, Matrix.mul_zero, add_zero]

theorem sixDRep_commute_perpProj (g : icosahedralRotationGroup) :
    sixDRep g * (icoPerp * icoPerpᵀ) = (icoPerp * icoPerpᵀ) * sixDRep g := by
  rw [← Matrix.mul_assoc, sixDRep_mul_icoPerp, sixDRep_apply, sixDRepMat]
  simp only [Matrix.mul_add, Matrix.mul_assoc, QtP_mul, QtQ_mul, Matrix.mul_zero, zero_add]

theorem sixDRep_injective : Function.Injective sixDRep := by
  intro g h hgh
  have e := congrArg (fun M => icoParᵀ * (M * icoPar)) hgh
  simp only [sixDRep_mul_icoPar, PtP_mul] at e
  exact Subtype.ext (Subtype.ext e)

/-! ### The signed-permutation table -/

/-- The table row for a scaled rotation `A`. -/
def SPRow (A : M3) : Prop :=
  ((⟨20, -4⟩ : Zsqrt5) • (icoW * A.toMatrix * icoWᵀ) +
      (⟨20, 4⟩ : Zsqrt5) • (icoWc * A.toMatrix.map star * icoWcᵀ) =
    (1280 : Zsqrt5) • (signedPermOf A).map (Int.cast)) ∧
  (∀ j k : Fin 6, signedPermIdx A j = signedPermIdx A k → j = k) ∧
  (∀ j i : Fin 6, signedPermOf A i j = 0 ∨ i = signedPermIdx A j) ∧
  (∀ j : Fin 6, signedPermOf A (signedPermIdx A j) j = 1 ∨
    signedPermOf A (signedPermIdx A j) j = -1)

instance (A : M3) : Decidable (SPRow A) := by unfold SPRow; infer_instance

theorem spRow0 : ∀ A ∈ scaledRotationChunk0, SPRow A := by decide +kernel
theorem spRow1 : ∀ A ∈ scaledRotationChunk1, SPRow A := by decide +kernel
theorem spRow2 : ∀ A ∈ scaledRotationChunk2, SPRow A := by decide +kernel
theorem spRow3 : ∀ A ∈ scaledRotationChunk3, SPRow A := by decide +kernel
theorem spRow4 : ∀ A ∈ scaledRotationChunk4, SPRow A := by decide +kernel
theorem spRow5 : ∀ A ∈ scaledRotationChunk5, SPRow A := by decide +kernel

theorem sp_row : ∀ A ∈ scaledRotationList, SPRow A := by
  intro A hA
  simp only [scaledRotationList, List.mem_append] at hA
  rcases hA with ((((h | h) | h) | h) | h) | h
  · exact spRow0 A h
  · exact spRow1 A h
  · exact spRow2 A h
  · exact spRow3 A h
  · exact spRow4 A h
  · exact spRow5 A h

theorem sandwich_aux (a b : ℝ) (M : Matrix (Fin 6) (Fin 3) Zsqrt5) (N : Matrix (Fin 3) (Fin 3) Zsqrt5) :
    (a • M.map zsqrt5ToReal) * (b • N.map zsqrt5ToReal) * (a • M.map zsqrt5ToReal)ᵀ =
      (a * a * b) • (M * N * Mᵀ).map zsqrt5ToReal := by
  simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.map_mul,
    Matrix.transpose_map]
  congr 1; ring

theorem icoRotConj_eq (g : icosahedralRotationGroup) :
    icoRotConj g = (1 / 4 : ℝ) • ((toM3 g).toMatrix.map star).map zsqrt5ToReal := by
  rw [icoRotConj]; congr 1; ext i j; simp [zsqrt5ConjToReal_eq_star]

theorem inv_nPar' : (20 + 4 * Real.sqrt 5)⁻¹ * (1 / 4) = zsqrt5ToReal ⟨20, -4⟩ / 1280 := by
  rw [f_20_m4]
  have h := nPar_pos
  field_simp
  nlinarith [sqrt5_sq]

theorem inv_nPerp' : (20 - 4 * Real.sqrt 5)⁻¹ * (1 / 4) = zsqrt5ToReal ⟨20, 4⟩ / 1280 := by
  rw [f_20_4]
  have h := nPerp_pos
  field_simp
  nlinarith [sqrt5_sq]

theorem sixDRepMat_eq (g : icosahedralRotationGroup) :
    sixDRepMat g = (signedPermOf (toM3 g)).map (Int.cast : ℤ → ℝ) := by
  obtain ⟨h, -⟩ := sp_row _ (toM3_mem g)
  rw [sixDRepMat, coe_eq_realQuarter_toM3', realQuarter, icoRotConj_eq, icoPar_eq, icoPerp_eq',
    sandwich_aux, sandwich_aux, inv_sqrt_mul_self nPar_pos, inv_sqrt_mul_self nPerp_pos,
    inv_nPar', inv_nPerp']
  ext i j
  have e := congrArg (fun M => zsqrt5ToReal (M i j)) h
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul,
    Matrix.map_apply, map_intCast, map_ofNat] at e ⊢
  calc zsqrt5ToReal ⟨20, -4⟩ / 1280 * zsqrt5ToReal ((icoW * (toM3 g).toMatrix * icoWᵀ) i j) +
        zsqrt5ToReal ⟨20, 4⟩ / 1280 *
          zsqrt5ToReal ((icoWc * (toM3 g).toMatrix.map star * icoWcᵀ) i j)
      = (zsqrt5ToReal ⟨20, -4⟩ * zsqrt5ToReal ((icoW * (toM3 g).toMatrix * icoWᵀ) i j) +
          zsqrt5ToReal ⟨20, 4⟩ *
            zsqrt5ToReal ((icoWc * (toM3 g).toMatrix.map star * icoWcᵀ) i j)) / 1280 := by ring
    _ = _ := by rw [e]; ring

theorem sixDRep_signedPerm (g : icosahedralRotationGroup) :
    ∃ σ : Perm (Fin 6), ∃ s : Fin 6 → ℤ, (∀ j, s j = 1 ∨ s j = -1) ∧
      sixDRep g = Matrix.of fun i j => if i = σ j then (s j : ℝ) else 0 := by
  obtain ⟨-, hinj, hform, hs⟩ := sp_row _ (toM3_mem g)
  have hbij : Function.Bijective (signedPermIdx (toM3 g)) :=
    Finite.injective_iff_bijective.mp (fun j k h => hinj j k h)
  refine ⟨Equiv.ofBijective _ hbij, fun j => signedPermOf (toM3 g) (signedPermIdx (toM3 g) j) j,
    hs, ?_⟩
  rw [sixDRep_apply, sixDRepMat_eq]
  ext i j
  simp only [Matrix.map_apply, Matrix.of_apply, Equiv.ofBijective_apply]
  by_cases hij : i = signedPermIdx (toM3 g) j
  · subst hij; simp
  · simp [hij, (hform j i).resolve_right hij]

#print axioms zsqrt5ConjToReal_apply
#print axioms zsqrt5ConjToReal_injective
#print axioms zsqrt5ConjToReal_eq_star
#print axioms zsqrt5ConjToReal_tau
#print axioms icoW_gram
#print axioms icoWc_gram
#print axioms icoW_cross
#print axioms icoW_complete
#print axioms icoWc_eq_star
#print axioms icoPar_eq
#print axioms icoPerp_eq
#print axioms icoPar_transpose_mul_self
#print axioms icoPerp_transpose_mul_self
#print axioms icoPar_transpose_mul_icoPerp
#print axioms icoPar_mul_transpose_add
#print axioms icoRotConj_orthogonal
#print axioms icoRotConj_mul
#print axioms sixDRepMat_one
#print axioms sixDRepMat_mul
#print axioms sixDRep
#print axioms sixDRep_signedPerm
#print axioms sixDRep_injective
#print axioms sixDRep_mul_icoPar
#print axioms sixDRep_mul_icoPerp
#print axioms sixDRep_commute_parProj
#print axioms sixDRep_commute_perpProj
