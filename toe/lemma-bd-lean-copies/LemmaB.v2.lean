import Mathlib

/-!
# Chair44 Lemma B: mask and denominator (scratch)

Source: `/home/box/shared/theory-of-everything/chair44-antidiagonal-mechanism-2026-11-07.md`
sha256 `08e4ceed4c1c9b1a4cb9e15b3af5484550636dfe377bb124409761f932cb7e64`, §6 Lemma B
and §1 grid/mask/den definitions. QIS scoping
`/home/box/shared/qis-eth/lean/lemmas-b-d-statement-dependencies-scoping-2026-11-09.md`
sha256 `c7b46dc3ecd2543b84354315bed5ba93b232bb96c37192bd06fbde40be6e4e93`.

Displayed statement: For integer L≥2 and 0≤jx,jy<L, not both zero, at jz=0:
L ∣ jx+jy ↔ qx+qy=1. On that mask jy=L−jx and gcd(jx,jy,L)=gcd(jx,L); hence
den=L iff gcd(jx,L)=1. For L=2^m, m≥1, this is exactly odd jx (L/2 points).
The L/2 count is also given as an explicit bijection
`maskPointOfIdx m : range (2^(m-1)) → maskDenSet (2^m)` (grid pairs on the mask
with den=L; jz not encoded), with `#(maskDenSet (2^m)) = 2^m / 2` derived from
that bijection (not via the odd-count lemma).

§1: q=(jx/L,jy/L,0); mask `(jx+jy)%L==0` excluding (0,0); `den=L/gcd(jx,jy,L)`.

Fidelity:
* `den` is defined as `L / Nat.gcd (Nat.gcd jx jy) L` exactly as §1.
* jz=0 / qz=0 carry no content and are **not encoded**; theorems are stated for
  `jx, jy : ℕ` alone (and a separate rational qx+qy form).
* No Bragg weight, torus wrapping, or physical q-periodicity is asserted.
* Scratch only: not in any Lake target, not peer reviewed. Licenses nothing about
  ScaleLiftToRAM, PrimToRAM, ETH, R2/R4/R5, fade, CH-V-020, or Theorem F.
-/

namespace LeanLab.Scratch.LemmaB

open Nat Finset

/-- §1 denominator: `den = L / gcd(jx, jy, L)`. -/
def den (L jx jy : ℕ) : ℕ :=
  L / Nat.gcd (Nat.gcd jx jy) L

/-- (B1a) With `0 ≤ jx,jy < L` and not both zero, `L ∣ jx+jy` iff `jx+jy = L`. -/
theorem dvd_add_iff_eq_L {L jx jy : ℕ} (hL : 2 ≤ L)
    (hjx : jx < L) (hjy : jy < L) (hne : ¬ (jx = 0 ∧ jy = 0)) :
    L ∣ jx + jy ↔ jx + jy = L := by
  constructor
  · rintro ⟨k, hk⟩
    -- hk : jx + jy = L * k, with 0 < jx+jy < 2L, so k = 1
    have hsum_pos : 0 < jx + jy := by omega
    have hkpos : 0 < k := Nat.pos_of_mul_pos_left (by rwa [← hk] : 0 < L * k)
    have hklt : k < 2 := by
      have hsum_lt : jx + jy < 2 * L := by omega
      have : L * k < L * 2 := by
        rwa [hk, mul_comm 2 L] at hsum_lt
      exact (Nat.mul_lt_mul_left (by omega : 0 < L)).mp this
    have hk1 : k = 1 := by omega
    rw [hk, hk1, mul_one]
  · intro h
    exact ⟨1, by omega⟩

/-- (B1b) Rational form: `L ∣ jx+jy` iff `(jx:ℚ)/L + (jy:ℚ)/L = 1`.
(`jz=0`/`qz=0` not encoded.) -/
theorem dvd_add_iff_qx_add_qy_eq_one {L jx jy : ℕ} (hL : 2 ≤ L)
    (hjx : jx < L) (hjy : jy < L) (hne : ¬ (jx = 0 ∧ jy = 0)) :
    L ∣ jx + jy ↔ ((jx : ℚ) / (L : ℚ) + (jy : ℚ) / (L : ℚ) = 1) := by
  have hLne : (L : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt (Nat.zero_lt_of_lt hL))
  rw [dvd_add_iff_eq_L hL hjx hjy hne]
  constructor
  · intro h
    field_simp
    exact_mod_cast h
  · intro h
    have := congrArg (fun z : ℚ => z * (L : ℚ)) h
    field_simp [hLne] at this
    exact_mod_cast this

/-- On the mask `jx + jy = L`, one has `jy = L - jx`. -/
theorem mask_jy_eq {L jx jy : ℕ} (hmask : jx + jy = L) : jy = L - jx := by
  omega

/-- (B2) On the mask, `gcd(jx, jy, L) = gcd(jx, L)`. -/
theorem gcd_mask {L jx jy : ℕ} (hjx : jx < L) (hmask : jx + jy = L) :
    Nat.gcd (Nat.gcd jx jy) L = Nat.gcd jx L := by
  have hjy : jy = L - jx := mask_jy_eq hmask
  have hjx_le : jx ≤ L := Nat.le_of_lt hjx
  subst hjy
  have h1 : Nat.gcd jx (L - jx) = Nat.gcd L jx := by
    rw [Nat.gcd_comm jx (L - jx), Nat.gcd_sub_self_left hjx_le]
  rw [h1, Nat.gcd_comm L jx, Nat.gcd_assoc, Nat.gcd_self, Nat.gcd_comm]

/-- (B3) On the mask, `den = L` iff `Nat.Coprime jx L`. -/
theorem den_eq_L_iff_coprime {L jx jy : ℕ} (hL : 2 ≤ L) (hjx : jx < L)
    (hmask : jx + jy = L) :
    den L jx jy = L ↔ Nat.Coprime jx L := by
  unfold den
  rw [gcd_mask hjx hmask]
  constructor
  · intro h
    have hg : Nat.gcd jx L ∣ L := Nat.gcd_dvd_right _ _
    have hmul := Nat.div_mul_cancel hg
    -- (L / d) * d = L; with L/d = L get L*d = L ⇒ d = 1
    rw [h] at hmul
    have : L * Nat.gcd jx L = L * 1 := by omega
    exact Nat.mul_left_cancel (Nat.zero_lt_of_lt hL) this
  · intro h
    change Nat.gcd jx L = 1 at h
    simp [h]

/-- (B4) For `L = 2^m` with `m ≥ 1`, on the mask: `den = L` iff `Odd jx`. -/
theorem den_eq_L_iff_odd_pow_two {m jx jy : ℕ} (hm : 1 ≤ m)
    (hjx : jx < 2 ^ m) (hmask : jx + jy = 2 ^ m) :
    den (2 ^ m) jx jy = 2 ^ m ↔ Odd jx := by
  have hL : 2 ≤ 2 ^ m := by
    calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  rw [den_eq_L_iff_coprime hL hjx hmask]
  have hmpos : 0 < m := hm
  rw [Nat.coprime_comm, Nat.coprime_pow_left_iff hmpos, Nat.coprime_comm,
      Nat.coprime_two_right]

/-- Helper: `2^(m-1) = (2^m)/2` for `m ≥ 1`. -/
theorem pow_two_div_two {m : ℕ} (hm : 1 ≤ m) :
    2 ^ (m - 1) = 2 ^ m / 2 := by
  have h : 2 ^ m = 2 * 2 ^ (m - 1) := by
    have hm' : 2 ^ m = 2 ^ ((m - 1) + 1) := by congr 1; omega
    rw [hm', pow_succ, mul_comm]
  rw [h, Nat.mul_div_right _ (by norm_num : 0 < 2)]

/-- Bound used in the odd-count bijection. -/
theorem two_mul_pred_add_one {m : ℕ} (hm : 1 ≤ m) :
    2 * (2 ^ (m - 1) - 1) + 1 = 2 ^ m - 1 := by
  have hge : 1 ≤ 2 ^ (m - 1) := Nat.one_le_pow _ _ (by norm_num)
  have h : 2 ^ m = 2 * 2 ^ (m - 1) := by
    have hm' : 2 ^ m = 2 ^ ((m - 1) + 1) := by congr 1; omega
    rw [hm', pow_succ, mul_comm]
  -- 2*(a-1)+1 = 2a-1 when a≥1; here a = 2^(m-1)
  have : 2 * (2 ^ (m - 1) - 1) + 1 = 2 * 2 ^ (m - 1) - 1 := by
    rw [Nat.mul_sub]; omega
  rw [this, h]

/-- Odd numbers in `[1, 2^m - 1]` number exactly `2^(m-1)`. -/
theorem card_odd_in_Icc_pow_two {m : ℕ} (hm : 1 ≤ m) :
    #{n ∈ Icc 1 (2 ^ m - 1) | Odd n} = 2 ^ (m - 1) := by
  have himage :
      ((range (2 ^ (m - 1))).image fun k => 2 * k + 1) =
        {n ∈ Icc 1 (2 ^ m - 1) | Odd n} := by
    ext n
    simp only [mem_image, mem_range, mem_filter, mem_Icc]
    constructor
    · rintro ⟨k, hk, rfl⟩
      refine ⟨⟨by omega, ?_⟩, odd_two_mul_add_one k⟩
      have : 2 * k + 1 ≤ 2 * (2 ^ (m - 1) - 1) + 1 := by omega
      have := two_mul_pred_add_one hm
      omega
    · rintro ⟨⟨_hn1, hn2⟩, hod⟩
      obtain ⟨k, rfl⟩ := hod
      refine ⟨k, ?_, rfl⟩
      -- 2k+1 ≤ 2^m-1 ⇒ k < 2^(m-1)
      have hlt : 2 * k < 2 ^ m := by omega
      have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by
        have hm' : 2 ^ m = 2 ^ ((m - 1) + 1) := by congr 1; omega
        rw [hm', pow_succ, mul_comm]
      have : 2 * k < 2 * 2 ^ (m - 1) := by rwa [hpow] at hlt
      exact (Nat.mul_lt_mul_left (by norm_num : 0 < 2)).mp this
  have hcard :
      #((range (2 ^ (m - 1))).image fun k => 2 * k + 1) = 2 ^ (m - 1) := by
    rw [Finset.card_image_of_injective _ (fun a b h => by omega)]
    simp [card_range]
  rw [← himage, hcard]

/-- (B5) On the mask for `L = 2^m`, the set of `jx ∈ [1, L-1]` with `den = L`
has cardinality `L/2` (exactly the odd `jx`). -/
theorem card_den_eq_L_on_mask_pow_two {m : ℕ} (hm : 1 ≤ m) :
    #{jx ∈ Icc 1 (2 ^ m - 1) | den (2 ^ m) jx (2 ^ m - jx) = 2 ^ m} =
      2 ^ m / 2 := by
  have heq :
      {jx ∈ Icc 1 (2 ^ m - 1) | den (2 ^ m) jx (2 ^ m - jx) = 2 ^ m} =
        {jx ∈ Icc 1 (2 ^ m - 1) | Odd jx} := by
    ext jx
    simp only [mem_filter, mem_Icc]
    constructor
    · rintro ⟨⟨hj1, hj2⟩, hden⟩
      refine ⟨⟨hj1, hj2⟩, ?_⟩
      have hjx : jx < 2 ^ m := by omega
      have hmask : jx + (2 ^ m - jx) = 2 ^ m := by omega
      exact (den_eq_L_iff_odd_pow_two hm hjx hmask).mp hden
    · rintro ⟨⟨hj1, hj2⟩, hod⟩
      refine ⟨⟨hj1, hj2⟩, ?_⟩
      have hjx : jx < 2 ^ m := by omega
      have hmask : jx + (2 ^ m - jx) = 2 ^ m := by omega
      exact (den_eq_L_iff_odd_pow_two hm hjx hmask).mpr hod
  rw [heq, card_odd_in_Icc_pow_two hm, pow_two_div_two hm]


/-- Mask points in the L×L grid with den = L (jz not encoded). -/
def maskDenSet (L : ℕ) : Finset (ℕ × ℕ) :=
  (range L ×ˢ range L).filter fun p =>
    ¬ (p.1 = 0 ∧ p.2 = 0) ∧ L ∣ p.1 + p.2 ∧ den L p.1 p.2 = L

/-- Explicit indexing of den=L mask points for `L = 2^m`: odd `jx = 2k+1`. -/
def maskPointOfIdx (m k : ℕ) : ℕ × ℕ :=
  (2 * k + 1, 2 ^ m - (2 * k + 1))

/-- For `m ≥ 1` and `k < 2^(m-1)`, the index lands in `maskDenSet (2^m)`. -/
theorem maskPointOfIdx_mem {m k : ℕ} (hm : 1 ≤ m) (hk : k < 2 ^ (m - 1)) :
    maskPointOfIdx m k ∈ maskDenSet (2 ^ m) := by
  unfold maskPointOfIdx maskDenSet
  simp only [mem_filter, mem_product, mem_range]
  set jx := 2 * k + 1
  set jy := 2 ^ m - (2 * k + 1)
  have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by
    have hm' : 2 ^ m = 2 ^ ((m - 1) + 1) := by congr 1; omega
    rw [hm', pow_succ, mul_comm]
  have hjx_pos : 0 < jx := by omega
  have hjx_lt : jx < 2 ^ m := by
    have : 2 * k + 1 ≤ 2 * (2 ^ (m - 1) - 1) + 1 := by omega
    have := two_mul_pred_add_one hm
    omega
  have hjy_lt : jy < 2 ^ m := by
    have : 1 ≤ jx := by omega
    omega
  have hmask : jx + jy = 2 ^ m := by omega
  have hL : 2 ≤ 2 ^ m := by
    calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  refine ⟨⟨hjx_lt, hjy_lt⟩, ?_, ?_, ?_⟩
  · intro h; exact absurd h.1 (ne_of_gt hjx_pos)
  · exact ⟨1, by omega⟩
  · exact (den_eq_L_iff_odd_pow_two hm hjx_lt hmask).mpr (odd_two_mul_add_one k)

/-- `maskPointOfIdx m` is injective on `range (2^(m-1))`. -/
theorem maskPointOfIdx_injective_on {m : ℕ} :
    Set.InjOn (maskPointOfIdx m) ↑(range (2 ^ (m - 1))) := by
  intro a ha b hb h
  simp only [maskPointOfIdx, Prod.mk.injEq] at h
  omega

/-- Every point of `maskDenSet (2^m)` is `maskPointOfIdx m k` for some `k < 2^(m-1)`. -/
theorem maskPointOfIdx_surjective_on {m : ℕ} (hm : 1 ≤ m) :
    Set.SurjOn (maskPointOfIdx m) ↑(range (2 ^ (m - 1))) ↑(maskDenSet (2 ^ m)) := by
  intro p hp
  unfold maskDenSet at hp
  simp only [mem_coe, mem_filter, mem_product, mem_range] at hp
  obtain ⟨⟨hjx, hjy⟩, hne, hdvd, hden⟩ := hp
  have hL : 2 ≤ 2 ^ m := by
    calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hmask : p.1 + p.2 = 2 ^ m := (dvd_add_iff_eq_L hL hjx hjy hne).mp hdvd
  have hjy_eq : p.2 = 2 ^ m - p.1 := mask_jy_eq hmask
  have hod : Odd p.1 := (den_eq_L_iff_odd_pow_two hm hjx hmask).mp hden
  obtain ⟨k, hk⟩ := hod
  refine ⟨k, ?_, ?_⟩
  · -- k < 2^(m-1)
    simp only [mem_coe, mem_range]
    have hlt : 2 * k < 2 ^ m := by omega
    have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by
      have hm' : 2 ^ m = 2 ^ ((m - 1) + 1) := by congr 1; omega
      rw [hm', pow_succ, mul_comm]
    have : 2 * k < 2 * 2 ^ (m - 1) := by rwa [hpow] at hlt
    exact (Nat.mul_lt_mul_left (by norm_num : 0 < 2)).mp this
  · -- maskPointOfIdx m k = p
    simp only [maskPointOfIdx]
    exact Prod.ext hk.symm (by rw [← hk]; exact hjy_eq.symm)

/-- Explicit bijection: indices `k ∈ range (2^(m-1))` ↔ mask points with `den = L`. -/
theorem maskDenSet_bijOn {m : ℕ} (hm : 1 ≤ m) :
    Set.BijOn (maskPointOfIdx m) ↑(range (2 ^ (m - 1))) ↑(maskDenSet (2 ^ m)) :=
  Set.BijOn.mk
    (fun k hk => by
      simp only [mem_coe, mem_range] at hk
      exact maskPointOfIdx_mem hm hk)
    maskPointOfIdx_injective_on
    (maskPointOfIdx_surjective_on hm)

/-- Cardinality `#(maskDenSet (2^m)) = 2^m / 2`, from the explicit bijection
(not via `card_odd_in_Icc_pow_two`). -/
theorem card_maskDenSet_pow_two {m : ℕ} (hm : 1 ≤ m) :
    #(maskDenSet (2 ^ m)) = 2 ^ m / 2 := by
  have hbij := maskDenSet_bijOn hm
  have hcard := Set.BijOn.finsetCard_eq (maskPointOfIdx m) hbij
  -- #range (2^(m-1)) = #(maskDenSet (2^m))
  simp only [card_range] at hcard
  exact hcard.symm.trans (pow_two_div_two hm)

/-- Combined Lemma B package for `L = 2^m`. -/
theorem lemma_B {m : ℕ} (hm : 1 ≤ m) (jx jy : ℕ)
    (hjx : jx < 2 ^ m) (hjy : jy < 2 ^ m) (hne : ¬ (jx = 0 ∧ jy = 0)) :
    (2 ^ m ∣ jx + jy ↔ jx + jy = 2 ^ m) ∧
    (2 ^ m ∣ jx + jy ↔
      ((jx : ℚ) / ((2 ^ m : ℕ) : ℚ) + (jy : ℚ) / ((2 ^ m : ℕ) : ℚ) = 1)) ∧
    (jx + jy = 2 ^ m → jy = 2 ^ m - jx) ∧
    (jx + jy = 2 ^ m → Nat.gcd (Nat.gcd jx jy) (2 ^ m) = Nat.gcd jx (2 ^ m)) ∧
    (jx + jy = 2 ^ m → (den (2 ^ m) jx jy = 2 ^ m ↔ Nat.Coprime jx (2 ^ m))) ∧
    (jx + jy = 2 ^ m → (den (2 ^ m) jx jy = 2 ^ m ↔ Odd jx)) ∧
    #{k ∈ Icc 1 (2 ^ m - 1) | den (2 ^ m) k (2 ^ m - k) = 2 ^ m} = 2 ^ m / 2 := by
  have hL : 2 ≤ 2 ^ m := by
    calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  exact ⟨dvd_add_iff_eq_L hL hjx hjy hne,
    dvd_add_iff_qx_add_qy_eq_one hL hjx hjy hne,
    fun h => mask_jy_eq h, fun h => gcd_mask hjx h,
    fun h => den_eq_L_iff_coprime hL hjx h,
    fun h => den_eq_L_iff_odd_pow_two hm hjx h,
    card_den_eq_L_on_mask_pow_two hm⟩

#print axioms dvd_add_iff_eq_L
#print axioms dvd_add_iff_qx_add_qy_eq_one
#print axioms mask_jy_eq
#print axioms gcd_mask
#print axioms den_eq_L_iff_coprime
#print axioms den_eq_L_iff_odd_pow_two
#print axioms pow_two_div_two
#print axioms two_mul_pred_add_one
#print axioms card_odd_in_Icc_pow_two
#print axioms card_den_eq_L_on_mask_pow_two
#print axioms maskPointOfIdx_mem
#print axioms maskPointOfIdx_injective_on
#print axioms maskPointOfIdx_surjective_on
#print axioms maskDenSet_bijOn
#print axioms card_maskDenSet_pow_two
#print axioms lemma_B

end LeanLab.Scratch.LemmaB
