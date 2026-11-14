/-
Scratch file, dated 2026-11-10. Not a Lake target. Not peer reviewed.

IcosianQ8FrameLift: the cube stabilisers of the official I lift to quaternion groups Q8 in the
icosian group, the cover 2I → I does not split, and the π-preimages of the classes of I (T1–T3).
Statement text and definitions were frozen before proving.

Imports `BinaryIcosahedralIcosians_2026-11-10` (src 9c9c6451…) unchanged. The body of
`BinaryIcosahedralOrders_2026-11-10` (src 9c5b4f84…) is copied verbatim, with one theorem renamed
(`orderOf_eq_two_iff` ↦ `orderOf_eq_two_iff_negOneBI`), because Mathlib's
`Mathlib.GroupTheory.Exponent` (needed for `QuaternionGroup` / `IsKleinFour`) declares the same root name.

Method: finite checks over ℤ[√5] and `Perm (Fin 5)` by `decide +kernel` (split by chunk), then
transfer to the groups.
-/
import «BinaryIcosahedralIcosians_2026-11-10»
import Mathlib.GroupTheory.SpecificGroups.Quaternion
import Mathlib.GroupTheory.SpecificGroups.KleinFour

open Equiv Matrix

/-! ## Verbatim body of `BinaryIcosahedralOrders_2026-11-10` (one theorem renamed, see header) -/

namespace Q4

/-- Divide every coordinate by `4` (integer division on both `ℤ[√5]` components). -/
def divFour (p : Q4) : Q4 :=
  ⟨⟨p.a.re / 4, p.a.im / 4⟩, ⟨p.b.re / 4, p.b.im / 4⟩, ⟨p.c.re / 4, p.c.im / 4⟩,
    ⟨p.d.re / 4, p.d.im / 4⟩⟩

/-- Product of scaled icosians, rescaled: `(4x)(4y) / 4 = 4(xy)`. -/
def mulN (p q : Q4) : Q4 := (p.mul q).divFour

/-- Rescaled powers, starting from `one4`. -/
def powN (p : Q4) : ℕ → Q4
  | 0 => one4
  | n + 1 => (p.powN n).mulN p

end Q4

/-- The least `n ∈ {1, …, 10}` with `p^n = 1` (rescaled), or `0` if none. -/
def q4Order (p : Q4) : ℕ :=
  ((List.range 10).map (· + 1) |>.find? (fun n => p.powN n = one4)).getD 0

/-- The least `n ∈ {1, …, 10}` with `p^n = ±1` (rescaled), or `0` if none. -/
def q4RotOrder (p : Q4) : ℕ :=
  ((List.range 10).map (· + 1) |>.find? (fun n => p.powN n = one4 ∨ p.powN n = negOne4)).getD 0

/-- The first listed icosian with the same real coordinate as `p`. -/
def classRep (p : Q4) : Q4 := (icosianList.find? (fun q => q.a = p.a)).getD one4

/-- Conjugating witnesses, entries 0–19 (aligned with `icosianChunk0`). -/
def icosianWitnessChunk0 : List Q4 :=
  [ ⟨⟨4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩
  , ⟨⟨4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩
  , ⟨⟨4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩
  , ⟨⟨-2, 0⟩, ⟨1, 1⟩, ⟨-1, 1⟩, ⟨0, 0⟩⟩
  , ⟨⟨-2, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩⟩
  , ⟨⟨-2, 0⟩, ⟨-2, 0⟩, ⟨-2, 0⟩, ⟨2, 0⟩⟩
  , ⟨⟨-2, 0⟩, ⟨-1, -1⟩, ⟨1, -1⟩, ⟨0, 0⟩⟩
  , ⟨⟨-1, -1⟩, ⟨1, -1⟩, ⟨-2, 0⟩, ⟨0, 0⟩⟩
  , ⟨⟨-2, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩⟩
  , ⟨⟨-1, 1⟩, ⟨-2, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩⟩
  , ⟨⟨-2, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, -1⟩⟩
  , ⟨⟨-1, -1⟩, ⟨-1, 1⟩, ⟨2, 0⟩, ⟨0, 0⟩⟩
  , ⟨⟨-1, 1⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨-1, -1⟩⟩
  , ⟨⟨-2, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩, ⟨0, 0⟩⟩
  , ⟨⟨-1, -1⟩, ⟨-2, 0⟩, ⟨0, 0⟩, ⟨1, -1⟩⟩
  , ⟨⟨-2, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩⟩
  , ⟨⟨-1, 1⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨1, 1⟩⟩
  , ⟨⟨-2, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩⟩
  , ⟨⟨-2, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, 1⟩⟩
  , ⟨⟨-2, 0⟩, ⟨2, 0⟩, ⟨-2, 0⟩, ⟨-2, 0⟩⟩ ]

/-- Conjugating witnesses, entries 20–39 (aligned with `icosianChunk1`). -/
def icosianWitnessChunk1 : List Q4 :=
  [ ⟨⟨-2, 0⟩, ⟨-2, 0⟩, ⟨2, 0⟩, ⟨-2, 0⟩⟩
  , ⟨⟨0, 0⟩, ⟨-2, 0⟩, ⟨1, -1⟩, ⟨1, 1⟩⟩
  , ⟨⟨4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩
  , ⟨⟨-2, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩, ⟨0, 0⟩⟩
  , ⟨⟨-2, 0⟩, ⟨-2, 0⟩, ⟨-2, 0⟩, ⟨-2, 0⟩⟩
  , ⟨⟨-2, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩⟩
  , ⟨⟨-2, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, 1⟩⟩
  , ⟨⟨-2, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩⟩
  , ⟨⟨-2, 0⟩, ⟨-2, 0⟩, ⟨2, 0⟩, ⟨-2, 0⟩⟩
  , ⟨⟨-2, 0⟩, ⟨-2, 0⟩, ⟨-2, 0⟩, ⟨2, 0⟩⟩
  , ⟨⟨-2, 0⟩, ⟨-1, -1⟩, ⟨1, -1⟩, ⟨0, 0⟩⟩
  , ⟨⟨-2, 0⟩, ⟨-2, 0⟩, ⟨2, 0⟩, ⟨2, 0⟩⟩
  , ⟨⟨-2, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩⟩
  , ⟨⟨0, 0⟩, ⟨-2, 0⟩, ⟨-1, 1⟩, ⟨-1, -1⟩⟩
  , ⟨⟨4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩
  , ⟨⟨-2, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩⟩
  , ⟨⟨-2, 0⟩, ⟨-1, -1⟩, ⟨1, -1⟩, ⟨0, 0⟩⟩
  , ⟨⟨-2, 0⟩, ⟨-2, 0⟩, ⟨-2, 0⟩, ⟨2, 0⟩⟩
  , ⟨⟨-2, 0⟩, ⟨-2, 0⟩, ⟨-2, 0⟩, ⟨-2, 0⟩⟩
  , ⟨⟨-2, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩⟩ ]

/-- Conjugating witnesses, entries 40–59 (aligned with `icosianChunk2`). -/
def icosianWitnessChunk2 : List Q4 :=
  [ ⟨⟨-2, 0⟩, ⟨-2, 0⟩, ⟨2, 0⟩, ⟨2, 0⟩⟩
  , ⟨⟨-2, 0⟩, ⟨1, 1⟩, ⟨1, -1⟩, ⟨0, 0⟩⟩
  , ⟨⟨-2, 0⟩, ⟨-2, 0⟩, ⟨2, 0⟩, ⟨-2, 0⟩⟩
  , ⟨⟨-2, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩⟩
  , ⟨⟨-2, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, -1⟩⟩
  , ⟨⟨0, 0⟩, ⟨-2, 0⟩, ⟨-1, 1⟩, ⟨-1, -1⟩⟩
  , ⟨⟨4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩
  , ⟨⟨-1, -1⟩, ⟨1, -1⟩, ⟨2, 0⟩, ⟨0, 0⟩⟩
  , ⟨⟨-1, -1⟩, ⟨-1, 1⟩, ⟨-2, 0⟩, ⟨0, 0⟩⟩
  , ⟨⟨-1, -1⟩, ⟨-1, 1⟩, ⟨2, 0⟩, ⟨0, 0⟩⟩
  , ⟨⟨-1, -1⟩, ⟨1, -1⟩, ⟨-2, 0⟩, ⟨0, 0⟩⟩
  , ⟨⟨-2, 0⟩, ⟨-1, -1⟩, ⟨1, -1⟩, ⟨0, 0⟩⟩
  , ⟨⟨-2, 0⟩, ⟨1, 1⟩, ⟨-1, 1⟩, ⟨0, 0⟩⟩
  , ⟨⟨-2, 0⟩, ⟨1, 1⟩, ⟨1, -1⟩, ⟨0, 0⟩⟩
  , ⟨⟨-2, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩, ⟨0, 0⟩⟩
  , ⟨⟨-2, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩⟩
  , ⟨⟨-2, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩⟩
  , ⟨⟨-2, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩⟩
  , ⟨⟨-2, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩⟩
  , ⟨⟨-2, 0⟩, ⟨-2, 0⟩, ⟨-2, 0⟩, ⟨-2, 0⟩⟩ ]

/-- Conjugating witnesses, entries 60–79 (aligned with `icosianChunk3`). -/
def icosianWitnessChunk3 : List Q4 :=
  [ ⟨⟨-2, 0⟩, ⟨-2, 0⟩, ⟨2, 0⟩, ⟨-2, 0⟩⟩
  , ⟨⟨-2, 0⟩, ⟨-2, 0⟩, ⟨-2, 0⟩, ⟨2, 0⟩⟩
  , ⟨⟨-2, 0⟩, ⟨-2, 0⟩, ⟨2, 0⟩, ⟨2, 0⟩⟩
  , ⟨⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, 1⟩, ⟨-2, 0⟩⟩
  , ⟨⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩, ⟨-2, 0⟩⟩
  , ⟨⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, 1⟩, ⟨2, 0⟩⟩
  , ⟨⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩, ⟨2, 0⟩⟩
  , ⟨⟨-1, 1⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨1, 1⟩⟩
  , ⟨⟨-1, 1⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨1, 1⟩⟩
  , ⟨⟨-1, 1⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨-1, -1⟩⟩
  , ⟨⟨-1, 1⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨-1, -1⟩⟩
  , ⟨⟨-2, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, 1⟩⟩
  , ⟨⟨-2, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩⟩
  , ⟨⟨-2, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, -1⟩⟩
  , ⟨⟨-2, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, -1⟩⟩
  , ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨-4, 0⟩, ⟨0, 0⟩⟩
  , ⟨⟨4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩
  , ⟨⟨-2, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩⟩
  , ⟨⟨-2, 0⟩, ⟨-1, -1⟩, ⟨1, -1⟩, ⟨0, 0⟩⟩
  , ⟨⟨-2, 0⟩, ⟨-2, 0⟩, ⟨-2, 0⟩, ⟨2, 0⟩⟩ ]

/-- Conjugating witnesses, entries 80–99 (aligned with `icosianChunk4`). -/
def icosianWitnessChunk4 : List Q4 :=
  [ ⟨⟨-2, 0⟩, ⟨-2, 0⟩, ⟨-2, 0⟩, ⟨-2, 0⟩⟩
  , ⟨⟨-2, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩⟩
  , ⟨⟨-2, 0⟩, ⟨-2, 0⟩, ⟨2, 0⟩, ⟨2, 0⟩⟩
  , ⟨⟨-2, 0⟩, ⟨1, 1⟩, ⟨1, -1⟩, ⟨0, 0⟩⟩
  , ⟨⟨-2, 0⟩, ⟨-2, 0⟩, ⟨2, 0⟩, ⟨-2, 0⟩⟩
  , ⟨⟨-2, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩⟩
  , ⟨⟨-2, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, -1⟩⟩
  , ⟨⟨0, 0⟩, ⟨-2, 0⟩, ⟨-1, 1⟩, ⟨-1, -1⟩⟩
  , ⟨⟨4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩
  , ⟨⟨-2, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩, ⟨0, 0⟩⟩
  , ⟨⟨-2, 0⟩, ⟨-2, 0⟩, ⟨-2, 0⟩, ⟨-2, 0⟩⟩
  , ⟨⟨-2, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩⟩
  , ⟨⟨-2, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, 1⟩⟩
  , ⟨⟨-2, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩⟩
  , ⟨⟨-2, 0⟩, ⟨-2, 0⟩, ⟨2, 0⟩, ⟨-2, 0⟩⟩
  , ⟨⟨-2, 0⟩, ⟨-2, 0⟩, ⟨-2, 0⟩, ⟨2, 0⟩⟩
  , ⟨⟨-2, 0⟩, ⟨-1, -1⟩, ⟨1, -1⟩, ⟨0, 0⟩⟩
  , ⟨⟨-2, 0⟩, ⟨-2, 0⟩, ⟨2, 0⟩, ⟨2, 0⟩⟩
  , ⟨⟨-2, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩⟩
  , ⟨⟨0, 0⟩, ⟨-2, 0⟩, ⟨-1, 1⟩, ⟨-1, -1⟩⟩ ]

/-- Conjugating witnesses, entries 100–119 (aligned with `icosianChunk5`). -/
def icosianWitnessChunk5 : List Q4 :=
  [ ⟨⟨4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩
  , ⟨⟨-2, 0⟩, ⟨1, 1⟩, ⟨-1, 1⟩, ⟨0, 0⟩⟩
  , ⟨⟨-2, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩⟩
  , ⟨⟨-2, 0⟩, ⟨-2, 0⟩, ⟨-2, 0⟩, ⟨2, 0⟩⟩
  , ⟨⟨-2, 0⟩, ⟨-1, -1⟩, ⟨1, -1⟩, ⟨0, 0⟩⟩
  , ⟨⟨-1, -1⟩, ⟨1, -1⟩, ⟨-2, 0⟩, ⟨0, 0⟩⟩
  , ⟨⟨-2, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩⟩
  , ⟨⟨-1, 1⟩, ⟨-2, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩⟩
  , ⟨⟨-2, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, -1⟩⟩
  , ⟨⟨-1, -1⟩, ⟨-1, 1⟩, ⟨2, 0⟩, ⟨0, 0⟩⟩
  , ⟨⟨-1, 1⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨-1, -1⟩⟩
  , ⟨⟨-2, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩, ⟨0, 0⟩⟩
  , ⟨⟨-1, -1⟩, ⟨-2, 0⟩, ⟨0, 0⟩, ⟨1, -1⟩⟩
  , ⟨⟨-2, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩⟩
  , ⟨⟨-1, 1⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨1, 1⟩⟩
  , ⟨⟨-2, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩⟩
  , ⟨⟨-2, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, 1⟩⟩
  , ⟨⟨-2, 0⟩, ⟨2, 0⟩, ⟨-2, 0⟩, ⟨-2, 0⟩⟩
  , ⟨⟨-2, 0⟩, ⟨-2, 0⟩, ⟨2, 0⟩, ⟨-2, 0⟩⟩
  , ⟨⟨0, 0⟩, ⟨-2, 0⟩, ⟨1, -1⟩, ⟨1, 1⟩⟩ ]

def icosianWitnesses : List Q4 :=
  icosianWitnessChunk0 ++ icosianWitnessChunk1 ++ icosianWitnessChunk2 ++ icosianWitnessChunk3 ++
    icosianWitnessChunk4 ++ icosianWitnessChunk5

/-- Nine class representatives (scaled by 4): `1`, `−1`, four elements with real part `±φ/2`, `±φ⁻¹/2`, then real part `−1/2`, `1/2`, and `0`. -/
def classRepList : List Q4 :=
  [ ⟨⟨4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩
  , ⟨⟨-4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩
  , ⟨⟨-1, -1⟩, ⟨-2, 0⟩, ⟨0, 0⟩, ⟨-1, 1⟩⟩
  , ⟨⟨-1, 1⟩, ⟨-2, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩⟩
  , ⟨⟨1, -1⟩, ⟨-2, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩⟩
  , ⟨⟨1, 1⟩, ⟨-2, 0⟩, ⟨0, 0⟩, ⟨-1, 1⟩⟩
  , ⟨⟨-2, 0⟩, ⟨-2, 0⟩, ⟨-2, 0⟩, ⟨-2, 0⟩⟩
  , ⟨⟨2, 0⟩, ⟨-2, 0⟩, ⟨-2, 0⟩, ⟨-2, 0⟩⟩
  , ⟨⟨0, 0⟩, ⟨-4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩ ]

/-- The listed witness for `p` (looked up by position). -/
def witnessOf (p : Q4) : Q4 := ((icosianList.zip icosianWitnesses).lookup p).getD one4

/-! ## Finite checks (`decide +kernel`, split by chunk) -/

def i4 : Q4 := ⟨0, 4, 0, 0⟩
def j4 : Q4 := ⟨0, 0, 4, 0⟩

theorem forall_mem_icosianList {P : Q4 → Prop} (h0 : ∀ p ∈ icosianChunk0, P p)
    (h1 : ∀ p ∈ icosianChunk1, P p) (h2 : ∀ p ∈ icosianChunk2, P p)
    (h3 : ∀ p ∈ icosianChunk3, P p) (h4 : ∀ p ∈ icosianChunk4, P p)
    (h5 : ∀ p ∈ icosianChunk5, P p) : ∀ p ∈ icosianList, P p := by
  intro p hp
  simp only [icosianList, List.mem_append] at hp
  rcases hp with ((((h | h) | h) | h) | h) | h
  · exact h0 p h
  · exact h1 p h
  · exact h2 p h
  · exact h3 p h
  · exact h4 p h
  · exact h5 p h

theorem ij_mem : i4 ∈ icosianList ∧ j4 ∈ icosianList := by decide +kernel

/-- Rescaled powers really are powers (divisibility by `4` at each step). -/
def PowStep (p : Q4) : Prop := ∀ k < 10, (p.powN k).mul p = (p.powN (k + 1)).smul 4

instance (p : Q4) : Decidable (PowStep p) := by unfold PowStep; infer_instance

theorem powStep0 : ∀ p ∈ icosianChunk0, PowStep p := by decide +kernel
theorem powStep1 : ∀ p ∈ icosianChunk1, PowStep p := by decide +kernel
theorem powStep2 : ∀ p ∈ icosianChunk2, PowStep p := by decide +kernel
theorem powStep3 : ∀ p ∈ icosianChunk3, PowStep p := by decide +kernel
theorem powStep4 : ∀ p ∈ icosianChunk4, PowStep p := by decide +kernel
theorem powStep5 : ∀ p ∈ icosianChunk5, PowStep p := by decide +kernel

theorem pow_step : ∀ p ∈ icosianList, PowStep p :=
  forall_mem_icosianList powStep0 powStep1 powStep2 powStep3 powStep4 powStep5

/-- The order table entry for `p`. -/
def OrdRow (p : Q4) : Prop :=
  (0 < q4Order p ∧ q4Order p ≤ 10 ∧ p.powN (q4Order p) = one4 ∧
    ∀ m < q4Order p, 0 < m → p.powN m ≠ one4) ∧
  (0 < q4RotOrder p ∧ q4RotOrder p ≤ 10 ∧
    (p.powN (q4RotOrder p) = one4 ∨ p.powN (q4RotOrder p) = negOne4) ∧
    (∀ m < q4RotOrder p, 0 < m → ¬ (p.powN m = one4 ∨ p.powN m = negOne4)) ∧
    q4RotOrder p = if q4Order p % 2 = 0 then q4Order p / 2 else q4Order p) ∧
  (q4Order p = 1 ∨ q4Order p = 2 ∨ q4Order p = 3 ∨ q4Order p = 4 ∨ q4Order p = 5 ∨
      q4Order p = 6 ∨ q4Order p = 10) ∧
  (q4Order p = 2 ↔ p = negOne4)

instance (p : Q4) : Decidable (OrdRow p) := by unfold OrdRow; infer_instance

theorem ordRow0 : ∀ p ∈ icosianChunk0, OrdRow p := by decide +kernel
theorem ordRow1 : ∀ p ∈ icosianChunk1, OrdRow p := by decide +kernel
theorem ordRow2 : ∀ p ∈ icosianChunk2, OrdRow p := by decide +kernel
theorem ordRow3 : ∀ p ∈ icosianChunk3, OrdRow p := by decide +kernel
theorem ordRow4 : ∀ p ∈ icosianChunk4, OrdRow p := by decide +kernel
theorem ordRow5 : ∀ p ∈ icosianChunk5, OrdRow p := by decide +kernel

theorem ord_row : ∀ p ∈ icosianList, OrdRow p :=
  forall_mem_icosianList ordRow0 ordRow1 ordRow2 ordRow3 ordRow4 ordRow5

/-- Commutation with `4i` and `4j`, with divisibility. -/
def CentRow (p : Q4) : Prop :=
  p.mul i4 = (p.mulN i4).smul 4 ∧ i4.mul p = (i4.mulN p).smul 4 ∧
  p.mul j4 = (p.mulN j4).smul 4 ∧ j4.mul p = (j4.mulN p).smul 4 ∧
  (p.mulN i4 = i4.mulN p → p.mulN j4 = j4.mulN p → p = one4 ∨ p = negOne4)

instance (p : Q4) : Decidable (CentRow p) := by unfold CentRow; infer_instance

theorem cent_row : ∀ p ∈ icosianList, CentRow p := by decide +kernel

/-- The witness row for `q`: the listed witness conjugates the class representative onto `q`. -/
def WitRow (q : Q4) : Prop :=
  witnessOf q ∈ icosianList ∧ classRep q ∈ icosianList ∧ (classRep q).a = q.a ∧
  (witnessOf q).mul (classRep q) = ((witnessOf q).mulN (classRep q)).smul 4 ∧
  ((witnessOf q).mulN (classRep q)).mul (witnessOf q).conj = q.smul 4

instance (q : Q4) : Decidable (WitRow q) := by unfold WitRow; infer_instance

theorem witRow0 : ∀ p ∈ icosianChunk0, WitRow p := by decide +kernel
theorem witRow1 : ∀ p ∈ icosianChunk1, WitRow p := by decide +kernel
theorem witRow2 : ∀ p ∈ icosianChunk2, WitRow p := by decide +kernel
theorem witRow3 : ∀ p ∈ icosianChunk3, WitRow p := by decide +kernel
theorem witRow4 : ∀ p ∈ icosianChunk4, WitRow p := by decide +kernel
theorem witRow5 : ∀ p ∈ icosianChunk5, WitRow p := by decide +kernel

theorem wit_row : ∀ p ∈ icosianList, WitRow p :=
  forall_mem_icosianList witRow0 witRow1 witRow2 witRow3 witRow4 witRow5

/-- The `i`-th class representative. -/
def repQ (i : Fin 9) : Q4 := classRepList.getD i one4

theorem repQ_mem : ∀ i : Fin 9, repQ i ∈ icosianList := by decide +kernel

theorem repQ_distinct : ∀ i j : Fin 9, (repQ i).a = (repQ j).a → i = j := by decide +kernel

theorem repQ_cover : ∀ p ∈ icosianList, ∃ i : Fin 9, (repQ i).a = p.a := by decide +kernel

theorem repQ_sizes : ∀ i : Fin 9,
    (icosianList.filter (fun p => decide ((repQ i).a = p.a))).length =
      (![1, 1, 12, 12, 12, 12, 20, 20, 30] : Fin 9 → ℕ) i := by decide +kernel

theorem order_count_table :
    (icosianList.filter (fun p => decide (q4Order p = 1))).length = 1 ∧
    (icosianList.filter (fun p => decide (q4Order p = 2))).length = 1 ∧
    (icosianList.filter (fun p => decide (q4Order p = 3))).length = 20 ∧
    (icosianList.filter (fun p => decide (q4Order p = 4))).length = 30 ∧
    (icosianList.filter (fun p => decide (q4Order p = 5))).length = 24 ∧
    (icosianList.filter (fun p => decide (q4Order p = 6))).length = 20 ∧
    (icosianList.filter (fun p => decide (q4Order p = 10))).length = 24 := by decide +kernel

/-! ## Transfer to the group -/

/-- The embedding of the group into `ℍ[ℝ]`. -/
noncomputable def coeQ : binaryIcosahedralGroup →* Quaternion ℝ :=
  (Units.coeHom (Quaternion ℝ)).comp binaryIcosahedralGroup.subtype

theorem coeQ_apply (u : binaryIcosahedralGroup) :
    coeQ u = ((u : (Quaternion ℝ)ˣ) : Quaternion ℝ) := rfl

theorem coeQ_injective : Function.Injective coeQ := fun _ _ h => Subtype.ext (Units.ext h)

theorem exists_toQ4 (u : binaryIcosahedralGroup) :
    ∃ p, p ∈ {p | p ∈ icosianList} ∧ toQuat p = ((u : (Quaternion ℝ)ˣ) : Quaternion ℝ) := u.2

/-- The listed scaled icosian of a group element. -/
noncomputable def toQ4 (u : binaryIcosahedralGroup) : Q4 := Classical.choose (exists_toQ4 u)

theorem toQ4_mem (u : binaryIcosahedralGroup) : toQ4 u ∈ icosianList :=
  (Classical.choose_spec (exists_toQ4 u)).1

theorem toQuat_toQ4 (u : binaryIcosahedralGroup) :
    toQuat (toQ4 u) = ((u : (Quaternion ℝ)ˣ) : Quaternion ℝ) :=
  (Classical.choose_spec (exists_toQ4 u)).2

theorem toQ4_injective : Function.Injective toQ4 := by
  intro u v h
  apply coeQ_injective
  rw [coeQ_apply, coeQ_apply, ← toQuat_toQ4, ← toQuat_toQ4, h]

theorem toQ4_surj : ∀ p ∈ icosianList, ∃ u, toQ4 u = p := by
  intro p hp
  have hx : toQuat p ∈ icosianSet := ⟨p, hp, rfl⟩
  refine ⟨icosianUnit hx, toQuat_injective ?_⟩
  rw [toQuat_toQ4, icosianUnit_coe]

theorem toQ4_one : toQ4 1 = one4 :=
  toQuat_injective (by rw [toQuat_toQ4, toQuat_one4]; rfl)

theorem negOneBI_coe : ((negOneBI : (Quaternion ℝ)ˣ) : Quaternion ℝ) = -1 := rfl

theorem toQ4_negOneBI : toQ4 negOneBI = negOne4 :=
  toQuat_injective (by rw [toQuat_toQ4, toQuat_negOne4, negOneBI_coe])

theorem toQuat_powN {p : Q4} (hp : p ∈ icosianList) :
    ∀ n ≤ 10, toQuat (p.powN n) = toQuat p ^ n := by
  intro n
  induction n with
  | zero => intro _; rw [pow_zero]; exact toQuat_one4
  | succ n ih =>
    intro hn
    rw [pow_succ, ← ih (by omega), ← toQuat_mul_of (pow_step p hp n (by omega))]

theorem coeQ_eq (u : binaryIcosahedralGroup) : coeQ u = toQuat (toQ4 u) := by
  rw [coeQ_apply, toQuat_toQ4]

theorem orderOf_eq_q4Order (u : binaryIcosahedralGroup) : orderOf u = q4Order (toQ4 u) := by
  obtain ⟨⟨h0, h10, h1, h2⟩, -⟩ := ord_row _ (toQ4_mem u)
  rw [← orderOf_injective coeQ coeQ_injective u, coeQ_eq, orderOf_eq_iff h0]
  refine ⟨?_, ?_⟩
  · rw [← toQuat_powN (toQ4_mem u) _ h10, h1, toQuat_one4]
  · intro m hm hm0 h
    rw [← toQuat_powN (toQ4_mem u) m (by omega), ← toQuat_one4] at h
    exact h2 m hm hm0 (toQuat_injective h)

theorem natCard_orderOf_eq (n : ℕ) :
    Nat.card {u : binaryIcosahedralGroup // orderOf u = n} =
      (icosianList.filter (fun p => decide (q4Order p = n))).length := by
  simp only [orderOf_eq_q4Order]
  exact natCard_filter_of_bijOn_list toQ4 _ icosianList_nodup toQ4_mem toQ4_injective toQ4_surj
    (fun p => q4Order p = n)

theorem rot_pow_eq_one_iff (u : binaryIcosahedralGroup) {m : ℕ} (hm : m ≤ 10) :
    icosianRotHom u ^ m = 1 ↔ (toQ4 u).powN m = one4 ∨ (toQ4 u).powN m = negOne4 := by
  rw [← map_pow, icosianRotHom_eq_one_iff]
  have hc : (((u ^ m : binaryIcosahedralGroup) : (Quaternion ℝ)ˣ) : Quaternion ℝ) =
      toQuat ((toQ4 u).powN m) := by
    rw [toQuat_powN (toQ4_mem u) m hm, ← coeQ_eq, ← coeQ_apply, map_pow]
  rw [hc, ← toQuat_negOne4, ← toQuat_one4, toQuat_injective.eq_iff, toQuat_injective.eq_iff]

theorem orderOf_icosianRotHom_eq (u : binaryIcosahedralGroup) :
    orderOf (icosianRotHom u) = q4RotOrder (toQ4 u) := by
  obtain ⟨-, ⟨h0, h10, h1, h2, -⟩, -⟩ := ord_row _ (toQ4_mem u)
  rw [orderOf_eq_iff h0]
  refine ⟨(rot_pow_eq_one_iff u h10).mpr h1, ?_⟩
  intro m hm hm0 h
  exact h2 m hm hm0 ((rot_pow_eq_one_iff u (by omega)).mp h)

theorem coe_inv_eq_star (c : binaryIcosahedralGroup) :
    (((c⁻¹ : binaryIcosahedralGroup) : (Quaternion ℝ)ˣ) : Quaternion ℝ) =
      star ((c : (Quaternion ℝ)ˣ) : Quaternion ℝ) := by
  rw [Subgroup.coe_inv]
  exact Units.inv_eq_of_mul_eq_one_right (icosianSet_mul_star _ c.2).1

theorem re_conj_of_unit (c x : Quaternion ℝ) (h : c * star c = 1) :
    (c * x * star c).re = x.re := by
  have hn := congrArg QuaternionAlgebra.re h
  simp only [Quaternion.re_mul, Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star,
    Quaternion.imK_star, Quaternion.re_one] at hn
  have hS : c.re * c.re + c.imI * c.imI + c.imJ * c.imJ + c.imK * c.imK = 1 := by
    ring_nf; ring_nf at hn; linarith
  have e : (c * x * star c).re =
      (c.re * c.re + c.imI * c.imI + c.imJ * c.imJ + c.imK * c.imK) * x.re := by
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
      Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star]
    ring
  rw [e, hS, one_mul]

theorem re_coe (u : binaryIcosahedralGroup) :
    ((u : (Quaternion ℝ)ˣ) : Quaternion ℝ).re = zsqrt5ToReal (toQ4 u).a / 4 := by
  rw [← toQuat_toQ4]; rfl

theorem isConj_of_rep (u b : binaryIcosahedralGroup) (hb : toQ4 b = classRep (toQ4 u)) :
    IsConj b u := by
  obtain ⟨hw, -, -, h1, h2⟩ := wit_row _ (toQ4_mem u)
  obtain ⟨c, hc⟩ := toQ4_surj _ hw
  refine isConj_iff.mpr ⟨c, coeQ_injective ?_⟩
  rw [map_mul, map_mul, coeQ_apply, coeQ_apply, coeQ_apply, coeQ_apply, coe_inv_eq_star,
    ← toQuat_toQ4 c, ← toQuat_toQ4 b, ← toQuat_toQ4 u, hc, hb, ← toQuat_conj,
    toQuat_mul_of h1, toQuat_mul_of h2]

theorem isConj_iff_a (u v : binaryIcosahedralGroup) : IsConj u v ↔ (toQ4 u).a = (toQ4 v).a := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := isConj_iff.mp h
    have e := congrArg coeQ hc
    rw [map_mul, map_mul, coeQ_apply, coeQ_apply, coeQ_apply, coeQ_apply, coe_inv_eq_star] at e
    have hre := congrArg QuaternionAlgebra.re e
    rw [re_conj_of_unit _ _ (icosianSet_mul_star _ c.2).1, re_coe, re_coe] at hre
    exact zsqrt5ToReal_injective (by linarith)
  · intro h
    obtain ⟨-, hbm, -⟩ := wit_row _ (toQ4_mem u)
    obtain ⟨b, hb⟩ := toQ4_surj _ hbm
    have hb' : toQ4 b = classRep (toQ4 v) := by rw [hb]; unfold classRep; rw [h]
    exact (isConj_of_rep u b hb).symm.trans (isConj_of_rep v b hb')

/-- The `i`-th representative in the group. -/
noncomputable def repG (i : Fin 9) : binaryIcosahedralGroup :=
  Classical.choose (toQ4_surj (repQ i) (repQ_mem i))

theorem toQ4_repG (i : Fin 9) : toQ4 (repG i) = repQ i :=
  Classical.choose_spec (toQ4_surj (repQ i) (repQ_mem i))

noncomputable def classMap (i : Fin 9) : ConjClasses binaryIcosahedralGroup :=
  ConjClasses.mk (repG i)

theorem classMap_bijective : Function.Bijective classMap := by
  constructor
  · intro i j h
    have h' := ConjClasses.mk_eq_mk_iff_isConj.mp h
    rw [isConj_iff_a, toQ4_repG, toQ4_repG] at h'
    exact repQ_distinct i j h'
  · intro x
    obtain ⟨u, rfl⟩ := ConjClasses.mk_surjective x
    obtain ⟨i, hi⟩ := repQ_cover _ (toQ4_mem u)
    refine ⟨i, ConjClasses.mk_eq_mk_iff_isConj.mpr ?_⟩
    rw [isConj_iff_a, toQ4_repG]
    exact hi

theorem natCard_carrier_mk' (g : binaryIcosahedralGroup) :
    Nat.card (ConjClasses.mk g).carrier = Nat.card {h : binaryIcosahedralGroup // IsConj g h} := by
  have hset : (ConjClasses.mk g).carrier = {h | IsConj g h} := by
    ext h
    rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj, Set.mem_ofPred_eq,
      isConj_comm]
  rw [hset]
  rfl

/-! ## The frozen statements -/

theorem orderOf_cases (u : binaryIcosahedralGroup) :
    orderOf u = 1 ∨ orderOf u = 2 ∨ orderOf u = 3 ∨ orderOf u = 4 ∨ orderOf u = 5 ∨
      orderOf u = 6 ∨ orderOf u = 10 := by
  rw [orderOf_eq_q4Order]
  exact (ord_row _ (toQ4_mem u)).2.2.1

theorem orderOf_counts :
    Nat.card {u : binaryIcosahedralGroup // orderOf u = 1} = 1 ∧
    Nat.card {u : binaryIcosahedralGroup // orderOf u = 2} = 1 ∧
    Nat.card {u : binaryIcosahedralGroup // orderOf u = 3} = 20 ∧
    Nat.card {u : binaryIcosahedralGroup // orderOf u = 4} = 30 ∧
    Nat.card {u : binaryIcosahedralGroup // orderOf u = 5} = 24 ∧
    Nat.card {u : binaryIcosahedralGroup // orderOf u = 6} = 20 ∧
    Nat.card {u : binaryIcosahedralGroup // orderOf u = 10} = 24 := by
  simp only [natCard_orderOf_eq]
  exact order_count_table

theorem orderOf_eq_two_iff_negOneBI (u : binaryIcosahedralGroup) : orderOf u = 2 ↔ u = negOneBI := by
  rw [orderOf_eq_q4Order, (ord_row _ (toQ4_mem u)).2.2.2]
  constructor
  · intro h; exact toQ4_injective (h.trans toQ4_negOneBI.symm)
  · rintro rfl; exact toQ4_negOneBI

theorem negOneBI_mem_center : negOneBI ∈ Subgroup.center binaryIcosahedralGroup := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply coeQ_injective
  rw [map_mul, map_mul, coeQ_apply, coeQ_apply, negOneBI_coe]
  simp

theorem center_eq : (Subgroup.center binaryIcosahedralGroup : Set binaryIcosahedralGroup) =
    {1, negOneBI} := by
  ext u
  simp only [SetLike.mem_coe, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hu
    rw [Subgroup.mem_center_iff] at hu
    obtain ⟨hi1, hi2, hj1, hj2, hc⟩ := cent_row _ (toQ4_mem u)
    obtain ⟨I, hI⟩ := toQ4_surj _ ij_mem.1
    obtain ⟨J, hJ⟩ := toQ4_surj _ ij_mem.2
    have eI := congrArg coeQ (hu I)
    have eJ := congrArg coeQ (hu J)
    rw [map_mul, map_mul, coeQ_eq, coeQ_eq, hI, toQuat_mul_of hi1, toQuat_mul_of hi2] at eI
    rw [map_mul, map_mul, coeQ_eq, coeQ_eq, hJ, toQuat_mul_of hj1, toQuat_mul_of hj2] at eJ
    rcases hc (toQuat_injective eI).symm (toQuat_injective eJ).symm with h | h
    · left; exact toQ4_injective (h.trans toQ4_one.symm)
    · right; exact toQ4_injective (h.trans toQ4_negOneBI.symm)
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact negOneBI_mem_center

theorem orderOf_icosianRotHom (u : binaryIcosahedralGroup) :
    orderOf (icosianRotHom u) = if orderOf u % 2 = 0 then orderOf u / 2 else orderOf u := by
  rw [orderOf_icosianRotHom_eq, orderOf_eq_q4Order]
  exact (ord_row _ (toQ4_mem u)).2.1.2.2.2.2

theorem isConj_iff_re (u v : binaryIcosahedralGroup) :
    IsConj u v ↔ ((u : (Quaternion ℝ)ˣ) : Quaternion ℝ).re = ((v : (Quaternion ℝ)ˣ) : Quaternion ℝ).re := by
  rw [isConj_iff_a, re_coe, re_coe]
  constructor
  · intro h; rw [h]
  · intro h; exact zsqrt5ToReal_injective (by linarith)

theorem conjClasses_natCard : Nat.card (ConjClasses binaryIcosahedralGroup) = 9 := by
  rw [← Nat.card_eq_of_bijective classMap classMap_bijective, Nat.card_eq_fintype_card,
    Fintype.card_fin]

theorem conjClasses_sizes : ∃ e : Fin 9 ≃ ConjClasses binaryIcosahedralGroup,
    ∀ i : Fin 9, Nat.card (e i).carrier = (![1, 1, 12, 12, 12, 12, 20, 20, 30] : Fin 9 → ℕ) i := by
  refine ⟨Equiv.ofBijective classMap classMap_bijective, fun i => ?_⟩
  rw [Equiv.ofBijective_apply, classMap, natCard_carrier_mk']
  simp only [isConj_iff_a, toQ4_repG]
  rw [natCard_filter_of_bijOn_list toQ4 _ icosianList_nodup toQ4_mem toQ4_injective toQ4_surj
    (fun p => (repQ i).a = p.a)]
  exact repQ_sizes i


/-! ## Computable layer -/

/-- The listed scaled rotation of a scaled icosian (`p.rot16 = A.smul 4`). -/
def rotM (p : Q4) : M3 :=
  (scaledRotationList.find? (fun A => decide (p.rot16 = A.smul 4))).getD (M3.scal 4)

/-- The frame (cube) permutation of a scaled icosian. -/
def q4Perm (p : Q4) : Perm (Fin 5) := framePermM3 (rotM p)

/-- Table form of `V4^(k)`: square `1` and fixing `k`. -/
def permV4 (k : Fin 5) (q : Perm (Fin 5)) : Prop := q * q = 1 ∧ q k = k

instance (k : Fin 5) (q : Perm (Fin 5)) : Decidable (permV4 k q) := by
  unfold permV4; infer_instance

/-- Table form of `Q^(k)`. -/
def inQ8 (k : Fin 5) (p : Q4) : Prop := permV4 k (q4Perm p)

instance (k : Fin 5) (p : Q4) : Decidable (inQ8 k p) := by unfold inQ8; infer_instance

/-- Generators of `Q^(k)` (two listed elements of the table form). -/
def q8x (k : Fin 5) : Q4 := (icosianList.filter (fun p => decide (inQ8 k p))).getD 2 one4
def q8y (k : Fin 5) : Q4 := (icosianList.filter (fun p => decide (inQ8 k p))).getD 3 one4

/-- The table map `QuaternionGroup 2 → Q4`: `a i ↦ x^i`, `xa i ↦ y x^i`. -/
def q8map (k : Fin 5) : QuaternionGroup 2 → Q4
  | .a i => (q8x k).powN i.val
  | .xa i => (q8y k).mulN ((q8x k).powN i.val)

/-! ## Finite checks -/

def RotRow (p : Q4) : Prop := rotM p ∈ scaledRotationList ∧ p.rot16 = (rotM p).smul 4
instance (p : Q4) : Decidable (RotRow p) := by unfold RotRow; infer_instance
theorem rotRow0 : ∀ p ∈ icosianChunk0, RotRow p := by decide +kernel
theorem rotRow1 : ∀ p ∈ icosianChunk1, RotRow p := by decide +kernel
theorem rotRow2 : ∀ p ∈ icosianChunk2, RotRow p := by decide +kernel
theorem rotRow3 : ∀ p ∈ icosianChunk3, RotRow p := by decide +kernel
theorem rotRow4 : ∀ p ∈ icosianChunk4, RotRow p := by decide +kernel
theorem rotRow5 : ∀ p ∈ icosianChunk5, RotRow p := by decide +kernel
theorem rot_row : ∀ p ∈ icosianList, RotRow p :=
  forall_mem_icosianList rotRow0 rotRow1 rotRow2 rotRow3 rotRow4 rotRow5

theorem permV4_card : ∀ k : Fin 5,
    (framePermList.filter (fun q => decide (permV4 k q))).length = 4 := by decide +kernel

theorem permV4_mul : ∀ k : Fin 5, ∀ p ∈ framePermList.filter (fun q => decide (permV4 k q)),
    ∀ q ∈ framePermList.filter (fun q => decide (permV4 k q)), permV4 k (p * q) := by decide +kernel

theorem permV4_unique : ∀ q ∈ framePermList, q * q = 1 → q ≠ 1 →
    ∃ k : Fin 5, q k = k ∧ ∀ j : Fin 5, q j = j → j = k := by decide +kernel

theorem q8_card : ∀ k : Fin 5, (icosianList.filter (fun p => decide (inQ8 k p))).length = 8 := by
  decide +kernel

theorem q8_sq : ∀ k : Fin 5, ∀ p ∈ icosianList.filter (fun p => decide (inQ8 k p)),
    p ≠ one4 → p ≠ negOne4 → p.powN 2 = negOne4 := by decide +kernel

theorem q8_inter : ∀ j k : Fin 5, j ≠ k → ∀ p ∈ icosianList.filter (fun p => decide (inQ8 k p)),
    inQ8 j p → p = one4 ∨ p = negOne4 := by decide +kernel

theorem q8_one : ∀ k : Fin 5, inQ8 k one4 ∧ inQ8 k negOne4 := by decide +kernel

theorem q8_distinct : ∀ j k : Fin 5, j ≠ k →
    ∃ p ∈ icosianList.filter (fun p => decide (inQ8 j p)), ¬ inQ8 k p := by decide +kernel

theorem sq_neg_one_count :
    (icosianList.filter (fun p => decide (p.powN 2 = negOne4))).length = 30 := by decide +kernel

theorem q8map_row : ∀ k : Fin 5, ∀ x : QuaternionGroup 2, q8map k x ∈ icosianList ∧ inQ8 k (q8map k x) := by
  decide +kernel

theorem q8map_mul : ∀ k : Fin 5, ∀ x y : QuaternionGroup 2,
    (q8map k x).mul (q8map k y) = (q8map k (x * y)).smul 4 := by decide +kernel

theorem q8map_inj : ∀ k : Fin 5, ∀ x y : QuaternionGroup 2, q8map k x = q8map k y → x = y := by
  decide +kernel

theorem re_zero_iff : ∀ p ∈ icosianList, (p.a = 0 ↔ q4Order p = 4) := by decide +kernel

theorem a_values : ∀ p ∈ icosianList, p.a = 4 ∨ p.a = -4 ∨ p.a = 2 ∨ p.a = -2 ∨ p.a = ⟨1, 1⟩ ∨
    p.a = ⟨-1, -1⟩ ∨ p.a = ⟨-1, 1⟩ ∨ p.a = ⟨1, -1⟩ ∨ p.a = 0 := by decide +kernel

/-! ## The groups `V4^(k)` and `Q^(k)` -/

instance : Finite icosahedralRotationGroup :=
  Nat.finite_of_card_ne_zero (by rw [icosahedralRotationGroup_natCard]; norm_num)

instance : Finite binaryIcosahedralGroup :=
  Nat.finite_of_card_ne_zero (by rw [binaryIcosahedralGroup_natCard]; norm_num)

theorem toPerm_one : toPerm 1 = 1 := by simp [toPerm]

theorem toPerm_inv (g : icosahedralRotationGroup) : toPerm g⁻¹ = (toPerm g)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← toPerm_mul, inv_mul_cancel, toPerm_one])

theorem sq_eq_one_iff_or {G : Type*} [Group G] (g : G) : g * g = 1 ↔ g = 1 ∨ orderOf g = 2 := by
  rw [← sq, ← orderOf_dvd_iff_pow_eq_one, Nat.dvd_prime Nat.prime_two, orderOf_eq_one_iff]

theorem mul_self_eq_one_iff_toPerm (g : icosahedralRotationGroup) :
    g * g = 1 ↔ toPerm g * toPerm g = 1 := by
  rw [← toPerm_mul, ← toPerm_one, toPerm_injective.eq_iff]

theorem cubeV4_carrier_iff (k : Fin 5) (g : icosahedralRotationGroup) :
    ((g = 1 ∨ orderOf g = 2) ∧
      (fun v => ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v) ''
        officialCube k = officialCube k) ↔ permV4 k (toPerm g) := by
  rw [officialCube_image_eq_iff, ← sq_eq_one_iff_or, mul_self_eq_one_iff_toPerm]
  rfl

theorem permV4_mem {k : Fin 5} {q : Perm (Fin 5)} (hq : q ∈ framePermList) (h : permV4 k q) :
    q ∈ framePermList.filter (fun q => decide (permV4 k q)) :=
  List.mem_filter.mpr ⟨hq, decide_eq_true h⟩

/-- `V4^(k)`: the identity and the involutions of `I` stabilising `officialCube k`. -/
noncomputable def cubeV4 (k : Fin 5) : Subgroup icosahedralRotationGroup where
  carrier := {g | (g = 1 ∨ orderOf g = 2) ∧
    (fun v => ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v) ''
      officialCube k = officialCube k}
  one_mem' := (cubeV4_carrier_iff k 1).mpr (by rw [toPerm_one]; exact ⟨mul_one 1, rfl⟩)
  mul_mem' := fun {g h} hg hh => (cubeV4_carrier_iff k (g * h)).mpr (by
    rw [toPerm_mul]
    exact permV4_mul k _ (permV4_mem (toPerm_mem g) ((cubeV4_carrier_iff k g).mp hg)) _
      (permV4_mem (toPerm_mem h) ((cubeV4_carrier_iff k h).mp hh)))
  inv_mem' := fun {g} hg => (cubeV4_carrier_iff k g⁻¹).mpr (by
    have h := (cubeV4_carrier_iff k g).mp hg
    have e : (toPerm g)⁻¹ = toPerm g := inv_eq_of_mul_eq_one_left h.1
    rw [toPerm_inv, e]
    exact h)

/-- `Q^(k) = π⁻¹(V4^(k))`. -/
noncomputable def cubeQ8 (k : Fin 5) : Subgroup binaryIcosahedralGroup :=
  (cubeV4 k).comap icosianRotHom

/-! ## Bridges -/

theorem toM3_icosianRotHom (u : binaryIcosahedralGroup) : toM3 (icosianRotHom u) = rotM (toQ4 u) := by
  obtain ⟨-, hrot⟩ := rot_row _ (toQ4_mem u)
  have h1 : realQuarter (toM3 (icosianRotHom u)).toMatrix = realQuarter (rotM (toQ4 u)).toMatrix := by
    rw [← coe_eq_realQuarter_toM3, icosianRotHom_spec, ← toQuat_toQ4, rotH_toQuat hrot]
  exact M3.toMatrix_injective (realQuarter_injective h1)

theorem toPerm_icosianRotHom (u : binaryIcosahedralGroup) :
    toPerm (icosianRotHom u) = q4Perm (toQ4 u) := by
  rw [toPerm_eq, toM3_icosianRotHom]; rfl

theorem mem_cubeV4_iff_perm (k : Fin 5) (g : icosahedralRotationGroup) :
    g ∈ cubeV4 k ↔ permV4 k (toPerm g) := cubeV4_carrier_iff k g

theorem mem_cubeQ8_iff (k : Fin 5) (u : binaryIcosahedralGroup) :
    u ∈ cubeQ8 k ↔ inQ8 k (toQ4 u) := by
  rw [cubeQ8, Subgroup.mem_comap, mem_cubeV4_iff_perm, toPerm_icosianRotHom]; rfl

theorem inQ8_mem {k : Fin 5} {p : Q4} (hp : p ∈ icosianList) (h : inQ8 k p) :
    p ∈ icosianList.filter (fun p => decide (inQ8 k p)) :=
  List.mem_filter.mpr ⟨hp, decide_eq_true h⟩

theorem icosianRotHom_negOneBI : icosianRotHom negOneBI = 1 :=
  (icosianRotHom_eq_one_iff _).mpr (Or.inr negOneBI_coe)

theorem negOneBI_mul_self : negOneBI * negOneBI = 1 := by
  apply coeQ_injective
  rw [map_mul, map_one, coeQ_apply, negOneBI_coe]; norm_num

theorem negOneBI_comm (g : binaryIcosahedralGroup) : g * negOneBI = negOneBI * g :=
  (Subgroup.mem_center_iff.mp negOneBI_mem_center g)

theorem icosianRotHom_eq_iff (x y : binaryIcosahedralGroup) :
    icosianRotHom x = icosianRotHom y ↔ x = y ∨ x = negOneBI * y := by
  constructor
  · intro h
    have h1 : icosianRotHom (x * y⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
    rcases (icosianRotHom_eq_one_iff _).mp h1 with h2 | h2
    · left; exact mul_inv_eq_one.mp (Subtype.ext (Units.ext h2))
    · right; exact mul_inv_eq_iff_eq_mul.mp (Subtype.ext (Units.ext (h2.trans negOneBI_coe.symm)))
  · rintro (rfl | rfl)
    · rfl
    · rw [map_mul, icosianRotHom_negOneBI, one_mul]

theorem re_negOneBI_mul (u : binaryIcosahedralGroup) :
    (((negOneBI * u : binaryIcosahedralGroup) : (Quaternion ℝ)ˣ) : Quaternion ℝ).re =
      -((u : (Quaternion ℝ)ˣ) : Quaternion ℝ).re := by
  rw [Subgroup.coe_mul, Units.val_mul, negOneBI_coe]; simp

theorem sq_eq_negOneBI_iff (q : binaryIcosahedralGroup) :
    q ^ 2 = negOneBI ↔ (toQ4 q).powN 2 = negOne4 := by
  have e : coeQ (q ^ 2) = toQuat ((toQ4 q).powN 2) := by
    rw [map_pow, coeQ_eq, toQuat_powN (toQ4_mem q) 2 (by norm_num)]
  have e2 : coeQ negOneBI = toQuat negOne4 := by rw [coeQ_eq, toQ4_negOneBI]
  constructor
  · intro h; exact toQuat_injective (e.symm.trans ((congrArg coeQ h).trans e2))
  · intro h; exact coeQ_injective (e.trans ((congrArg toQuat h).trans e2.symm))

/-! ## Q8 -/

noncomputable def q8elem (k : Fin 5) (x : QuaternionGroup 2) : binaryIcosahedralGroup :=
  Classical.choose (toQ4_surj (q8map k x) (q8map_row k x).1)

theorem toQ4_q8elem (k : Fin 5) (x : QuaternionGroup 2) : toQ4 (q8elem k x) = q8map k x :=
  Classical.choose_spec (toQ4_surj (q8map k x) (q8map_row k x).1)

noncomputable def q8hom (k : Fin 5) : QuaternionGroup 2 →* binaryIcosahedralGroup :=
  MonoidHom.mk' (q8elem k) (fun x y => coeQ_injective (by
    rw [map_mul, coeQ_eq, coeQ_eq, coeQ_eq, toQ4_q8elem, toQ4_q8elem, toQ4_q8elem,
      toQuat_mul_of (q8map_mul k x y)]))

theorem q8hom_injective (k : Fin 5) : Function.Injective (q8hom k) := fun x y h =>
  q8map_inj k x y (by
    rw [← toQ4_q8elem, ← toQ4_q8elem]
    exact congrArg toQ4 h)

/-! ## The frozen statements -/

theorem mem_cubeV4 (k : Fin 5) (g : icosahedralRotationGroup) :
    g ∈ cubeV4 k ↔ (g = 1 ∨ orderOf g = 2) ∧
      (fun v => ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v) ''
        officialCube k = officialCube k := Iff.rfl

theorem cubeV4_natCard (k : Fin 5) : Nat.card (cubeV4 k) = 4 := by
  rw [← permV4_card k, ← natCard_filter_of_bijOn_list toPerm _ framePermList_nodup toPerm_mem
    toPerm_injective toPerm_surj (fun q => permV4 k q)]
  exact Nat.card_congr (Equiv.subtypeEquivRight (fun g => mem_cubeV4_iff_perm k g))

theorem cubeV4_isKleinFour (k : Fin 5) : IsKleinFour (cubeV4 k) := by
  have : Nontrivial (cubeV4 k) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [cubeV4_natCard]; norm_num)
  refine ⟨cubeV4_natCard k, (Monoid.exponent_eq_prime_iff Nat.prime_two).mpr fun g hg => ?_⟩
  rw [← Subgroup.orderOf_coe]
  rcases ((mem_cubeV4 k g).mp g.2).1 with h | h
  · exact absurd (Subtype.ext h) hg
  · exact h

theorem involution_mem_unique_cubeV4 (g : icosahedralRotationGroup) (hg : orderOf g = 2) :
    ∃! k : Fin 5, g ∈ cubeV4 k := by
  have h1 : toPerm g * toPerm g = 1 :=
    (mul_self_eq_one_iff_toPerm g).mp ((sq_eq_one_iff_or g).mpr (Or.inr hg))
  have h2 : toPerm g ≠ 1 := by
    intro h
    rw [← toPerm_one, toPerm_injective.eq_iff] at h
    rw [h, orderOf_one] at hg
    exact absurd hg (by norm_num)
  obtain ⟨k, hk, huniq⟩ := permV4_unique _ (toPerm_mem g) h1 h2
  exact ⟨k, (mem_cubeV4_iff_perm k g).mpr ⟨h1, hk⟩,
    fun j hj => huniq j ((mem_cubeV4_iff_perm j g).mp hj).2⟩

theorem cubeQ8_natCard (k : Fin 5) : Nat.card (cubeQ8 k) = 8 := by
  rw [← q8_card k, ← natCard_filter_of_bijOn_list toQ4 _ icosianList_nodup toQ4_mem toQ4_injective
    toQ4_surj (fun p => inQ8 k p)]
  exact Nat.card_congr (Equiv.subtypeEquivRight (fun u => mem_cubeQ8_iff k u))

theorem cubeQ8_sq (k : Fin 5) : ∀ q ∈ cubeQ8 k, q ≠ 1 → q ≠ negOneBI → q ^ 2 = negOneBI := by
  intro q hq h1 h2
  rw [sq_eq_negOneBI_iff]
  refine q8_sq k _ (inQ8_mem (toQ4_mem q) ((mem_cubeQ8_iff k q).mp hq)) ?_ ?_
  · intro h; exact h1 (toQ4_injective (h.trans toQ4_one.symm))
  · intro h; exact h2 (toQ4_injective (h.trans toQ4_negOneBI.symm))

theorem cubeQ8_mulEquiv (k : Fin 5) : Nonempty (cubeQ8 k ≃* QuaternionGroup 2) := by
  have hle : (q8hom k).range ≤ cubeQ8 k := by
    rintro _ ⟨x, rfl⟩
    rw [mem_cubeQ8_iff]
    show inQ8 k (toQ4 (q8elem k x))
    rw [toQ4_q8elem]
    exact (q8map_row k x).2
  have hcard : Nat.card (q8hom k).range = 8 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective (q8hom_injective k)).toEquiv,
      Nat.card_eq_fintype_card, QuaternionGroup.card]
  have heq : (q8hom k).range = cubeQ8 k :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, cubeQ8_natCard])
  exact ⟨(MulEquiv.subgroupCongr heq).symm.trans (MonoidHom.ofInjective (q8hom_injective k)).symm⟩

theorem cubeQ8_inf (j k : Fin 5) (hjk : j ≠ k) :
    ((cubeQ8 j ⊓ cubeQ8 k : Subgroup binaryIcosahedralGroup) : Set binaryIcosahedralGroup) =
      {1, negOneBI} := by
  ext u
  simp only [Subgroup.coe_inf, Set.mem_inter_iff, SetLike.mem_coe, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨hj, hk⟩
    rw [mem_cubeQ8_iff] at hj hk
    rcases q8_inter j k hjk _ (inQ8_mem (toQ4_mem u) hk) hj with h | h
    · left; exact toQ4_injective (h.trans toQ4_one.symm)
    · right; exact toQ4_injective (h.trans toQ4_negOneBI.symm)
  · rintro (rfl | rfl)
    · exact ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩
    · rw [mem_cubeQ8_iff, mem_cubeQ8_iff, toQ4_negOneBI]
      exact ⟨(q8_one j).2, (q8_one k).2⟩

theorem natCard_sq_eq_negOneBI : Nat.card {q : binaryIcosahedralGroup // q ^ 2 = negOneBI} = 30 := by
  rw [← sq_neg_one_count, ← natCard_filter_of_bijOn_list toQ4 _ icosianList_nodup toQ4_mem
    toQ4_injective toQ4_surj (fun p => p.powN 2 = negOne4)]
  exact Nat.card_congr (Equiv.subtypeEquivRight sq_eq_negOneBI_iff)

theorem permV4_conj (k : Fin 5) (σ τ : Perm (Fin 5)) :
    permV4 (σ k) τ ↔ permV4 k (σ⁻¹ * τ * σ) := by
  unfold permV4
  have e : σ⁻¹ * τ * σ * (σ⁻¹ * τ * σ) = σ⁻¹ * (τ * τ) * σ⁻¹⁻¹ := by group
  rw [e, conj_eq_one_iff, Perm.mul_apply, Perm.mul_apply, Perm.inv_eq_iff_eq]

theorem mem_cubeQ8_conj (u v : binaryIcosahedralGroup) (k : Fin 5) :
    v ∈ cubeQ8 (toPerm (icosianRotHom u) k) ↔ u⁻¹ * v * u ∈ cubeQ8 k := by
  rw [cubeQ8, cubeQ8, Subgroup.mem_comap, Subgroup.mem_comap, mem_cubeV4_iff_perm,
    mem_cubeV4_iff_perm, permV4_conj, map_mul, map_mul, map_inv, toPerm_mul, toPerm_mul, toPerm_inv]

theorem cubeQ8_map_conj (u : binaryIcosahedralGroup) (k : Fin 5) :
    (cubeQ8 k).map (MulAut.conj u).toMonoidHom = cubeQ8 (toPerm (icosianRotHom u) k) := by
  ext v
  rw [Subgroup.mem_map, mem_cubeQ8_conj]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    convert hw using 1
    group
  · intro h
    refine ⟨u⁻¹ * v * u, h, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem cubeQ8_injective : Function.Injective cubeQ8 := by
  intro a b hab
  by_contra h
  obtain ⟨p, hp, hnot⟩ := q8_distinct a b h
  obtain ⟨hpL, hpa⟩ := List.mem_filter.mp hp
  obtain ⟨u, rfl⟩ := toQ4_surj p hpL
  have hu : u ∈ cubeQ8 a := (mem_cubeQ8_iff a u).mpr (of_decide_eq_true hpa)
  rw [hab, mem_cubeQ8_iff] at hu
  exact hnot hu

theorem cubeQ8_map_conj_iff (u : binaryIcosahedralGroup) (j k : Fin 5) :
    (cubeQ8 k).map (MulAut.conj u).toMonoidHom = cubeQ8 j ↔
      (fun v => (((icosianRotHom u : icosahedralRotationGroup) : specialOrthogonalGroup (Fin 3) ℝ) :
        Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v) '' officialCube k = officialCube j := by
  rw [cubeQ8_map_conj, cubeQ8_injective.eq_iff, officialCube_image_eq_iff]

theorem cubeQ8_not_normal (k : Fin 5) : ¬ (cubeQ8 k).Normal := by
  intro hN
  have hne : ∀ k : Fin 5, k + 1 ≠ k := by decide
  obtain ⟨q, hq, hqk⟩ := table_reach (k + 1) k
  obtain ⟨g, rfl⟩ := toPerm_surj q hq
  obtain ⟨u, rfl⟩ := icosianRotHom_surjective g
  have hle : cubeQ8 (k + 1) ≤ cubeQ8 k := by
    intro v hv
    rw [← hqk, ← cubeQ8_map_conj] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact hN.conj_mem w hw u
  have heq : cubeQ8 (k + 1) = cubeQ8 k :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [cubeQ8_natCard, cubeQ8_natCard])
  exact hne k (cubeQ8_injective heq)

theorem cube_stabilizer_lifts_to_Q8 (k : Fin 5) :
    Nat.card (cubeQ8 k) = 8 ∧ (∀ q ∈ cubeQ8 k, q ≠ 1 → q ≠ negOneBI → q ^ 2 = negOneBI) ∧
      Nonempty (cubeQ8 k ≃* QuaternionGroup 2) ∧ ¬ (cubeQ8 k).Normal :=
  ⟨cubeQ8_natCard k, cubeQ8_sq k, cubeQ8_mulEquiv k, cubeQ8_not_normal k⟩

theorem not_splits_icosian_cover :
    ¬ ∃ s : icosahedralRotationGroup →* binaryIcosahedralGroup, ∀ g, icosianRotHom (s g) = g := by
  rintro ⟨s, hs⟩
  obtain ⟨I, hI⟩ := toQ4_surj _ ij_mem.1
  have hI4 : orderOf I = 4 := by
    rw [orderOf_eq_q4Order, hI]; decide +kernel
  have hh : orderOf (icosianRotHom I) = 2 := by
    rw [orderOf_icosianRotHom, hI4]; decide
  have hsq : s (icosianRotHom I) ^ 2 = 1 := by
    rw [← map_pow, ← hh, pow_orderOf_eq_one, map_one]
  have hd : orderOf (s (icosianRotHom I)) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
  have h1 : icosianRotHom (s (icosianRotHom I)) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
    · rw [orderOf_eq_one_iff.mp h, map_one]
    · rw [(orderOf_eq_two_iff_negOneBI _).mp h, icosianRotHom_negOneBI]
  rw [hs, ← orderOf_eq_one_iff] at h1
  rw [h1] at hh
  exact absurd hh (by norm_num)

theorem orderOf_icosianRotHom_eq_two_iff (u : binaryIcosahedralGroup) :
    orderOf (icosianRotHom u) = 2 ↔ orderOf u = 4 := by
  rw [orderOf_icosianRotHom]
  rcases orderOf_cases u with h | h | h | h | h | h | h <;> rw [h] <;> decide

theorem re_eq_zero_iff_a (u : binaryIcosahedralGroup) :
    ((u : (Quaternion ℝ)ˣ) : Quaternion ℝ).re = 0 ↔ (toQ4 u).a = 0 := by
  rw [re_coe]
  constructor
  · intro h; apply zsqrt5ToReal_injective; rw [map_zero]; linarith
  · intro h; rw [h, map_zero, zero_div]

theorem re_eq_zero_iff_involution (u : binaryIcosahedralGroup) :
    ((u : (Quaternion ℝ)ˣ) : Quaternion ℝ).re = 0 ↔ orderOf (icosianRotHom u) = 2 := by
  rw [re_eq_zero_iff_a, re_zero_iff _ (toQ4_mem u), ← orderOf_eq_q4Order,
    orderOf_icosianRotHom_eq_two_iff]

theorem isConj_of_involution (u v : binaryIcosahedralGroup) (hu : orderOf (icosianRotHom u) = 2)
    (hv : orderOf (icosianRotHom v) = 2) : IsConj u v := by
  rw [isConj_iff_re, (re_eq_zero_iff_involution u).mpr hu, (re_eq_zero_iff_involution v).mpr hv]

theorem natCard_involution_preimage :
    Nat.card {u : binaryIcosahedralGroup // orderOf (icosianRotHom u) = 2} = 30 := by
  rw [← orderOf_counts.2.2.2.1]
  exact Nat.card_congr (Equiv.subtypeEquivRight orderOf_icosianRotHom_eq_two_iff)

theorem isConj_icosianRotHom_iff (u v : binaryIcosahedralGroup) :
    IsConj (icosianRotHom u) (icosianRotHom v) ↔ IsConj u v ∨ IsConj (negOneBI * u) v := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := isConj_iff.mp h
    obtain ⟨c', rfl⟩ := icosianRotHom_surjective c
    have e : icosianRotHom (c' * u * c'⁻¹) = icosianRotHom v := by
      rw [map_mul, map_mul, map_inv, hc]
    rcases (icosianRotHom_eq_iff _ _).mp e with h1 | h1
    · left; exact isConj_iff.mpr ⟨c', h1⟩
    · right
      refine isConj_iff.mpr ⟨c', ?_⟩
      have e2 : c' * (negOneBI * u) * c'⁻¹ = negOneBI * (c' * u * c'⁻¹) := by
        rw [← mul_assoc, negOneBI_comm, mul_assoc, mul_assoc, mul_assoc]
      rw [e2, h1, ← mul_assoc, negOneBI_mul_self, one_mul]
  · rintro (h | h)
    · exact icosianRotHom.map_isConj h
    · have := icosianRotHom.map_isConj h
      rwa [map_mul, icosianRotHom_negOneBI, one_mul] at this

theorem isConj_negOneBI_mul_iff (u : binaryIcosahedralGroup) :
    IsConj u (negOneBI * u) ↔ orderOf (icosianRotHom u) = 2 := by
  rw [isConj_iff_re, re_negOneBI_mul, ← re_eq_zero_iff_involution]
  constructor
  · intro h; linarith
  · intro h; rw [h, neg_zero]

theorem isConj_iff_sign (u v : binaryIcosahedralGroup) (hu : orderOf (icosianRotHom u) ≠ 2) :
    IsConj u v ↔ IsConj (icosianRotHom u) (icosianRotHom v) ∧
      (0 < ((u : (Quaternion ℝ)ˣ) : Quaternion ℝ).re ↔ 0 < ((v : (Quaternion ℝ)ˣ) : Quaternion ℝ).re) := by
  constructor
  · intro h
    exact ⟨icosianRotHom.map_isConj h, by rw [(isConj_iff_re u v).mp h]⟩
  · rintro ⟨hc, hs⟩
    rcases (isConj_icosianRotHom_iff u v).mp hc with h | h
    · exact h
    · exfalso
      have hv := (isConj_iff_re _ _).mp h
      rw [re_negOneBI_mul] at hv
      have hu0 : ((u : (Quaternion ℝ)ˣ) : Quaternion ℝ).re ≠ 0 :=
        fun h0 => hu ((re_eq_zero_iff_involution u).mp h0)
      rw [← hv] at hs
      rcases lt_or_gt_of_ne hu0 with h' | h'
      · have := hs.mpr (by linarith); linarith
      · have := hs.mp h'; linarith

theorem isConj_negOneBI_mul_mul (u v : binaryIcosahedralGroup) :
    IsConj u v ↔ IsConj (negOneBI * u) (negOneBI * v) := by
  rw [isConj_iff_re, isConj_iff_re, re_negOneBI_mul, re_negOneBI_mul, neg_inj]

theorem natCard_isConj_negOneBI_mul (u : binaryIcosahedralGroup) :
    Nat.card {v : binaryIcosahedralGroup // IsConj u v} =
      Nat.card {v : binaryIcosahedralGroup // IsConj (negOneBI * u) v} :=
  Nat.card_congr (Equiv.subtypeEquiv (Equiv.mulLeft negOneBI)
    (fun v => isConj_negOneBI_mul_mul u v))

theorem two_re_mem (u : binaryIcosahedralGroup) :
    2 * ((u : (Quaternion ℝ)ˣ) : Quaternion ℝ).re ∈ ({2, -2, 1, -1, Real.goldenRatio,
      -Real.goldenRatio, Real.goldenRatio⁻¹, -Real.goldenRatio⁻¹, 0} : Set ℝ) := by
  rw [re_coe, Real.inv_goldenRatio, Real.goldenRatio, Real.goldenConj]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases a_values _ (toQ4_mem u) with h | h | h | h | h | h | h | h | h <;> rw [h, zsqrt5ToReal_apply]
  · left; norm_num
  · right; left; norm_num
  · right; right; left; norm_num
  · right; right; right; left; norm_num
  · right; right; right; right; left; push_cast; ring
  · right; right; right; right; right; left; push_cast; ring
  · right; right; right; right; right; right; left; push_cast; ring
  · right; right; right; right; right; right; right; left; push_cast; ring
  · right; right; right; right; right; right; right; right; norm_num

theorem icosian_conjugacy_classes_9 :
    [1, 1, 30, 20, 20, 12, 12, 12, 12].sum = 120 ∧
      [1, 1, 30, 20, 20, 12, 12, 12, 12].Perm [1, 1, 12, 12, 12, 12, 20, 20, 30] ∧
      Nat.card (ConjClasses binaryIcosahedralGroup) = 9 :=
  ⟨by decide, by decide, conjClasses_natCard⟩

#print axioms mem_cubeV4
#print axioms cubeV4_natCard
#print axioms cubeV4_isKleinFour
#print axioms involution_mem_unique_cubeV4
#print axioms cubeQ8_natCard
#print axioms cubeQ8_sq
#print axioms cubeQ8_mulEquiv
#print axioms cubeQ8_inf
#print axioms natCard_sq_eq_negOneBI
#print axioms mem_cubeQ8_conj
#print axioms cubeQ8_map_conj_iff
#print axioms cubeQ8_not_normal
#print axioms cube_stabilizer_lifts_to_Q8
#print axioms not_splits_icosian_cover
#print axioms orderOf_icosianRotHom_eq_two_iff
#print axioms re_eq_zero_iff_involution
#print axioms isConj_of_involution
#print axioms natCard_involution_preimage
#print axioms isConj_icosianRotHom_iff
#print axioms isConj_negOneBI_mul_iff
#print axioms isConj_iff_sign
#print axioms natCard_isConj_negOneBI_mul
#print axioms two_re_mem
#print axioms icosian_conjugacy_classes_9
#print axioms cubeV4
#print axioms cubeQ8
