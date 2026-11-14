/-
Scratch file, dated 2026-11-10. Not a Lake target. Not peer reviewed.

Element orders, centre and conjugacy classes of the 120-element icosian group.
Statement text and definitions were frozen before proving.

Imports `BinaryIcosahedralIcosians_2026-11-10` (src 9c9c6451…) unchanged.

Method: rescaled powers, order tables, commutation with `4i`, `4j`, and listed conjugating witnesses
are checked by `decide +kernel` on the explicit lists (split by chunk), then transferred to the group
via `toQuat`. Conjugation preserves the real part; a listed witness conjugates the class
representative onto each element.
-/
import «BinaryIcosahedralIcosians_2026-11-10»

open Equiv Matrix

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

theorem orderOf_eq_two_iff (u : binaryIcosahedralGroup) : orderOf u = 2 ↔ u = negOneBI := by
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

#print axioms orderOf_cases
#print axioms orderOf_counts
#print axioms orderOf_eq_two_iff
#print axioms negOneBI_mem_center
#print axioms center_eq
#print axioms orderOf_icosianRotHom
#print axioms isConj_iff_re
#print axioms conjClasses_natCard
#print axioms conjClasses_sizes
