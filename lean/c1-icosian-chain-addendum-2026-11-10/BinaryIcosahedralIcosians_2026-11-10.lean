/-
Scratch file, dated 2026-11-10. Not a Lake target. Not peer reviewed.

The 120 icosians and the double cover onto the official icosahedral rotation group.
Statement text and definitions were frozen before proving.

Imports `IcosahedralAbstractions_2026-11-10` (src dc045da6…) unchanged and Mathlib's quaternions.
No existing file is edited.

Method: finite facts about the explicit list of 120 scaled icosians over `ℤ[√5]` (closure, conjugates,
norms, rotation images in `scaledRotationList`, every listed rotation hit, the two icosians with the
identity rotation) are checked by `decide +kernel`. They are transferred to `Quaternion ℝ` via `toQuat`,
and to the official group via `toM3` / `coe_eq_realQuarter_repM3`. `rotH_mul` and `rotH_conj_action`
are ring identities tying the homomorphism to the action v ↦ q v q⋆.
-/
import «IcosahedralAbstractions_2026-11-10»
import Mathlib.Algebra.Quaternion

open Equiv Matrix

/-- A quaternion over `ℤ[√5]`, components `(a, b, c, d)` for `a + b i + c j + d k`. -/
structure Q4 where
  a : Zsqrt5
  b : Zsqrt5
  c : Zsqrt5
  d : Zsqrt5
  deriving DecidableEq

namespace Q4

/-- Hamilton product, written out. -/
def mul (p q : Q4) : Q4 :=
  ⟨p.a * q.a - p.b * q.b - p.c * q.c - p.d * q.d,
   p.a * q.b + p.b * q.a + p.c * q.d - p.d * q.c,
   p.a * q.c - p.b * q.d + p.c * q.a + p.d * q.b,
   p.a * q.d + p.b * q.c - p.c * q.b + p.d * q.a⟩

def smul (k : Zsqrt5) (p : Q4) : Q4 := ⟨k * p.a, k * p.b, k * p.c, k * p.d⟩

/-- Quaternion conjugate. -/
def conj (p : Q4) : Q4 := ⟨p.a, -p.b, -p.c, -p.d⟩

/-- The homogeneous rotation matrix of `p` (for `4q`, this is `16` times the rotation of `q`). -/
def rot16 (p : Q4) : M3 :=
  ⟨p.a * p.a + p.b * p.b - p.c * p.c - p.d * p.d, 2 * (p.b * p.c - p.a * p.d),
    2 * (p.b * p.d + p.a * p.c),
   2 * (p.b * p.c + p.a * p.d), p.a * p.a - p.b * p.b + p.c * p.c - p.d * p.d,
    2 * (p.c * p.d - p.a * p.b),
   2 * (p.b * p.d - p.a * p.c), 2 * (p.c * p.d + p.a * p.b),
    p.a * p.a - p.b * p.b - p.c * p.c + p.d * p.d⟩

end Q4

/-- The 120 icosians, scaled by 4: `4 q` for the unit quaternions `±1, ±i, ±j, ±k`,
`(±1 ± i ± j ± k)/2`, and `(±φ, ±1, ±φ⁻¹, 0)/2` placed by the odd permutations of the four
coordinates (`2φ = 1 + √5`, `2φ⁻¹ = √5 − 1`). The odd-permutation choice matches the official
vertex set; this is re-checked in Lean, not assumed. -/
def icosianChunk0 : List Q4 :=
  [ ⟨⟨4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩
  , ⟨⟨-4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩
  , ⟨⟨-2, 0⟩, ⟨-2, 0⟩, ⟨-2, 0⟩, ⟨-2, 0⟩⟩
  , ⟨⟨-2, 0⟩, ⟨-2, 0⟩, ⟨-2, 0⟩, ⟨2, 0⟩⟩
  , ⟨⟨-2, 0⟩, ⟨-2, 0⟩, ⟨2, 0⟩, ⟨-2, 0⟩⟩
  , ⟨⟨-2, 0⟩, ⟨-2, 0⟩, ⟨2, 0⟩, ⟨2, 0⟩⟩
  , ⟨⟨-2, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩, ⟨0, 0⟩⟩
  , ⟨⟨-2, 0⟩, ⟨-1, -1⟩, ⟨1, -1⟩, ⟨0, 0⟩⟩
  , ⟨⟨-2, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩⟩
  , ⟨⟨-2, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩⟩
  , ⟨⟨-2, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩⟩
  , ⟨⟨-2, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, -1⟩⟩
  , ⟨⟨-2, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, 1⟩⟩
  , ⟨⟨-2, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, -1⟩⟩
  , ⟨⟨-2, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩⟩
  , ⟨⟨-2, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩⟩
  , ⟨⟨-2, 0⟩, ⟨1, 1⟩, ⟨-1, 1⟩, ⟨0, 0⟩⟩
  , ⟨⟨-2, 0⟩, ⟨1, 1⟩, ⟨1, -1⟩, ⟨0, 0⟩⟩
  , ⟨⟨-2, 0⟩, ⟨2, 0⟩, ⟨-2, 0⟩, ⟨-2, 0⟩⟩
  , ⟨⟨-2, 0⟩, ⟨2, 0⟩, ⟨-2, 0⟩, ⟨2, 0⟩⟩
  ]

def icosianChunk1 : List Q4 :=
  [ ⟨⟨-2, 0⟩, ⟨2, 0⟩, ⟨2, 0⟩, ⟨-2, 0⟩⟩
  , ⟨⟨-2, 0⟩, ⟨2, 0⟩, ⟨2, 0⟩, ⟨2, 0⟩⟩
  , ⟨⟨-1, -1⟩, ⟨-2, 0⟩, ⟨0, 0⟩, ⟨-1, 1⟩⟩
  , ⟨⟨-1, -1⟩, ⟨-2, 0⟩, ⟨0, 0⟩, ⟨1, -1⟩⟩
  , ⟨⟨-1, -1⟩, ⟨-1, 1⟩, ⟨-2, 0⟩, ⟨0, 0⟩⟩
  , ⟨⟨-1, -1⟩, ⟨-1, 1⟩, ⟨2, 0⟩, ⟨0, 0⟩⟩
  , ⟨⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, 1⟩, ⟨-2, 0⟩⟩
  , ⟨⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, 1⟩, ⟨2, 0⟩⟩
  , ⟨⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩, ⟨-2, 0⟩⟩
  , ⟨⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩, ⟨2, 0⟩⟩
  , ⟨⟨-1, -1⟩, ⟨1, -1⟩, ⟨-2, 0⟩, ⟨0, 0⟩⟩
  , ⟨⟨-1, -1⟩, ⟨1, -1⟩, ⟨2, 0⟩, ⟨0, 0⟩⟩
  , ⟨⟨-1, -1⟩, ⟨2, 0⟩, ⟨0, 0⟩, ⟨-1, 1⟩⟩
  , ⟨⟨-1, -1⟩, ⟨2, 0⟩, ⟨0, 0⟩, ⟨1, -1⟩⟩
  , ⟨⟨-1, 1⟩, ⟨-2, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩⟩
  , ⟨⟨-1, 1⟩, ⟨-2, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩⟩
  , ⟨⟨-1, 1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-2, 0⟩⟩
  , ⟨⟨-1, 1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨2, 0⟩⟩
  , ⟨⟨-1, 1⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨-1, -1⟩⟩
  , ⟨⟨-1, 1⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨1, 1⟩⟩
  ]

def icosianChunk2 : List Q4 :=
  [ ⟨⟨-1, 1⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨-1, -1⟩⟩
  , ⟨⟨-1, 1⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨1, 1⟩⟩
  , ⟨⟨-1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨-2, 0⟩⟩
  , ⟨⟨-1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨2, 0⟩⟩
  , ⟨⟨-1, 1⟩, ⟨2, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩⟩
  , ⟨⟨-1, 1⟩, ⟨2, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩⟩
  , ⟨⟨0, 0⟩, ⟨-4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩
  , ⟨⟨0, 0⟩, ⟨-2, 0⟩, ⟨-1, 1⟩, ⟨-1, -1⟩⟩
  , ⟨⟨0, 0⟩, ⟨-2, 0⟩, ⟨-1, 1⟩, ⟨1, 1⟩⟩
  , ⟨⟨0, 0⟩, ⟨-2, 0⟩, ⟨1, -1⟩, ⟨-1, -1⟩⟩
  , ⟨⟨0, 0⟩, ⟨-2, 0⟩, ⟨1, -1⟩, ⟨1, 1⟩⟩
  , ⟨⟨0, 0⟩, ⟨-1, -1⟩, ⟨-2, 0⟩, ⟨-1, 1⟩⟩
  , ⟨⟨0, 0⟩, ⟨-1, -1⟩, ⟨-2, 0⟩, ⟨1, -1⟩⟩
  , ⟨⟨0, 0⟩, ⟨-1, -1⟩, ⟨2, 0⟩, ⟨-1, 1⟩⟩
  , ⟨⟨0, 0⟩, ⟨-1, -1⟩, ⟨2, 0⟩, ⟨1, -1⟩⟩
  , ⟨⟨0, 0⟩, ⟨-1, 1⟩, ⟨-1, -1⟩, ⟨-2, 0⟩⟩
  , ⟨⟨0, 0⟩, ⟨-1, 1⟩, ⟨-1, -1⟩, ⟨2, 0⟩⟩
  , ⟨⟨0, 0⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-2, 0⟩⟩
  , ⟨⟨0, 0⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨2, 0⟩⟩
  , ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨-4, 0⟩, ⟨0, 0⟩⟩
  ]

def icosianChunk3 : List Q4 :=
  [ ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-4, 0⟩⟩
  , ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨4, 0⟩⟩
  , ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨4, 0⟩, ⟨0, 0⟩⟩
  , ⟨⟨0, 0⟩, ⟨1, -1⟩, ⟨-1, -1⟩, ⟨-2, 0⟩⟩
  , ⟨⟨0, 0⟩, ⟨1, -1⟩, ⟨-1, -1⟩, ⟨2, 0⟩⟩
  , ⟨⟨0, 0⟩, ⟨1, -1⟩, ⟨1, 1⟩, ⟨-2, 0⟩⟩
  , ⟨⟨0, 0⟩, ⟨1, -1⟩, ⟨1, 1⟩, ⟨2, 0⟩⟩
  , ⟨⟨0, 0⟩, ⟨1, 1⟩, ⟨-2, 0⟩, ⟨-1, 1⟩⟩
  , ⟨⟨0, 0⟩, ⟨1, 1⟩, ⟨-2, 0⟩, ⟨1, -1⟩⟩
  , ⟨⟨0, 0⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨-1, 1⟩⟩
  , ⟨⟨0, 0⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨1, -1⟩⟩
  , ⟨⟨0, 0⟩, ⟨2, 0⟩, ⟨-1, 1⟩, ⟨-1, -1⟩⟩
  , ⟨⟨0, 0⟩, ⟨2, 0⟩, ⟨-1, 1⟩, ⟨1, 1⟩⟩
  , ⟨⟨0, 0⟩, ⟨2, 0⟩, ⟨1, -1⟩, ⟨-1, -1⟩⟩
  , ⟨⟨0, 0⟩, ⟨2, 0⟩, ⟨1, -1⟩, ⟨1, 1⟩⟩
  , ⟨⟨0, 0⟩, ⟨4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩
  , ⟨⟨1, -1⟩, ⟨-2, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩⟩
  , ⟨⟨1, -1⟩, ⟨-2, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩⟩
  , ⟨⟨1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-2, 0⟩⟩
  , ⟨⟨1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨2, 0⟩⟩
  ]

def icosianChunk4 : List Q4 :=
  [ ⟨⟨1, -1⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨-1, -1⟩⟩
  , ⟨⟨1, -1⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨1, 1⟩⟩
  , ⟨⟨1, -1⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨-1, -1⟩⟩
  , ⟨⟨1, -1⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨1, 1⟩⟩
  , ⟨⟨1, -1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨-2, 0⟩⟩
  , ⟨⟨1, -1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨2, 0⟩⟩
  , ⟨⟨1, -1⟩, ⟨2, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩⟩
  , ⟨⟨1, -1⟩, ⟨2, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩⟩
  , ⟨⟨1, 1⟩, ⟨-2, 0⟩, ⟨0, 0⟩, ⟨-1, 1⟩⟩
  , ⟨⟨1, 1⟩, ⟨-2, 0⟩, ⟨0, 0⟩, ⟨1, -1⟩⟩
  , ⟨⟨1, 1⟩, ⟨-1, 1⟩, ⟨-2, 0⟩, ⟨0, 0⟩⟩
  , ⟨⟨1, 1⟩, ⟨-1, 1⟩, ⟨2, 0⟩, ⟨0, 0⟩⟩
  , ⟨⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩, ⟨-2, 0⟩⟩
  , ⟨⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩, ⟨2, 0⟩⟩
  , ⟨⟨1, 1⟩, ⟨0, 0⟩, ⟨1, -1⟩, ⟨-2, 0⟩⟩
  , ⟨⟨1, 1⟩, ⟨0, 0⟩, ⟨1, -1⟩, ⟨2, 0⟩⟩
  , ⟨⟨1, 1⟩, ⟨1, -1⟩, ⟨-2, 0⟩, ⟨0, 0⟩⟩
  , ⟨⟨1, 1⟩, ⟨1, -1⟩, ⟨2, 0⟩, ⟨0, 0⟩⟩
  , ⟨⟨1, 1⟩, ⟨2, 0⟩, ⟨0, 0⟩, ⟨-1, 1⟩⟩
  , ⟨⟨1, 1⟩, ⟨2, 0⟩, ⟨0, 0⟩, ⟨1, -1⟩⟩
  ]

def icosianChunk5 : List Q4 :=
  [ ⟨⟨2, 0⟩, ⟨-2, 0⟩, ⟨-2, 0⟩, ⟨-2, 0⟩⟩
  , ⟨⟨2, 0⟩, ⟨-2, 0⟩, ⟨-2, 0⟩, ⟨2, 0⟩⟩
  , ⟨⟨2, 0⟩, ⟨-2, 0⟩, ⟨2, 0⟩, ⟨-2, 0⟩⟩
  , ⟨⟨2, 0⟩, ⟨-2, 0⟩, ⟨2, 0⟩, ⟨2, 0⟩⟩
  , ⟨⟨2, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩, ⟨0, 0⟩⟩
  , ⟨⟨2, 0⟩, ⟨-1, -1⟩, ⟨1, -1⟩, ⟨0, 0⟩⟩
  , ⟨⟨2, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩⟩
  , ⟨⟨2, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩⟩
  , ⟨⟨2, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩⟩
  , ⟨⟨2, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, -1⟩⟩
  , ⟨⟨2, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, 1⟩⟩
  , ⟨⟨2, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, -1⟩⟩
  , ⟨⟨2, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩⟩
  , ⟨⟨2, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩⟩
  , ⟨⟨2, 0⟩, ⟨1, 1⟩, ⟨-1, 1⟩, ⟨0, 0⟩⟩
  , ⟨⟨2, 0⟩, ⟨1, 1⟩, ⟨1, -1⟩, ⟨0, 0⟩⟩
  , ⟨⟨2, 0⟩, ⟨2, 0⟩, ⟨-2, 0⟩, ⟨-2, 0⟩⟩
  , ⟨⟨2, 0⟩, ⟨2, 0⟩, ⟨-2, 0⟩, ⟨2, 0⟩⟩
  , ⟨⟨2, 0⟩, ⟨2, 0⟩, ⟨2, 0⟩, ⟨-2, 0⟩⟩
  , ⟨⟨2, 0⟩, ⟨2, 0⟩, ⟨2, 0⟩, ⟨2, 0⟩⟩
  ]

def icosianList : List Q4 :=
  icosianChunk0 ++ icosianChunk1 ++ icosianChunk2 ++ icosianChunk3 ++ icosianChunk4 ++
    icosianChunk5

/-- The real quaternion of a scaled icosian: map the entries to `ℝ` and divide by `4`. -/
noncomputable def toQuat (p : Q4) : Quaternion ℝ :=
  ⟨zsqrt5ToReal p.a / 4, zsqrt5ToReal p.b / 4, zsqrt5ToReal p.c / 4, zsqrt5ToReal p.d / 4⟩

/-- The 120 icosians as real quaternions. -/
noncomputable def icosianSet : Set (Quaternion ℝ) := toQuat '' {p | p ∈ icosianList}

/-- The homogeneous rotation matrix of a quaternion over any commutative ring. -/
def rotH {R : Type*} [CommRing R] (q : Quaternion R) : Matrix (Fin 3) (Fin 3) R :=
  !![q.re * q.re + q.imI * q.imI - q.imJ * q.imJ - q.imK * q.imK,
      2 * (q.imI * q.imJ - q.re * q.imK), 2 * (q.imI * q.imK + q.re * q.imJ);
    2 * (q.imI * q.imJ + q.re * q.imK),
      q.re * q.re - q.imI * q.imI + q.imJ * q.imJ - q.imK * q.imK, 2 * (q.imJ * q.imK - q.re * q.imI);
    2 * (q.imI * q.imK - q.re * q.imJ), 2 * (q.imJ * q.imK + q.re * q.imI),
      q.re * q.re - q.imI * q.imI - q.imJ * q.imJ + q.imK * q.imK]

/-- The pure quaternion of a vector. -/
def pureQ {R : Type*} [CommRing R] (v : Fin 3 → R) : Quaternion R := ⟨0, v 0, v 1, v 2⟩

/-! ## Finite checks on the list -/

def one4 : Q4 := ⟨4, 0, 0, 0⟩
def negOne4 : Q4 := ⟨-4, 0, 0, 0⟩

theorem one4_mem : one4 ∈ icosianList ∧ negOne4 ∈ icosianList := by decide +kernel

theorem icosian_conj : ∀ p ∈ icosianList, p.conj ∈ icosianList ∧
    p.mul p.conj = one4.smul 4 ∧ p.conj.mul p = one4.smul 4 := by decide +kernel

theorem icosian_rot : ∀ p ∈ icosianList, ∃ A ∈ scaledRotationList, p.rot16 = A.smul 4 := by
  decide +kernel

theorem icosian_rot_surj : ∀ A ∈ scaledRotationList, ∃ p ∈ icosianList, p.rot16 = A.smul 4 := by
  decide +kernel

theorem icosian_rot_eq_one : ∀ p ∈ icosianList, p.rot16 = (M3.scal 4).smul 4 →
    p = one4 ∨ p = negOne4 := by decide +kernel

/-! ## Transfer to `ℍ[ℝ]` -/

theorem zsqrt5ToReal_four : zsqrt5ToReal 4 = 4 := map_ofNat zsqrt5ToReal 4

theorem zsqrt5ToReal_two : zsqrt5ToReal 2 = 2 := map_ofNat zsqrt5ToReal 2

theorem toQuat_injective : Function.Injective toQuat := by
  rintro ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩ h
  have h1 := congrArg QuaternionAlgebra.re h
  have h2 := congrArg QuaternionAlgebra.imI h
  have h3 := congrArg QuaternionAlgebra.imJ h
  have h4 := congrArg QuaternionAlgebra.imK h
  simp only [toQuat] at h1 h2 h3 h4
  have e1 := zsqrt5ToReal_injective (by linarith : zsqrt5ToReal a = zsqrt5ToReal a')
  have e2 := zsqrt5ToReal_injective (by linarith : zsqrt5ToReal b = zsqrt5ToReal b')
  have e3 := zsqrt5ToReal_injective (by linarith : zsqrt5ToReal c = zsqrt5ToReal c')
  have e4 := zsqrt5ToReal_injective (by linarith : zsqrt5ToReal d = zsqrt5ToReal d')
  subst e1 e2 e3 e4; rfl

theorem toQuat_mul_of {p q r : Q4} (h : p.mul q = r.smul 4) :
    toQuat p * toQuat q = toQuat r := by
  have ea := congrArg (fun x => zsqrt5ToReal x.a) h
  have eb := congrArg (fun x => zsqrt5ToReal x.b) h
  have ec := congrArg (fun x => zsqrt5ToReal x.c) h
  have ed := congrArg (fun x => zsqrt5ToReal x.d) h
  simp only [Q4.mul, Q4.smul, map_add, map_sub, map_mul, map_ofNat] at ea eb ec ed
  ext <;> simp only [toQuat, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
    Quaternion.imK_mul]
  · field_simp; linarith [ea]
  · field_simp; linarith [eb]
  · field_simp; linarith [ec]
  · field_simp; linarith [ed]

theorem toQuat_conj (p : Q4) : toQuat p.conj = star (toQuat p) := by
  ext <;> simp [toQuat, Q4.conj, neg_div]

theorem toQuat_one4 : toQuat one4 = 1 := by
  ext <;> simp [toQuat, one4, zsqrt5ToReal_four]

theorem toQuat_negOne4 : toQuat negOne4 = -1 := by
  ext <;> simp [toQuat, negOne4, zsqrt5ToReal_four]

theorem rotH_toQuat {p : Q4} {A : M3} (h : p.rot16 = A.smul 4) :
    rotH (toQuat p) = realQuarter A.toMatrix := by
  have e : ∀ i j, zsqrt5ToReal (p.rot16.toMatrix i j) = 4 * zsqrt5ToReal (A.toMatrix i j) := by
    intro i j
    rw [h]
    fin_cases i <;> fin_cases j <;> simp [M3.smul, M3.toMatrix, zsqrt5ToReal_four]
  ext i j
  have hij := e i j
  fin_cases i <;> fin_cases j <;>
    simp [rotH, toQuat, realQuarter, Q4.rot16, M3.toMatrix, zsqrt5ToReal_two] at hij ⊢ <;> field_simp at hij ⊢ <;> linarith [hij]

theorem realQuarter_scal_four : realQuarter (M3.scal 4).toMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [realQuarter, M3.scal, M3.toMatrix, zsqrt5ToReal_four]

theorem coe_eq_realQuarter_toM3 (g : icosahedralRotationGroup) :
    ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) =
      realQuarter (toM3 g).toMatrix :=
  coe_eq_realQuarter_repM3 g

theorem matrix_coe_injective :
    Function.Injective (fun g : icosahedralRotationGroup =>
      ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ)) := by
  intro g h hgh
  exact Subtype.ext (Subtype.ext hgh)

/-! ## The frozen statements -/

theorem rotH_mul {R : Type*} [CommRing R] (q r : Quaternion R) :
    rotH (q * r) = rotH q * rotH r := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotH, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem rotH_conj_action {R : Type*} [CommRing R] (q : Quaternion R) (v : Fin 3 → R) :
    q * pureQ v * star q = pureQ (rotH q *ᵥ v) := by
  ext <;> simp [pureQ, rotH, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

theorem icosianList_length : icosianList.length = 120 := rfl

theorem icosianList_nodup : icosianList.Nodup := by decide +kernel

/-! ### Closure, in twelve half-chunks -/

theorem icosian_closed_chunk0a : ∀ p ∈ icosianChunk0.take 10, ∀ q ∈ icosianList,
    ∃ r ∈ icosianList, p.mul q = r.smul 4 := by decide +kernel

theorem icosian_closed_chunk0b : ∀ p ∈ icosianChunk0.drop 10, ∀ q ∈ icosianList,
    ∃ r ∈ icosianList, p.mul q = r.smul 4 := by decide +kernel

theorem icosian_closed_chunk1a : ∀ p ∈ icosianChunk1.take 10, ∀ q ∈ icosianList,
    ∃ r ∈ icosianList, p.mul q = r.smul 4 := by decide +kernel

theorem icosian_closed_chunk1b : ∀ p ∈ icosianChunk1.drop 10, ∀ q ∈ icosianList,
    ∃ r ∈ icosianList, p.mul q = r.smul 4 := by decide +kernel

theorem icosian_closed_chunk2a : ∀ p ∈ icosianChunk2.take 10, ∀ q ∈ icosianList,
    ∃ r ∈ icosianList, p.mul q = r.smul 4 := by decide +kernel

theorem icosian_closed_chunk2b : ∀ p ∈ icosianChunk2.drop 10, ∀ q ∈ icosianList,
    ∃ r ∈ icosianList, p.mul q = r.smul 4 := by decide +kernel

theorem icosian_closed_chunk3a : ∀ p ∈ icosianChunk3.take 10, ∀ q ∈ icosianList,
    ∃ r ∈ icosianList, p.mul q = r.smul 4 := by decide +kernel

theorem icosian_closed_chunk3b : ∀ p ∈ icosianChunk3.drop 10, ∀ q ∈ icosianList,
    ∃ r ∈ icosianList, p.mul q = r.smul 4 := by decide +kernel

theorem icosian_closed_chunk4a : ∀ p ∈ icosianChunk4.take 10, ∀ q ∈ icosianList,
    ∃ r ∈ icosianList, p.mul q = r.smul 4 := by decide +kernel

theorem icosian_closed_chunk4b : ∀ p ∈ icosianChunk4.drop 10, ∀ q ∈ icosianList,
    ∃ r ∈ icosianList, p.mul q = r.smul 4 := by decide +kernel

theorem icosian_closed_chunk5a : ∀ p ∈ icosianChunk5.take 10, ∀ q ∈ icosianList,
    ∃ r ∈ icosianList, p.mul q = r.smul 4 := by decide +kernel

theorem icosian_closed_chunk5b : ∀ p ∈ icosianChunk5.drop 10, ∀ q ∈ icosianList,
    ∃ r ∈ icosianList, p.mul q = r.smul 4 := by decide +kernel

theorem icosian_closed_chunk0 : ∀ p ∈ icosianChunk0, ∀ q ∈ icosianList,
    ∃ r ∈ icosianList, p.mul q = r.smul 4 := by
  intro p hp
  rw [← List.take_append_drop 10 icosianChunk0, List.mem_append] at hp
  rcases hp with h | h
  · exact icosian_closed_chunk0a p h
  · exact icosian_closed_chunk0b p h

theorem icosian_closed_chunk1 : ∀ p ∈ icosianChunk1, ∀ q ∈ icosianList,
    ∃ r ∈ icosianList, p.mul q = r.smul 4 := by
  intro p hp
  rw [← List.take_append_drop 10 icosianChunk1, List.mem_append] at hp
  rcases hp with h | h
  · exact icosian_closed_chunk1a p h
  · exact icosian_closed_chunk1b p h

theorem icosian_closed_chunk2 : ∀ p ∈ icosianChunk2, ∀ q ∈ icosianList,
    ∃ r ∈ icosianList, p.mul q = r.smul 4 := by
  intro p hp
  rw [← List.take_append_drop 10 icosianChunk2, List.mem_append] at hp
  rcases hp with h | h
  · exact icosian_closed_chunk2a p h
  · exact icosian_closed_chunk2b p h

theorem icosian_closed_chunk3 : ∀ p ∈ icosianChunk3, ∀ q ∈ icosianList,
    ∃ r ∈ icosianList, p.mul q = r.smul 4 := by
  intro p hp
  rw [← List.take_append_drop 10 icosianChunk3, List.mem_append] at hp
  rcases hp with h | h
  · exact icosian_closed_chunk3a p h
  · exact icosian_closed_chunk3b p h

theorem icosian_closed_chunk4 : ∀ p ∈ icosianChunk4, ∀ q ∈ icosianList,
    ∃ r ∈ icosianList, p.mul q = r.smul 4 := by
  intro p hp
  rw [← List.take_append_drop 10 icosianChunk4, List.mem_append] at hp
  rcases hp with h | h
  · exact icosian_closed_chunk4a p h
  · exact icosian_closed_chunk4b p h

theorem icosian_closed_chunk5 : ∀ p ∈ icosianChunk5, ∀ q ∈ icosianList,
    ∃ r ∈ icosianList, p.mul q = r.smul 4 := by
  intro p hp
  rw [← List.take_append_drop 10 icosianChunk5, List.mem_append] at hp
  rcases hp with h | h
  · exact icosian_closed_chunk5a p h
  · exact icosian_closed_chunk5b p h

theorem icosian_closed : ∀ p ∈ icosianList, ∀ q ∈ icosianList,
    ∃ r ∈ icosianList, p.mul q = r.smul 4 := by
  intro p hp
  simp only [icosianList, List.mem_append] at hp
  rcases hp with ((((h | h) | h) | h) | h) | h
  · exact icosian_closed_chunk0 p h
  · exact icosian_closed_chunk1 p h
  · exact icosian_closed_chunk2 p h
  · exact icosian_closed_chunk3 p h
  · exact icosian_closed_chunk4 p h
  · exact icosian_closed_chunk5 p h

theorem icosianSet_ncard : icosianSet.ncard = 120 := by
  rw [icosianSet, Set.ncard_image_of_injective _ toQuat_injective]
  have h : {p | p ∈ icosianList} = (icosianList.toFinset : Set Q4) := by ext; simp
  rw [h, Set.ncard_coe_finset, List.toFinset_card_of_nodup icosianList_nodup, icosianList_length]

theorem icosianSet_mul_mem : ∀ x ∈ icosianSet, ∀ y ∈ icosianSet, x * y ∈ icosianSet := by
  rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
  obtain ⟨r, hr, h⟩ := icosian_closed p hp q hq
  exact ⟨r, hr, (toQuat_mul_of h).symm⟩

theorem icosianSet_mul_star : ∀ x ∈ icosianSet, x * star x = 1 ∧ star x * x = 1 := by
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨-, h1, h2⟩ := icosian_conj p hp
  have e1 := toQuat_mul_of h1
  have e2 := toQuat_mul_of h2
  rw [toQuat_conj, toQuat_one4] at e1 e2
  exact ⟨e1, e2⟩

theorem icosianSet_star_mem : ∀ x ∈ icosianSet, star x ∈ icosianSet := by
  rintro _ ⟨p, hp, rfl⟩
  exact ⟨p.conj, (icosian_conj p hp).1, toQuat_conj p⟩

theorem icosianSet_one_mem : (1 : Quaternion ℝ) ∈ icosianSet ∧ (-1 : Quaternion ℝ) ∈ icosianSet :=
  ⟨⟨one4, one4_mem.1, toQuat_one4⟩, ⟨negOne4, one4_mem.2, toQuat_negOne4⟩⟩

noncomputable def binaryIcosahedralGroup : Subgroup (Quaternion ℝ)ˣ where
  carrier := {u | (u : Quaternion ℝ) ∈ icosianSet}
  one_mem' := by
    show ((1 : (Quaternion ℝ)ˣ) : Quaternion ℝ) ∈ icosianSet
    rw [Units.val_one]; exact icosianSet_one_mem.1
  mul_mem' := by
    intro u v hu hv
    show ((u * v : (Quaternion ℝ)ˣ) : Quaternion ℝ) ∈ icosianSet
    rw [Units.val_mul]; exact icosianSet_mul_mem _ hu _ hv
  inv_mem' := by
    intro u hu
    show ((u⁻¹ : (Quaternion ℝ)ˣ) : Quaternion ℝ) ∈ icosianSet
    rw [Units.inv_eq_of_mul_eq_one_right (icosianSet_mul_star _ hu).1]
    exact icosianSet_star_mem _ hu

theorem mem_binaryIcosahedralGroup (u : (Quaternion ℝ)ˣ) :
    u ∈ binaryIcosahedralGroup ↔ (u : Quaternion ℝ) ∈ icosianSet := Iff.rfl

/-- The unit of a member of `icosianSet`. -/
noncomputable def icosianUnit {x : Quaternion ℝ} (hx : x ∈ icosianSet) : binaryIcosahedralGroup :=
  ⟨⟨x, star x, (icosianSet_mul_star x hx).1, (icosianSet_mul_star x hx).2⟩, hx⟩

theorem icosianUnit_coe {x : Quaternion ℝ} (hx : x ∈ icosianSet) :
    (((icosianUnit hx : binaryIcosahedralGroup) : (Quaternion ℝ)ˣ) : Quaternion ℝ) = x := rfl

theorem binaryIcosahedralGroup_natCard : Nat.card binaryIcosahedralGroup = 120 := by
  let φ : binaryIcosahedralGroup → icosianSet := fun u => ⟨((u : (Quaternion ℝ)ˣ) : Quaternion ℝ), u.2⟩
  have hφ : Function.Bijective φ := by
    constructor
    · intro u v h
      exact Subtype.ext (Units.ext (congrArg Subtype.val h))
    · rintro ⟨x, hx⟩
      exact ⟨icosianUnit hx, rfl⟩
  rw [Nat.card_eq_of_bijective φ hφ, Nat.card_coe_set_eq, icosianSet_ncard]

theorem rotH_icosian_mem : ∀ u : binaryIcosahedralGroup, ∃ g : icosahedralRotationGroup,
    ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) =
      rotH ((u : (Quaternion ℝ)ˣ) : Quaternion ℝ) := by
  intro u
  obtain ⟨p, hp, hpu⟩ := u.2
  obtain ⟨A, hA, h⟩ := icosian_rot p hp
  obtain ⟨g, hg⟩ := toM3_surj A hA
  refine ⟨g, ?_⟩
  rw [← hpu, rotH_toQuat h, coe_eq_realQuarter_toM3, hg]

noncomputable def icosianRotHom : binaryIcosahedralGroup →* icosahedralRotationGroup :=
  MonoidHom.mk' (fun u => Classical.choose (rotH_icosian_mem u)) (by
    intro u v
    apply matrix_coe_injective
    show (((Classical.choose (rotH_icosian_mem (u * v)) : icosahedralRotationGroup) :
        specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) =
      (((Classical.choose (rotH_icosian_mem u) : icosahedralRotationGroup) :
        specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *
      (((Classical.choose (rotH_icosian_mem v) : icosahedralRotationGroup) :
        specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ)
    rw [Classical.choose_spec (rotH_icosian_mem (u * v)), Classical.choose_spec (rotH_icosian_mem u),
      Classical.choose_spec (rotH_icosian_mem v), Subgroup.coe_mul, Units.val_mul, rotH_mul])

theorem icosianRotHom_spec (u : binaryIcosahedralGroup) :
    (((icosianRotHom u : icosahedralRotationGroup) : specialOrthogonalGroup (Fin 3) ℝ) :
      Matrix (Fin 3) (Fin 3) ℝ) = rotH ((u : (Quaternion ℝ)ˣ) : Quaternion ℝ) :=
  Classical.choose_spec (rotH_icosian_mem u)

theorem icosianRotHom_conj_action (u : binaryIcosahedralGroup) (v : Fin 3 → ℝ) :
    ((u : (Quaternion ℝ)ˣ) : Quaternion ℝ) * pureQ v * star ((u : (Quaternion ℝ)ˣ) : Quaternion ℝ) =
      pureQ ((((icosianRotHom u : icosahedralRotationGroup) : specialOrthogonalGroup (Fin 3) ℝ) :
        Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v) := by
  rw [icosianRotHom_spec, rotH_conj_action]

theorem icosianRotHom_surjective : Function.Surjective icosianRotHom := by
  intro g
  obtain ⟨p, hp, h⟩ := icosian_rot_surj (toM3 g) (toM3_mem g)
  have hx : toQuat p ∈ icosianSet := ⟨p, hp, rfl⟩
  refine ⟨icosianUnit hx, matrix_coe_injective ?_⟩
  show (((icosianRotHom (icosianUnit hx) : icosahedralRotationGroup) :
    specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) = _
  rw [icosianRotHom_spec, icosianUnit_coe, rotH_toQuat h]
  exact (coe_eq_realQuarter_toM3 g).symm

theorem rotH_one_real : rotH (1 : Quaternion ℝ) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rotH]

theorem rotH_neg_one_real : rotH (-1 : Quaternion ℝ) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rotH]

theorem icosianRotHom_eq_one_iff (u : binaryIcosahedralGroup) :
    icosianRotHom u = 1 ↔
      (((u : (Quaternion ℝ)ˣ) : Quaternion ℝ) = 1 ∨ ((u : (Quaternion ℝ)ˣ) : Quaternion ℝ) = -1) := by
  have key : icosianRotHom u = 1 ↔ rotH ((u : (Quaternion ℝ)ˣ) : Quaternion ℝ) = 1 := by
    rw [← icosianRotHom_spec]
    constructor
    · intro h; rw [h]; rfl
    · intro h; apply matrix_coe_injective; exact h
  rw [key]
  constructor
  · intro h
    obtain ⟨p, hp, hpu⟩ := u.2
    obtain ⟨A, hA, hpA⟩ := icosian_rot p hp
    rw [← hpu, rotH_toQuat hpA, ← realQuarter_scal_four] at h
    have hA1 : A = M3.scal 4 := M3.toMatrix_injective (realQuarter_injective h)
    subst hA1
    rcases icosian_rot_eq_one p hp hpA with rfl | rfl
    · left; rw [← hpu, toQuat_one4]
    · right; rw [← hpu, toQuat_negOne4]
  · rintro (h | h) <;> rw [h]
    · exact rotH_one_real
    · exact rotH_neg_one_real

/-- `-1` as an element of the group. -/
noncomputable def negOneBI : binaryIcosahedralGroup := icosianUnit icosianSet_one_mem.2

theorem icosianRotHom_ker_natCard : Nat.card icosianRotHom.ker = 2 := by
  have hset : (icosianRotHom.ker : Set binaryIcosahedralGroup) = {1, negOneBI} := by
    ext u
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, icosianRotHom_eq_one_iff, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro (h | h)
      · left; exact Subtype.ext (Units.ext h)
      · right; exact Subtype.ext (Units.ext h)
    · rintro (rfl | rfl)
      · left; rfl
      · right; rfl
  have hne : (1 : binaryIcosahedralGroup) ≠ negOneBI := by
    intro h
    have h1 := congrArg (fun u : binaryIcosahedralGroup => ((u : (Quaternion ℝ)ˣ) : Quaternion ℝ)) h
    have h2 := congrArg QuaternionAlgebra.re h1
    simp [negOneBI, icosianUnit_coe] at h2
    norm_num at h2
  show Nat.card ((icosianRotHom.ker : Set binaryIcosahedralGroup)) = 2
  rw [Nat.card_coe_set_eq, hset, Set.ncard_pair hne]

theorem binaryIcosahedral_quotient_iso :
    Nonempty (binaryIcosahedralGroup ⧸ icosianRotHom.ker ≃* icosahedralRotationGroup) :=
  ⟨QuotientGroup.quotientKerEquivOfSurjective icosianRotHom icosianRotHom_surjective⟩

#print axioms rotH_mul
#print axioms rotH_conj_action
#print axioms icosianList_length
#print axioms icosianList_nodup
#print axioms icosian_closed
#print axioms icosianSet_ncard
#print axioms icosianSet_mul_mem
#print axioms icosianSet_mul_star
#print axioms icosianSet_star_mem
#print axioms icosianSet_one_mem
#print axioms binaryIcosahedralGroup
#print axioms binaryIcosahedralGroup_natCard
#print axioms rotH_icosian_mem
#print axioms icosianRotHom
#print axioms icosianRotHom_spec
#print axioms icosianRotHom_conj_action
#print axioms icosianRotHom_surjective
#print axioms icosianRotHom_eq_one_iff
#print axioms icosianRotHom_ker_natCard
#print axioms binaryIcosahedral_quotient_iso
