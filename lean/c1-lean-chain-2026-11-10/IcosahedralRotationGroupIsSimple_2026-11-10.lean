/-
Scratch file, dated 2026-11-10.
Not a Lake target. Not peer reviewed.

This file imports `IcosahedralRotationGroupIsoAlternatingFive_v2_2026-11-10`,
which reaches the official module `IcosahedralRotationGroup_2026-11-09`
through `IcosahedralRotationGroupImportedMulEquiv_2026-11-10`. No text
from those modules is copied here.
-/

import «IcosahedralRotationGroupIsoAlternatingFive_v2_2026-11-10»
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-- C1 as a Lean statement: the imported official icosahedral rotation group is a simple
group. Transported from Mathlib's `alternatingGroup.isSimpleGroup` (for `Fin 5`) along
`icosahedralRotationGroupMulEquivAlternatingGroup`. -/
theorem icosahedralRotationGroup_isSimpleGroup : IsSimpleGroup icosahedralRotationGroup :=
  (icosahedralRotationGroupMulEquivAlternatingGroup.isSimpleGroup_congr).mpr
    (alternatingGroup.isSimpleGroup (by simp))

#print axioms icosahedralRotationGroup_isSimpleGroup
