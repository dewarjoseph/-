/-
Phase VII: the finite combinatorics behind the strengthened forced-flux theorem of deliverables/PHASE7_REPORT.md (II.1),
checked by the Lean kernel with `decide` (core Lean 4, no Mathlib, no axioms beyond the kernel's).

Setting (proved on paper in the report).  In parent coordinates the level-1 supertile consists of the centre chair (sign
vector (+,+,+)) and seven octant chairs with sign vectors s(v) = 1 - 2v, v ∈ {0,1}³ \ {(1,1,1)}.  A geometry-compatible
frame is M = D_s P(π) with π any of the 6 permutations (proper iff det M = Π s · sgn π = 1).  The level-1 incidence
structure contains exactly 21 two-cycles: centre against each octant, one for each third axis m ∈ {0,1,2}.  The two-cycle
centre →(k) octant →(l) centre with third axis m has holonomy W = 1 iff
    π_c⁻¹(m) = π_v⁻¹(m)   and   det M_c · det M_v · s_c(m) · s_v(m) = 1          (Lemma F'.1 with the det factors).

Certified here:
1. `octant_bound`      for every centre permutation, octant permutation and admissible octant sign vector, the number of
                       trivial two-cycles of that octant is ≤ 3 if s = (+,+,+) and ≤ 1 otherwise
                       (two permutations of three letters that agree at two points agree everywhere).
2. `total_bound`       summed over the seven octants the bounds give 9, so ≥ 12 of the 21 two-cycles are non-trivial for
                       EVERY compatible frame field, proper or improper.
3. `bound_attained`    some frame choice has exactly 9 trivial two-cycles (the bound 12 is sharp; exhaustive search agrees).
4. `forced_proper`     for proper frames the 9 two-cycles with s_v(m) = -1 are never trivial (Phase VI, Theorem F').
5. `forced_fails_improper`   that list is not forced for improper frames (explicit counterexample).
-/
namespace Phase7Counting

/-- the six permutations of {0,1,2}, as [π 0, π 1, π 2] -/
def perms : List (List Nat) := [[0,1,2], [0,2,1], [1,0,2], [1,2,0], [2,0,1], [2,1,0]]

def sgn (p : List Nat) : Int :=
  if p == [0,1,2] || p == [1,2,0] || p == [2,0,1] then 1 else -1

/-- π⁻¹(m): the position at which p takes the value m -/
def inv (p : List Nat) (m : Nat) : Nat :=
  if p.getD 0 9 == m then 0 else if p.getD 1 9 == m then 1 else 2

/-- admissible octant sign vectors s(v) = 1 - 2v for the seven octants v ≠ (1,1,1) -/
def octantSigns : List (List Int) :=
  [[1,1,1], [1,1,-1], [1,-1,1], [1,-1,-1], [-1,1,1], [-1,1,-1], [-1,-1,1]]

def prod3 (s : List Int) : Int := s.getD 0 0 * s.getD 1 0 * s.getD 2 0

/-- det of the centre frame P(π_c) and of the octant frame D_s P(π_v) -/
def detC (pc : List Nat) : Int := sgn pc
def detV (s : List Int) (pv : List Nat) : Int := prod3 s * sgn pv

/-- the two-cycle with third axis m between the centre (sign +) and an octant with sign vector s is trivial -/
def trivial (pc pv : List Nat) (s : List Int) (m : Nat) : Bool :=
  inv pc m == inv pv m && detC pc * detV s pv * s.getD m 0 == 1

def countTriv (pc pv : List Nat) (s : List Int) : Nat :=
  ([0,1,2].filter (fun m => trivial pc pv s m)).length

def bound (s : List Int) : Nat := if s == [1,1,1] then 3 else 1

theorem octant_bound :
    perms.all (fun pc => perms.all (fun pv => octantSigns.all (fun s => decide (countTriv pc pv s ≤ bound s)))) = true := by
  decide

theorem total_bound : (octantSigns.map bound).foldl (· + ·) 0 = 9 := by decide

theorem bound_attained :
    perms.any (fun pc => octantSigns.all (fun s => perms.any (fun pv => countTriv pc pv s == bound s))) = true := by
  decide

theorem forced_proper :
    perms.all (fun pc => perms.all (fun pv => octantSigns.all (fun s =>
      !(detC pc == 1 && detV s pv == 1) ||
      [0,1,2].all (fun m => !(s.getD m 0 == -1) || !trivial pc pv s m)))) = true := by
  decide

/-- number of (octant, axis) pairs with s_v(m) = -1: the Phase VI list -/
theorem forced_count : (octantSigns.map (fun s => ([0,1,2].filter (fun m => s.getD m 0 == -1)).length)).foldl (· + ·) 0 = 9 := by
  decide

theorem forced_fails_improper : trivial [0,1,2] [0,1,2] [-1,1,1] 0 = true ∧ detV [-1,1,1] [0,1,2] = -1 := by decide

end Phase7Counting

#print axioms Phase7Counting.octant_bound
#print axioms Phase7Counting.total_bound
#print axioms Phase7Counting.bound_attained
#print axioms Phase7Counting.forced_proper
#print axioms Phase7Counting.forced_fails_improper
