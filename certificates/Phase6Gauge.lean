/-
Phase VI: finite algebraic identities behind Theorems G2 (corner factorization) and F' (forced flux) of
deliverables/PHASE6_GAUGE_QM_AUDIT.md, checked by the Lean kernel with `decide` (core Lean 4, no Mathlib).
Only these finite identities are formalized; the graph-theoretic statements built on them are proved on paper.

1. `corner_identity`        for orthogonal signed coordinate axes u ⊥ v:  (σ·u)(σ·v) = i σ·(u × v)
                            (the "turning factor" of the Clifford face-normal connection is a unit quaternion of trace 0).
2. `straight_identity`      (σ·u)(σ·u) = 1  (no turn, no holonomy contribution).
3. `two_cycle_classes`      for signed axes u, v:  (σ·u)(σ·v) = 1 iff u = v;  = -1 iff u = -v;  trace 0 iff u ⊥ v.
                            This is the holonomy class of the 2-cycle formed by two parallel panels (Lemma F'.1):
                            W ~ (σ·M_bᵀe_m)(σ·M_aᵀe_m).
-/
namespace Phase6Gauge

structure GI where
  re : Int
  im : Int
  deriving DecidableEq, Repr
def GI.add (x y : GI) : GI := ⟨x.re + y.re, x.im + y.im⟩
def GI.mul (x y : GI) : GI := ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re⟩
def GI.neg (x : GI) : GI := ⟨-x.re, -x.im⟩

structure M2 where
  a : GI
  b : GI
  c : GI
  d : GI
  deriving DecidableEq, Repr
def M2.mul (x y : M2) : M2 :=
  ⟨(x.a.mul y.a).add (x.b.mul y.c), (x.a.mul y.b).add (x.b.mul y.d),
   (x.c.mul y.a).add (x.d.mul y.c), (x.c.mul y.b).add (x.d.mul y.d)⟩
def M2.neg (x : M2) : M2 := ⟨x.a.neg, x.b.neg, x.c.neg, x.d.neg⟩
def M2.trace (x : M2) : GI := x.a.add x.d

def z : GI := ⟨0, 0⟩
def o : GI := ⟨1, 0⟩
def i : GI := ⟨0, 1⟩
def one : M2 := ⟨o, z, z, o⟩
def zeroM : M2 := ⟨z, z, z, z⟩
def s1 : M2 := ⟨z, o, o, z⟩
def s2 : M2 := ⟨z, i.neg, i, z⟩
def s3 : M2 := ⟨o, z, z, o.neg⟩
def isg (s : M2) : M2 := ⟨i.mul s.a, i.mul s.b, i.mul s.c, i.mul s.d⟩

/-- signed axis = (axis index 0..2, sign) ; as an integer vector -/
def vec (u : Nat × Bool) : Int × Int × Int :=
  let sg : Int := if u.2 then 1 else -1
  if u.1 = 0 then (sg, 0, 0) else if u.1 = 1 then (0, sg, 0) else (0, 0, sg)
/-- σ·w for an integer vector w (here always a signed axis or zero) -/
def sdot (w : Int × Int × Int) : M2 :=
  let sc := fun (k : Int) (m : M2) => (⟨⟨k * m.a.re, k * m.a.im⟩, ⟨k * m.b.re, k * m.b.im⟩, ⟨k * m.c.re, k * m.c.im⟩, ⟨k * m.d.re, k * m.d.im⟩⟩ : M2)
  let add := fun (x y : M2) => (⟨x.a.add y.a, x.b.add y.b, x.c.add y.c, x.d.add y.d⟩ : M2)
  add (add (sc w.1 s1) (sc w.2.1 s2)) (sc w.2.2 s3)
def cross (u v : Int × Int × Int) : Int × Int × Int :=
  (u.2.1 * v.2.2 - u.2.2 * v.2.1, u.2.2 * v.1 - u.1 * v.2.2, u.1 * v.2.1 - u.2.1 * v.1)
def dot (u v : Int × Int × Int) : Int := u.1 * v.1 + u.2.1 * v.2.1 + u.2.2 * v.2.2
def negv (u : Int × Int × Int) : Int × Int × Int := (-u.1, -u.2.1, -u.2.2)

def signedAxes : List (Nat × Bool) := [(0, true), (0, false), (1, true), (1, false), (2, true), (2, false)]

theorem straight_identity : ∀ u ∈ signedAxes, (sdot (vec u)).mul (sdot (vec u)) = one := by decide

theorem corner_identity :
    ∀ u ∈ signedAxes, ∀ v ∈ signedAxes, dot (vec u) (vec v) = 0 →
      (sdot (vec u)).mul (sdot (vec v)) = isg (sdot (cross (vec u) (vec v))) := by decide

theorem two_cycle_classes :
    ∀ u ∈ signedAxes, ∀ v ∈ signedAxes,
      ((sdot (vec u)).mul (sdot (vec v)) = one ↔ vec u = vec v) ∧
      ((sdot (vec u)).mul (sdot (vec v)) = one.neg ↔ vec u = negv (vec v)) ∧
      (dot (vec u) (vec v) = 0 → ((sdot (vec u)).mul (sdot (vec v))).trace = z) := by decide

#print axioms straight_identity
#print axioms corner_identity
#print axioms two_cycle_classes

end Phase6Gauge
