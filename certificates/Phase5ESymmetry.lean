/-
Phase V-E: finite algebraic facts used by the theorems of deliverables/PHASE5E_THEORETICAL_CONJECTURE.md, checked by the
Lean kernel with `decide` (core Lean 4, no Mathlib).  What is proved here is exactly the stated finite identities; the
analytic theorems (Schur/inertia, Ritz bounds) are proved on paper in the report and are NOT formalized here.

1. `kramers_commutes`   every element q of Q8 = {±1, ±iσ₁, ±iσ₂, ±iσ₃} satisfies J q̄ = q J with J = iσ_y; hence the
                        antiunitary T = (1 ⊗ iσ_y)K commutes with every 2x2 block -C_ab and with the diagonal of H (Kramers).
2. `axis_factor_hermitian_unitary`   for every signed coordinate axis u, σ·u is Hermitian and squares to 1, so the link
                        C_ab = (σ·M_aᵀn)(σ·M_bᵀn) equals u_a u_b† : the connection is pure gauge along each single axis.
3. `link_in_Q8`         every product of two signed-axis Pauli matrices lies in Q8; since M_aᵀn is a signed axis for every
                        frame M_a ∈ SO(3,ℤ), every link C_ab lies in Q8.
4. `chair_axis_permutation_invariant`   the chair {0,1}³ \ {(1,1,1)} is invariant under all 6 axis permutations; this is
                        the step of Proposition E0 showing that the 3 admissible permutations of each parity (a coset of the
                        rotation group of the chair's axis permutations) give the same cube set at every depth.
-/
namespace Phase5ESymmetry

/-- Gaussian integer a + b i. -/
structure GI where
  re : Int
  im : Int
  deriving DecidableEq, Repr

def GI.add (x y : GI) : GI := ⟨x.re + y.re, x.im + y.im⟩
def GI.mul (x y : GI) : GI := ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re⟩
def GI.conj (x : GI) : GI := ⟨x.re, -x.im⟩
def GI.neg (x : GI) : GI := ⟨-x.re, -x.im⟩

/-- 2x2 Gaussian-integer matrix [[a, b], [c, d]]. -/
structure M2 where
  a : GI
  b : GI
  c : GI
  d : GI
  deriving DecidableEq, Repr

def M2.mul (x y : M2) : M2 :=
  ⟨(x.a.mul y.a).add (x.b.mul y.c), (x.a.mul y.b).add (x.b.mul y.d),
   (x.c.mul y.a).add (x.d.mul y.c), (x.c.mul y.b).add (x.d.mul y.d)⟩
def M2.conj (x : M2) : M2 := ⟨x.a.conj, x.b.conj, x.c.conj, x.d.conj⟩
def M2.adj (x : M2) : M2 := ⟨x.a.conj, x.c.conj, x.b.conj, x.d.conj⟩
def M2.neg (x : M2) : M2 := ⟨x.a.neg, x.b.neg, x.c.neg, x.d.neg⟩

def z : GI := ⟨0, 0⟩
def o : GI := ⟨1, 0⟩
def i : GI := ⟨0, 1⟩
def one : M2 := ⟨o, z, z, o⟩
def s1 : M2 := ⟨z, o, o, z⟩                 -- σ₁
def s2 : M2 := ⟨z, i.neg, i, z⟩             -- σ₂
def s3 : M2 := ⟨o, z, z, o.neg⟩             -- σ₃
def isg (s : M2) : M2 := ⟨i.mul s.a, i.mul s.b, i.mul s.c, i.mul s.d⟩   -- i σ
def J : M2 := ⟨z, o, o.neg, z⟩              -- i σ_y

def Q8 : List M2 := [one, one.neg, isg s1, (isg s1).neg, isg s2, (isg s2).neg, isg s3, (isg s3).neg]

theorem kramers_commutes : ∀ q ∈ Q8, J.mul q.conj = q.mul J := by decide

/-- σ·u for a signed coordinate axis u = sgn · e_k (k = 0, 1, 2). -/
def sigmaAxis (k : Nat) (sgn : Bool) : M2 :=
  let s := if k = 0 then s1 else if k = 1 then s2 else s3
  if sgn then s else s.neg

def signedAxes : List (Nat × Bool) := [(0, true), (0, false), (1, true), (1, false), (2, true), (2, false)]

theorem axis_factor_hermitian_unitary :
    ∀ u ∈ signedAxes, (sigmaAxis u.1 u.2).adj = sigmaAxis u.1 u.2 ∧ (sigmaAxis u.1 u.2).mul (sigmaAxis u.1 u.2) = one := by decide

/-- For any frame M in SO(3,Z) (a signed permutation matrix) and any coordinate axis n, M^T n is a signed coordinate axis,
so sigma.M_a^T n and sigma.M_b^T n each range over the six `sigmaAxis` matrices; the link is their product. -/
theorem link_in_Q8 :
    ∀ u ∈ signedAxes, ∀ v ∈ signedAxes, (sigmaAxis u.1 u.2).mul (sigmaAxis v.1 v.2) ∈ Q8 := by decide

def perms : List (Nat × Nat × Nat) := [(0,1,2), (1,2,0), (2,0,1), (0,2,1), (2,1,0), (1,0,2)]
def permAt (p : Nat × Nat × Nat) (j : Nat) : Nat := if j = 0 then p.1 else if j = 1 then p.2.1 else p.2.2

/-- the chair: octants {0,1}³ minus (1,1,1) -/
def chair : List (Nat × Nat × Nat) := [(0,0,0), (0,0,1), (0,1,0), (0,1,1), (1,0,0), (1,0,1), (1,1,0)]
def applyPerm (p : Nat × Nat × Nat) (v : Nat × Nat × Nat) : Nat × Nat × Nat :=
  let c := fun j => if j = 0 then v.1 else if j = 1 then v.2.1 else v.2.2
  (c (permAt p 0), c (permAt p 1), c (permAt p 2))

theorem chair_axis_permutation_invariant :
    ∀ p ∈ perms, (∀ v ∈ chair, applyPerm p v ∈ chair) ∧ (chair.map (applyPerm p)).length = chair.length := by decide

#print axioms kramers_commutes
#print axioms axis_factor_hermitian_unitary
#print axioms link_in_Q8
#print axioms chair_axis_permutation_invariant

end Phase5ESymmetry
