/-
Phase VIII: the finite group facts behind the Abelian "shadow" controls of deliverables/PHASE8_REPORT.md (sections 6, 8),
checked by the Lean kernel with `decide` (core Lean 4, no Mathlib).

Q8 = {±1, ±q1, ±q2, ±q3}, encoded as (unit, sign) with unit 0 = 1, 1 = q1, 2 = q2, 3 = q3 and sign true = minus.
Hamilton relations: q_k^2 = -1, q1 q2 = q3, q2 q3 = q1, q3 q1 = q2, and the reversed products carry a minus sign.
(The Python table phase7_adversarial.MUL uses index 2*unit + sign; tests/test_phase8.py checks that both tables agree.)

1. `chi_hom`      for k = 1, 2, 3, chi_k(x) = +1 if x is in <q_k> = {±1, ±q_k}, else -1, is a homomorphism Q8 -> {±1}.
2. `chi_kernel`   the kernel of chi_k is exactly {±1, ±q_k} (4 elements), so the three shadows are the three non-trivial
                  characters of Q8 / {±1} = Z2 x Z2.
3. `shadow_class` chi_k sends -1 to +1: the shadow of the central element is trivial, so a -1 plaquette becomes trivial and
                  a traceless plaquette (±q_j) becomes -1 exactly when j ≠ k.
-/
namespace Phase8Shadows

def umul : Nat → Nat → Nat × Bool
  | 0, b => (b, false)
  | a, 0 => (a, false)
  | 1, 1 => (0, true)
  | 2, 2 => (0, true)
  | 3, 3 => (0, true)
  | 1, 2 => (3, false)
  | 2, 3 => (1, false)
  | 3, 1 => (2, false)
  | 2, 1 => (3, true)
  | 3, 2 => (1, true)
  | 1, 3 => (2, true)
  | _, _ => (0, false)

def mul (x y : Nat × Bool) : Nat × Bool :=
  let r := umul x.1 y.1
  (r.1, xor (xor x.2 y.2) r.2)

def chi (k : Nat) (x : Nat × Bool) : Int := if x.1 == 0 || x.1 == k then 1 else -1

def elems : List (Nat × Bool) :=
  [(0, false), (0, true), (1, false), (1, true), (2, false), (2, true), (3, false), (3, true)]

theorem assoc : elems.all (fun a => elems.all (fun b => elems.all (fun c => mul (mul a b) c == mul a (mul b c)))) = true := by
  decide

theorem chi_hom :
    [1, 2, 3].all (fun k => elems.all (fun a => elems.all (fun b => chi k (mul a b) == chi k a * chi k b))) = true := by
  decide

theorem chi_kernel :
    [1, 2, 3].all (fun k => (elems.filter (fun a => chi k a == 1)).length == 4 &&
      elems.all (fun a => chi k a != 1 || a.1 == 0 || a.1 == k)) = true := by
  decide

theorem shadow_class : [1, 2, 3].all (fun k => chi k (0, true) == 1) = true := by decide

end Phase8Shadows

#print axioms Phase8Shadows.assoc
#print axioms Phase8Shadows.chi_hom
#print axioms Phase8Shadows.chi_kernel
#print axioms Phase8Shadows.shadow_class
