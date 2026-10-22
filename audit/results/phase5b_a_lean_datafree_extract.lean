-- Phase V-B / A: data-free extract of certificates/TypeSubstitutionCertificate.lean (sha256 f8f89bb...0de68):
-- lines 40-79 (V3/M3 arithmetic), 181-195 and 205-222 (Q8 section without the Owner-dependent linkCubes/plaqHol), 576-705 (general closed-form theorem). No certificate data.
namespace TypeSubstitution

/-! ### Integer vectors and 3x3 matrices -/
abbrev V3 := Int × Int × Int
structure M3 where
  r0 : V3
  r1 : V3
  r2 : V3
  deriving DecidableEq, Repr

def dot (a b : V3) : Int := a.1 * b.1 + a.2.1 * b.2.1 + a.2.2 * b.2.2
def mulVec (A : M3) (v : V3) : V3 := (dot A.r0 v, dot A.r1 v, dot A.r2 v)
def col (A : M3) : Nat → V3
  | 0 => (A.r0.1, A.r1.1, A.r2.1)
  | 1 => (A.r0.2.1, A.r1.2.1, A.r2.2.1)
  | _ => (A.r0.2.2, A.r1.2.2, A.r2.2.2)
def transpose (A : M3) : M3 := ⟨col A 0, col A 1, col A 2⟩
def mulM (A B : M3) : M3 :=
  let Bt := transpose B
  ⟨(dot A.r0 Bt.r0, dot A.r0 Bt.r1, dot A.r0 Bt.r2),
   (dot A.r1 Bt.r0, dot A.r1 Bt.r1, dot A.r1 Bt.r2),
   (dot A.r2 Bt.r0, dot A.r2 Bt.r1, dot A.r2 Bt.r2)⟩
def I3 : M3 := ⟨(1,0,0),(0,1,0),(0,0,1)⟩
def vadd (a b : V3) : V3 := (a.1 + b.1, a.2.1 + b.2.1, a.2.2 + b.2.2)
def vsub (a b : V3) : V3 := (a.1 - b.1, a.2.1 - b.2.1, a.2.2 - b.2.2)
def vscale (c : Int) (a : V3) : V3 := (c * a.1, c * a.2.1, c * a.2.2)
def vneg (a : V3) : V3 := (-a.1, -a.2.1, -a.2.2)
def comp (v : V3) : Nat → Int
  | 0 => v.1
  | 1 => v.2.1
  | _ => v.2.2
def setComp (v : V3) (k : Nat) (x : Int) : V3 :=
  match k with
  | 0 => (x, v.2.1, v.2.2)
  | 1 => (v.1, x, v.2.2)
  | _ => (v.1, v.2.1, x)
def e (j : Nat) : V3 := match j with | 0 => (1,0,0) | 1 => (0,1,0) | _ => (0,0,1)
def permMat (p : Nat × Nat × Nat) : M3 := ⟨e p.1, e p.2.1, e p.2.2⟩
def diag (a b c : Int) : M3 := ⟨(a,0,0),(0,b,0),(0,0,c)⟩
abbrev Pose := M3 × V3
structure Q where
  s : Int
  x : Int
  y : Int
  z : Int
  deriving DecidableEq, Repr
def qmul (a b : Q) : Q :=
  ⟨a.s*b.s - a.x*b.x - a.y*b.y - a.z*b.z, a.s*b.x + a.x*b.s + a.y*b.z - a.z*b.y,
   a.s*b.y - a.x*b.z + a.y*b.s + a.z*b.x, a.s*b.z + a.x*b.y - a.y*b.x + a.z*b.s⟩
def qOne : Q := ⟨1,0,0,0⟩
def vecQ (u : V3) : Q := ⟨0, u.1, u.2.1, u.2.2⟩
/-- (sigma.u_a)(sigma.u_b) = -(u_a u_b) in the quaternion algebra with e_i = -i sigma_i. -/
def cliffordLink (Ma Mb : M3) (n : V3) : Q :=
  let p := qmul (vecQ (mulVec (transpose Ma) n)) (vecQ (mulVec (transpose Mb) n))
  ⟨-p.s, -p.x, -p.y, -p.z⟩
def classOfQ (q : Q) : Nat :=
  if q.s == 1 then 0 else if q.s == -1 then 1 else if q.x != 0 then 2 else if q.y != 0 then 3 else 4

/-! ### (F8) Q_8 as a finite group: the class function is invariant under conjugation and inversion
`q8Elements` lists the eight unit quaternions {±1, ±i, ±j, ±k}; `qconj` is the quaternion conjugate, which is the
group inverse on Q_8 (`q8_conj_is_inverse`). The statements are finite checks (8 x 8 and 8 cases) decided by
`decide`. They are the formal content of the sentence "the holonomy class of a plaquette is gauge invariant and
independent of the base point and of the orientation": a gauge transformation or a change of base point conjugates
the holonomy, and reversing the orientation inverts it. -/
def qconj (a : Q) : Q := ⟨a.s, -a.x, -a.y, -a.z⟩
def q8Elements : List Q :=
  [⟨1,0,0,0⟩, ⟨-1,0,0,0⟩, ⟨0,1,0,0⟩, ⟨0,-1,0,0⟩, ⟨0,0,1,0⟩, ⟨0,0,-1,0⟩, ⟨0,0,0,1⟩, ⟨0,0,0,-1⟩]

theorem q8_closed : ∀ g ∈ q8Elements, ∀ w ∈ q8Elements, qmul g w ∈ q8Elements := by decide
theorem q8_conj_is_inverse : ∀ g ∈ q8Elements, qmul g (qconj g) = qOne ∧ qmul (qconj g) g = qOne := by decide
theorem q8_class_conj_invariant :
    ∀ g ∈ q8Elements, ∀ w ∈ q8Elements, classOfQ (qmul (qmul g w) (qconj g)) = classOfQ w := by decide
theorem q8_class_inverse_invariant : ∀ w ∈ q8Elements, classOfQ (qconj w) = classOfQ w := by decide
theorem foldl_add_split (l : List Nat) (g h : Nat → Int) : ∀ (a b : Int),
    l.foldl (fun acc c => acc + (g c + h c)) (a + b) =
      l.foldl (fun acc c => acc + g c) a + l.foldl (fun acc c => acc + h c) b := by
  induction l with
  | nil => intro a b; rfl
  | cons c l ih =>
    intro a b
    simp only [List.foldl_cons]
    rw [show a + b + (g c + h c) = (a + g c) + (b + h c) by omega]
    exact ih (a + g c) (b + h c)

theorem foldl_smul (l : List Nat) (g : Nat → Int) (k : Int) : ∀ (a : Int),
    l.foldl (fun acc c => acc + k * g c) (k * a) = k * l.foldl (fun acc c => acc + g c) a := by
  induction l with
  | nil => intro a; rfl
  | cons c l ih =>
    intro a
    simp only [List.foldl_cons]
    rw [← Int.mul_add]
    exact ih (a + g c)

theorem foldl_congr_mem (l : List Nat) (g h : Nat → Int) (hgh : ∀ c ∈ l, g c = h c) : ∀ (a : Int),
    l.foldl (fun acc c => acc + g c) a = l.foldl (fun acc c => acc + h c) a := by
  induction l with
  | nil => intro a; rfl
  | cons c l ih =>
    intro a
    simp only [List.foldl_cons]
    rw [hgh c (by simp)]
    exact ih (fun x hx => hgh x (by simp [hx])) (a + h c)

/-! ### (F6') The closed-form theorem in general form, independent of the certificate data
`applyG N S` is the linear operator x ↦ S x on vectors indexed by 0..N-1 (the same left fold as `applyS`, with the
dimension and the matrix as explicit arguments), and `CFG W8 W4 W2 W1 j r` is the closed form
8^(j+1) W8 r + 4^(j+1) W4 r + 2^(j+1) W2 r + W1 r.  THEOREM `closed_form_general`: for ANY N, S, f, D and any
sequence u with u 0 = f and u (j+1) = S (u j) + 8^(j+1) f, if W8, W4, W2, W1 satisfy the four eigen-identities
S W8 + D f = 8 W8, S W4 = 4 W4, S W2 = 2 W2, S W1 = W1 on 0..N-1 and the closed form holds at j = 2, then it holds
for every j >= 2.  The concrete theorem `closed_form_all` below is this theorem instantiated with the certified data
(N = 157, S = Sentry, f = fvec, u = useq). -/
def applyG (N : Nat) (S : Nat → Nat → Int) (x : Nat → Int) (r : Nat) : Int :=
  (List.range N).foldl (fun acc c => acc + S r c * x c) 0
def CFG (W8 W4 W2 W1 : Nat → Int) (j r : Nat) : Int :=
  (8 : Int) ^ (j+1) * W8 r + (4 : Int) ^ (j+1) * W4 r + (2 : Int) ^ (j+1) * W2 r + W1 r

theorem applyG_add (N : Nat) (S : Nat → Nat → Int) (x y : Nat → Int) (r : Nat) :
    applyG N S (fun c => x c + y c) r = applyG N S x r + applyG N S y r := by
  unfold applyG
  have h : (fun (acc : Int) (c : Nat) => acc + S r c * (x c + y c)) =
           (fun (acc : Int) (c : Nat) => acc + (S r c * x c + S r c * y c)) := by
    funext acc c; rw [Int.mul_add]
  rw [h]
  have := foldl_add_split (List.range N) (fun c => S r c * x c) (fun c => S r c * y c) 0 0
  simpa using this

theorem applyG_smul (N : Nat) (S : Nat → Nat → Int) (x : Nat → Int) (k : Int) (r : Nat) :
    applyG N S (fun c => k * x c) r = k * applyG N S x r := by
  unfold applyG
  have h : (fun (acc : Int) (c : Nat) => acc + S r c * (k * x c)) =
           (fun (acc : Int) (c : Nat) => acc + k * (S r c * x c)) := by
    funext acc c; rw [Int.mul_left_comm]
  rw [h]
  have := foldl_smul (List.range N) (fun c => S r c * x c) k 0
  simpa using this

theorem applyG_congr (N : Nat) (S : Nat → Nat → Int) (x y : Nat → Int) (hxy : ∀ c, c < N → x c = y c)
    (r : Nat) : applyG N S x r = applyG N S y r := by
  unfold applyG
  exact foldl_congr_mem (List.range N) (fun c => S r c * x c) (fun c => S r c * y c)
    (fun c hc => by rw [hxy c (List.mem_range.mp hc)]) 0

/-- Inductive step of the general theorem: linearity of `applyG` plus the four eigen-identities. -/
theorem step_case_general (N : Nat) (S : Nat → Nat → Int) (f W8 W4 W2 W1 : Nat → Int) (D : Int)
    (u : Nat → Nat → Int) (hu : ∀ j r, u (j+1) r = applyG N S (u j) r + (8:Int)^(j+1) * f r)
    (h8 : ∀ r, r < N → applyG N S W8 r + D * f r = 8 * W8 r) (h4 : ∀ r, r < N → applyG N S W4 r = 4 * W4 r)
    (h2 : ∀ r, r < N → applyG N S W2 r = 2 * W2 r) (h1 : ∀ r, r < N → applyG N S W1 r = W1 r)
    (j : Nat) (ih : ∀ r, r < N → D * u j r = CFG W8 W4 W2 W1 j r) :
    ∀ r, r < N → D * u (j+1) r = CFG W8 W4 W2 W1 (j+1) r := by
  intro r hr
  have k1 : D * applyG N S (u j) r = applyG N S (fun c => D * u j c) r := (applyG_smul N S (u j) D r).symm
  have k2 : applyG N S (fun c => D * u j c) r = applyG N S (CFG W8 W4 W2 W1 j) r :=
    applyG_congr N S _ _ (fun c hc => ih c hc) r
  have e1 : CFG W8 W4 W2 W1 j = fun c => ((fun c => (8 : Int) ^ (j+1) * W8 c + (4 : Int) ^ (j+1) * W4 c) c +
                                          (fun c => (2 : Int) ^ (j+1) * W2 c) c) + (fun c => W1 c) c := by
    funext c; rfl
  have e2 : (fun c => (8 : Int) ^ (j+1) * W8 c + (4 : Int) ^ (j+1) * W4 c) =
            fun c => (fun c => (8 : Int) ^ (j+1) * W8 c) c + (fun c => (4 : Int) ^ (j+1) * W4 c) c := by
    funext c; rfl
  have k3 : applyG N S (CFG W8 W4 W2 W1 j) r =
      (8 : Int) ^ (j+1) * applyG N S W8 r + (4 : Int) ^ (j+1) * applyG N S W4 r +
      (2 : Int) ^ (j+1) * applyG N S W2 r + applyG N S W1 r := by
    rw [e1, applyG_add, applyG_add, e2, applyG_add, applyG_smul, applyG_smul, applyG_smul]
  have g8 := h8 r hr
  have g4 := h4 r hr
  have g2 := h2 r hr
  have g1 := h1 r hr
  have g8' : applyG N S W8 r = 8 * W8 r - D * f r := by omega
  rw [hu j r, Int.mul_add, k1, k2, k3, g8', g4, g2, g1]
  unfold CFG
  rw [Int.pow_succ (8 : Int) (j+1), Int.pow_succ (4 : Int) (j+1), Int.pow_succ (2 : Int) (j+1)]
  rw [Int.mul_sub, Int.mul_left_comm D ((8 : Int) ^ (j+1)) (f r)]
  simp only [Int.mul_assoc]
  generalize (8 : Int) ^ (j+1) * (8 * W8 r) = X1 at *
  generalize (8 : Int) ^ (j+1) * (D * f r) = X2 at *
  generalize (4 : Int) ^ (j+1) * (4 * W4 r) = X3 at *
  generalize (2 : Int) ^ (j+1) * (2 * W2 r) = X4 at *
  omega

set_option linter.unusedVariables false in
/-- THEOREM (F6'), general form. No certificate data enters: N, S, f, D, W8, W4, W2, W1 and the sequence u are
    arbitrary; the hypotheses are the recursion u 0 = f, u (j+1) = S (u j) + 8^(j+1) f, the four eigen-identities
    on 0..N-1 and the closed form at j = 2. (`hu0` fixes the start of the recursion and is part of the stated
    interface; it is not needed in the induction, which starts from `hbase`, so the unused-variable linter is
    silenced for this declaration only.) -/
theorem closed_form_general (N : Nat) (S : Nat → Nat → Int) (f W8 W4 W2 W1 : Nat → Int) (D : Int)
    (u : Nat → Nat → Int) (hu0 : ∀ r, u 0 r = f r)
    (hu : ∀ j r, u (j+1) r = applyG N S (u j) r + (8:Int)^(j+1) * f r)
    (h8 : ∀ r, r < N → applyG N S W8 r + D * f r = 8 * W8 r) (h4 : ∀ r, r < N → applyG N S W4 r = 4 * W4 r)
    (h2 : ∀ r, r < N → applyG N S W2 r = 2 * W2 r) (h1 : ∀ r, r < N → applyG N S W1 r = W1 r)
    (hbase : ∀ r, r < N → D * u 2 r = CFG W8 W4 W2 W1 2 r) :
    ∀ j, 2 ≤ j → ∀ r, r < N → D * u j r = CFG W8 W4 W2 W1 j r := by
  intro j
  induction j with
  | zero => intro h; omega
  | succ n ih =>
    intro h
    cases Nat.lt_or_ge n 2 with
    | inl hlt =>
      have hn : n + 1 = 2 := by omega
      rw [hn]; exact hbase
    | inr hge => exact step_case_general N S f W8 W4 W2 W1 D u hu h8 h4 h2 h1 n (ih hge)
end TypeSubstitution
#print axioms TypeSubstitution.closed_form_general
#print axioms TypeSubstitution.step_case_general
#print axioms TypeSubstitution.q8_closed
#print axioms TypeSubstitution.q8_conj_is_inverse
#print axioms TypeSubstitution.q8_class_conj_invariant
#print axioms TypeSubstitution.q8_class_inverse_invariant
