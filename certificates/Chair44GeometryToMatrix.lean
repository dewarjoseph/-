/-
Geometry-to-matrix certificate for the Level-1 Chair44 supertile.

Unlike `Chair44Certificates.lean` and `PvsNPCliffordCertificates.lean`, which take the 8x8 Laplacian and the
Clifford link values as *stored constants*, this file constructs the Level-1 tiling from the substitution rule
and the FR30 frames inside Lean, derives the shared-panel multigraph, the contact Laplacian and the
face-normal Clifford links in Q_8, and checks the resulting numbers by `decide`.  Everything is computed from
the axioms A1-A6 of deliverables/CLIFFORD_Q8_END_TO_END_AUDIT.md; no matrix is pasted in.
-/
namespace Chair44GeometryToMatrix

abbrev V3 := Int × Int × Int

/-- 3x3 integer matrix as rows. -/
structure M3 where
  r0 : V3
  r1 : V3
  r2 : V3
  deriving DecidableEq, Repr

def dot (a b : V3) : Int := a.1 * b.1 + a.2.1 * b.2.1 + a.2.2 * b.2.2
def mulVec (A : M3) (v : V3) : V3 := (dot A.r0 v, dot A.r1 v, dot A.r2 v)
def col (A : M3) (i : Nat) : V3 :=
  match i with
  | 0 => (A.r0.1, A.r1.1, A.r2.1)
  | 1 => (A.r0.2.1, A.r1.2.1, A.r2.2.1)
  | _ => (A.r0.2.2, A.r1.2.2, A.r2.2.2)
def transpose (A : M3) : M3 := ⟨col A 0, col A 1, col A 2⟩
def mulM (A B : M3) : M3 :=
  let Bt := transpose B
  ⟨(dot A.r0 Bt.r0, dot A.r0 Bt.r1, dot A.r0 Bt.r2),
   (dot A.r1 Bt.r0, dot A.r1 Bt.r1, dot A.r1 Bt.r2),
   (dot A.r2 Bt.r0, dot A.r2 Bt.r1, dot A.r2 Bt.r2)⟩
def det (A : M3) : Int :=
  A.r0.1 * (A.r1.2.1 * A.r2.2.2 - A.r1.2.2 * A.r2.2.1)
  - A.r0.2.1 * (A.r1.1 * A.r2.2.2 - A.r1.2.2 * A.r2.1)
  + A.r0.2.2 * (A.r1.1 * A.r2.2.1 - A.r1.2.1 * A.r2.1)
def I3 : M3 := ⟨(1,0,0),(0,1,0),(0,0,1)⟩
def vadd (a b : V3) : V3 := (a.1 + b.1, a.2.1 + b.2.1, a.2.2 + b.2.2)
def vsub (a b : V3) : V3 := (a.1 - b.1, a.2.1 - b.2.1, a.2.2 - b.2.2)
def vscale (c : Int) (a : V3) : V3 := (c * a.1, c * a.2.1, c * a.2.2)

/-- Permutation matrix of a permutation given as the image tuple (p0,p1,p2): row i has a 1 in column p_i. -/
def e (j : Nat) : V3 := match j with | 0 => (1,0,0) | 1 => (0,1,0) | _ => (0,0,1)
def permMat (p : Nat × Nat × Nat) : M3 := ⟨e p.1, e p.2.1, e p.2.2⟩
def diag (a b c : Int) : M3 := ⟨(a,0,0),(0,b,0),(0,0,c)⟩

/-- A1: the seven octant vectors U_3 = {0,1}^3 \ {(1,1,1)}. -/
def U3 : List V3 := [(0,0,0),(0,0,1),(0,1,0),(0,1,1),(1,0,0),(1,0,1),(1,1,0)]

/-- A3: FR30 permutations, indexed as (centre, then U3 in the order above). -/
def fr30 : V3 → Nat × Nat × Nat
  | (0,0,0) => (0,1,2) | (0,0,1) => (0,2,1) | (0,1,0) => (2,1,0) | (0,1,1) => (1,2,0)
  | (1,0,0) => (1,0,2) | (1,0,1) => (0,1,2) | (1,1,0) => (2,0,1) | _ => (0,1,2)
def pi0 : Nat × Nat × Nat := (0,1,2)

/-- A2: the eight Level-1 child poses (frame, translation) in doubled coordinates. -/
def childPoses : List (M3 × V3) :=
  (permMat pi0, (1,1,1)) ::
  U3.map (fun v => (mulM (diag (1 - 2*v.1) (1 - 2*v.2.1) (1 - 2*v.2.2)) (permMat (fr30 v)), vscale 4 v))

/-- Unit cubes of a posed chair: corner = (G*(2u+1) + 2T - 1)/2 for u in U3 (exact division). -/
def cubesOf (G : M3) (T : V3) : List V3 :=
  U3.map (fun u =>
    let c := vadd (mulVec G (vadd (vscale 2 u) (1,1,1))) (vsub (vscale 2 T) (1,1,1))
    (c.1 / 2, c.2.1 / 2, c.2.2 / 2))

def tiles : List (M3 × V3 × List V3) := childPoses.map (fun gt => (gt.1, gt.2, cubesOf gt.1 gt.2))
def allCubes : List V3 := tiles.foldl (fun acc t => acc ++ t.2.2) []

/-- Owner of a cube (tile index), if any. -/
def owner (c : V3) : Option Nat :=
  (List.range 8).find? (fun a => ((tiles.getD a (I3, (0,0,0), [])).2.2).contains c)

/-- A4: directed shared panels (a, b, axis) for cubes c in a and c + e_axis in b, a != b. -/
def panels : List (Nat × Nat × Nat) :=
  allCubes.foldl (fun acc c =>
    acc ++ ([0,1,2].filterMap (fun ax =>
      match owner c, owner (vadd c (e ax)) with
      | some a, some b => if a != b then some (a, b, ax) else none
      | _, _ => none))) []

/-- Contact weights w_ab = number of shared unit squares. -/
def weight (a b : Nat) : Int :=
  (panels.filter (fun p => (p.1 == a && p.2.1 == b) || (p.1 == b && p.2.1 == a))).length

def laplacianEntry (a b : Nat) : Int :=
  if a == b then (List.range 8).foldl (fun s c => if c == a then s else s + weight a c) 0 else - weight a b
def laplacian : List (List Int) := (List.range 8).map (fun a => (List.range 8).map (fun b => laplacianEntry a b))

/-- A5: Clifford link as an integer quaternion (s,x,y,z) with i=-i sigma_1 etc., i.e. C = (u_a.u_b) - (u_a x u_b).(i,j,k). -/
structure Q where
  s : Int
  x : Int
  y : Int
  z : Int
  deriving DecidableEq, Repr
def qmul (a b : Q) : Q :=
  ⟨a.s*b.s - a.x*b.x - a.y*b.y - a.z*b.z, a.s*b.x + a.x*b.s + a.y*b.z - a.z*b.y,
   a.s*b.y - a.x*b.z + a.y*b.s + a.z*b.x, a.s*b.z + a.x*b.y - a.y*b.x + a.z*b.s⟩
def qconj (a : Q) : Q := ⟨a.s, -a.x, -a.y, -a.z⟩
def qOne : Q := ⟨1,0,0,0⟩
def vecQ (u : V3) : Q := ⟨0, u.1, u.2.1, u.2.2⟩
/-- (sigma.u_a)(sigma.u_b) = -(u_a u_b) in the quaternion algebra with e_i = -i sigma_i. -/
def cliffordLink (Ma Mb : M3) (n : V3) : Q :=
  let p := qmul (vecQ (mulVec (transpose Ma) n)) (vecQ (mulVec (transpose Mb) n))
  ⟨-p.s, -p.x, -p.y, -p.z⟩
def frameOf (a : Nat) : M3 := (tiles.getD a (I3, (0,0,0), [])).1
def panelLinks : List Q := panels.map (fun p => cliffordLink (frameOf p.1) (frameOf p.2.1) (e p.2.2))
def isQ8 (q : Q) : Bool := q.s*q.s + q.x*q.x + q.y*q.y + q.z*q.z == 1
def countLink (q : Q) : Nat := (panelLinks.filter (fun r => r == q)).length

/-- Transport across cube boundary c -> c' (identity inside a tile). -/
def linkCubes (c c' : V3) : Q :=
  match owner c, owner c' with
  | some a, some b => if a == b then qOne else cliffordLink (frameOf a) (frameOf b) (vsub c' c)
  | _, _ => qOne
def isCube (c : V3) : Bool := allCubes.contains c
/-- A6 on canonical plaquettes: holonomy around the four cubes c, c+e_i, c+e_i+e_j, c+e_j, inter-tile only. -/
def plaquetteHolonomies : List Q :=
  allCubes.foldl (fun acc c =>
    acc ++ ([(0,1),(1,2),(0,2)].filterMap (fun ij =>
      let c1 := vadd c (e ij.1); let c2 := vadd c1 (e ij.2); let c3 := vadd c (e ij.2)
      if isCube c1 && isCube c2 && isCube c3 then
        match owner c, owner c1, owner c2, owner c3 with
        | some a, some b, some d, some f =>
          if a == b && b == d && d == f then none
          else some (qmul (qmul (qmul (linkCubes c c1) (linkCubes c1 c2)) (linkCubes c2 c3)) (linkCubes c3 c))
        | _, _, _, _ => none
      else none))) []
def countHol (q : Q) : Nat := (plaquetteHolonomies.filter (fun r => r == q)).length

set_option maxRecDepth 100000 in
/-- Geometry facts: 56 distinct cubes, 48 shared panels, all eight frames in SO(3,Z). -/
theorem level1_geometry :
    allCubes.length = 56 ∧ allCubes.eraseDups.length = 56 ∧ panels.length = 48 ∧
    (tiles.all (fun t => mulM (transpose t.1) t.1 == I3 && det t.1 == 1)) = true := by
  decide

set_option maxRecDepth 100000 in
/-- The contact Laplacian computed from the geometry equals the matrix used by all the stored certificates. -/
theorem level1_laplacian_from_geometry :
    laplacian = [ [21, -3, -3, -3, -3, -3, -3, -3],
                  [-3, 12, -3, -3,  0, -3,  0,  0],
                  [-3, -3, 12,  0, -3,  0, -3,  0],
                  [-3, -3,  0, 12, -3,  0,  0, -3],
                  [-3,  0, -3, -3,  9,  0,  0,  0],
                  [-3, -3,  0,  0,  0, 12, -3, -3],
                  [-3,  0, -3,  0,  0, -3,  9,  0],
                  [-3,  0,  0, -3,  0, -3,  0,  9] ] := by
  decide

set_option maxRecDepth 100000 in
/-- Every panel link lies in Q_8; 24 links equal -1, 6 equal +1, 18 are traceless. -/
theorem level1_links_in_Q8 :
    (panelLinks.all isQ8) = true ∧ countLink ⟨-1,0,0,0⟩ = 24 ∧ countLink qOne = 6 ∧
    (panelLinks.filter (fun q => q.s == 0)).length = 18 := by
  decide

set_option maxRecDepth 100000 in
/-- Canonical inter-tile plaquette curvature at Level 1: 60 plaquettes; 26 trivial, 3 central (-1), 31 traceless. -/
theorem level1_plaquette_curvature :
    plaquetteHolonomies.length = 60 ∧ countHol qOne = 26 ∧ countHol ⟨-1,0,0,0⟩ = 3 ∧
    (plaquetteHolonomies.filter (fun q => q.s == 0)).length = 31 ∧
    (plaquetteHolonomies.all isQ8) = true := by
  decide

end Chair44GeometryToMatrix

#print axioms Chair44GeometryToMatrix.level1_geometry
#print axioms Chair44GeometryToMatrix.level1_laplacian_from_geometry
#print axioms Chair44GeometryToMatrix.level1_links_in_Q8
#print axioms Chair44GeometryToMatrix.level1_plaquette_curvature
