# Icosian-chain addendum to the C1 Lean-chain public copy (2026-11-10)

**Public addendum candidate, rev4.1.** Proposed repository path: `lean/c1-icosian-chain-addendum-2026-11-10/` (new files only).

This folder adds thirteen scratch Lean modules that extend the C1 Lean-chain public copy (`lean/c1-lean-chain-2026-11-10/`, MANIFEST sha256 62342986cfd8410689b7fde41fada69752e9fc4aeff095c7286e22a3ebe18a56) and the geometric-frames addendum (`lean/c1-geometric-frames-addendum-2026-11-10/`). It is not a Lake package and not a Lake target. No licence is granted or implied. Neither earlier public folder is edited by this folder.

Each `.lean` file here is a comment-redacted copy of a pinned source. Only comments and docstrings differ: with all comments (`--` and `/- … -/`) stripped, the code of each copy is byte-identical to the code of its pinned source (see Provenance).

## Labels

[P] proved, [C] computed or certified, [S] standard (cited, not re-derived), [E] evidence, [X] conjecture, [A] analogy, [F] falsified.

A paper label may be weaker than its source, never stronger.

Each statement below marked [P, Lean, scratch, not peer reviewed] is scoped exactly to its own wording. Every module in this folder is final (source, independent audit PASS): the label is final for the pinned source of each module. The redacted copies in this folder were also rebuilt cleanly against public main plus Mathlib (see Build record). The isomorphism σ from the official icosahedral rotation group I to A5 is still defined by the table.

Stays [X] conjecture, not proved here and not implied by anything in this folder: an E8 isometry of the ℤ[φ]-span of the icosians; any derivation or formalisation of the McKay correspondence from these modules; the spectral floor. The McKay graph of the icosian group being the affine Ẽ8 diagram is a standard fact [S]; it is not re-derived and not in Lean here.

## Results

### Real frames (`IcosahedralFramesReal_2026-11-10.lean`)

The edge vectors u+w of the imported official icosahedron vertex set (vertex pairs at squared distance 4, the least nonzero squared distance) and five frames of them, labelled by chosen golden-ratio representatives, are defined directly on the official real vertex set; there are 30 edge vectors, nonzero and closed under negation; each frame has 6 vectors, is closed under negation and is pairwise orthogonal-or-parallel; the five frames are distinct and pairwise disjoint, partition the 30 edge vectors, and every orthogonal pair or triple of edge vectors lies in a single frame [P, Lean, scratch, not peer reviewed]. These real facts are proved by a proved transfer from the ℤ[√5] model. Every element g of the imported official group maps frame i onto frame σ(g)(i), and σ(g)(i) is the only frame that g maps frame i into, where σ is the isomorphism to A5, which is still defined by the table [P, Lean, scratch, not peer reviewed]. Each official edge vector is fixed by some element g ≠ 1 with g·g = 1 [P, Lean, scratch, not peer reviewed]. No classical-solid claim about the frames is made.

### Involutions fix edge vectors (`IcosahedralFramesInvolutions_2026-11-10.lean`)

In the ℤ[√5] model, exactly 15 of the 60 listed scaled rotation matrices A satisfy A ≠ 4·I and A·A = 16·I, and each fixes, up to the factor 4, some edge sum; every element g ≠ 1 with g·g = 1 of the imported official group fixes some official edge vector (with the real-frames module, both directions hold); the official edge vectors up to sign form exactly 15 sign-pairs {p, −p} [P, Lean, scratch, not peer reviewed]. Some identifier names in this module are historical; they refer to sign-pairs {p, −p} only and carry no further geometric claim.

### Face-sum sets and involutions (`IcosahedralCubesInvolutions_v2_2026-11-10.lean`)

Among the 20 official face sums u+v+w (official vertices at pairwise squared distance 4), the 8-point sets whose pairwise squared distances all lie in {s, 2s, 3s} for some s are exactly five, namely `officialCube i` := the face sums with equal squared projections onto every vector of `officialFrame i`; two points of officialCube i at squared distance 14+6√5 differ by a vector parallel to a vector of officialFrame i [P, Lean, scratch, not peer reviewed]. In the imported official group there are exactly 15 elements g ≠ 1 with g·g = 1 (Nat.card); any two official edge vectors fixed by such a g agree up to sign, and two such elements fixing the same official edge vector are equal, so they correspond bijectively to the 15 sign-pairs {p, −p} of official edge vectors, each g fixing both points of its pair [P, Lean, scratch, not peer reviewed]. In this module 'cube' names the {s, 2s, 3s} test only; the cube form and the group action are proved in the cube-completion module below. This module does not prove that g fixes exactly the span of p, or anything about g on p⊥. Two identifier names in it are historical; they refer to sign-pairs {p, −p} only and carry no further geometric claim.

### Cube completion (`IcosahedralCubeCompletion_2026-11-10.lean`)

For each k, cube k (`officialCube k`) has ncard 8 and equals {c + (s1•e1+s2•e2+s3•e3)/2 | si = ±1} with c = 0, a = 3+√5, ei⬝ei = a², the ei pairwise orthogonal, and each ei = φ•m for some m ∈ `officialFrame k` [P, Lean, scratch, not peer reviewed]. Every g in I maps cube k onto cube σ(g)(k): g '' officialCube k = officialCube (σ g k) [P, Lean, scratch, not peer reviewed]. The action on the five cubes is a faithful action onto A5 equal to σ: `officialCubeHom`, defined only from the action on the sets officialCube k, is injective, has range alternatingGroup (Fin 5), and equals σ g for every g [P, Lean, scratch, not peer reviewed]. σ itself is still defined by the table.

### Abstractions (`IcosahedralAbstractions_2026-11-10.lean`)

Generic lemmas: orthogonal matrices preserve the dot product and squared distance; an orthogonal A with A '' S = S maps the pair-sum and triple-sum sets of S onto themselves; on a finite set an injective self-map into itself is onto; transfer along a ring hom R →+* ℝ for dot products, matrix-vector products and scaled orthogonality, and, for an injective hom, vector equality, dot equations and ncard of list images; transitivity from one base point for a hom G →* Function.End X; Nat.card of a filtered subtype equals a filtered list length for a bijection onto a duplicate-free list [P, Lean, scratch, not peer reviewed].

Official group I: the official edge vectors and face sums are the pair sums and triple sums of the official vertex set, so every g maps each onto itself; I acts transitively with stabiliser order 5 on the vertex set, 2 on the edge vectors, 3 on the face sums, 12 on the cubes officialCube k and 12 on the frames officialFrame k; for each sign-pair {p, −p} of edge vectors, exactly 4 elements g satisfy g p = p ∨ g p = −p; every conjugacy class has 1, 12, 15 or 20 elements [P, Lean, scratch, not peer reviewed].

### Class orders (`IcosahedralClassOrders_2026-11-10.lean`)

Every g in I has element order (orderOf) 1, 2, 3 or 5, with 1, 15, 20 and 24 elements of each order; the class of g has 1, 15, 20 or 12 elements accordingly; g is conjugate to g⁻¹; an element g of order 5 is not conjugate to g²; Nat.card (ConjClasses I) = 5, with class sizes 1, 15, 20, 12, 12 [P, Lean, scratch, not peer reviewed]. All of these go through σ, the table-defined isomorphism. Characters and the assignment of rotation angles to the two size-12 classes are not proved.

### Icosians double cover (`BinaryIcosahedralIcosians_2026-11-10.lean`)

The 120 icosians, listed over ℤ[√5] (8 + 16 + 96 unit elements; the 96 are, as a set, the even permutations of ½(0, ±1, ±φ⁻¹, ±φ)), form a duplicate-free list of length 120 closed under multiplication and conjugation with x x⋆ = 1; they define a subgroup 2I of the units of the real quaternions with Nat.card 120; the map u ↦ (v ↦ u v u⋆) gives a surjective hom π onto the official group I, with π u = 1 ↔ u = ±1, kernel of card 2, and quotient ≃* I [P, Lean, scratch, not peer reviewed].

### Orders and classes of 2I (`BinaryIcosahedralOrders_2026-11-10.lean`)

Every element of 2I has element order (orderOf) in {1, 2, 3, 4, 5, 6, 10}, occurring 1, 1, 20, 30, 24, 20, 24 times; −1 is the unique element of order 2; the centre is {1, −1}; the image order in I is half the order if even and the same order if odd; two elements are conjugate iff they have the same real part; there are 9 conjugacy classes, with sizes 1, 1, 12, 12, 12, 12, 20, 20, 30 [P, Lean, scratch, not peer reviewed].

### Cube stabilisers lift to Q8; the cover does not split (`IcosianQ8FrameLift_2026-11-10.lean`)

For each k, the identity together with the involutions of I that stabilise cube k form a Klein four-subgroup V4^(k) of order 4, and each involution lies in exactly one V4^(k); Q^(k) := π⁻¹(V4^(k)) has card 8, satisfies q² = −1 for q ∉ {±1}, and is isomorphic to the quaternion group Q8 (Mathlib `QuaternionGroup 2`); Q^(j) ∩ Q^(k) = {1, −1} for j ≠ k; exactly 30 elements of 2I satisfy q² = −1; u Q^(k) u⁻¹ = Q^(j) iff π(u) maps cube k onto cube j; no Q^(k) is normal in 2I [P, Lean, scratch, not peer reviewed]. There is no hom s : I → 2I with π ∘ s = id [P, Lean, scratch, not peer reviewed]. π(u) is an involution iff u has order 4 iff Re u = 0, and these 30 elements form one class; π(u) and π(v) are conjugate iff u ~ v or −u ~ v; u ~ −u iff π(u) is an involution; 2 Re u ∈ {±2, ±1, ±φ, ±φ⁻¹, 0} [P, Lean, scratch, not peer reviewed]. The statement that the nine class sizes 1+1+30+20+20+12+12+12+12 sum to 120 and match the list of the 2I-orders module is literal-list arithmetic only: no theorem here states that each non-involution class of I pulls back to two classes of 2I of equal size swapped by −1. The 2I-orders results used inside this module are re-elaborated from a verbatim copy of that module's body (one theorem renamed to avoid a Mathlib name clash), not imported from it. The label of this module is [P, Lean, scratch, not peer reviewed] for exactly the statements above, with that scope limit: the per-class split is arithmetic only, not a theorem.

Trace pairing (standard, cited, not a Lean statement here): on the classes of 2I of orders 5 and 10, 2 Re = +φ⁻¹ on 5A, −φ on 5B, +φ on 10A and −φ⁻¹ on 10B, following the GroupNames and nLab character tables of SL(2,5); 2 Re = 0 is the order-4 class of size 30 [S].

### Exact 6D cut-and-project identities (`QuasicrystalCutProject6D_2026-11-10.lean`)

The matrices are transcribed from the script `qc/cutproject.py` (sha256 84663d078b203e235f512c590d6b3e08db433f3f1df3f7bcf2b8d87ece586c43), which is not in this repository; it is cited by name and hash only. The Galois conjugation √5 ↦ −√5 gives an injective ring hom to ℝ. Over ℤ[√5], WᵀW = (20+4√5)·1, W′ᵀW′ = (20−4√5)·1, WᵀW′ = 0 and (5−√5)WWᵀ + (5+√5)W′W′ᵀ = 80·1; transferred exactly, the parallel and perpendicular projectors satisfy P∥ᵀP∥ = 1, P⊥ᵀP⊥ = 1, P∥ᵀP⊥ = 0 and P∥P∥ᵀ + P⊥P⊥ᵀ = 1₆ [P, Lean, scratch, not peer reviewed]. The map g ↦ P∥RP∥ᵀ + P⊥R′P⊥ᵀ (R′ the Galois-conjugate rotation) is an injective hom from I into 6×6 real matrices whose values are signed permutation matrices, and it commutes with both projectors [P, Lean, scratch, not peer reviewed]. Idempotence and rank 3 of the projectors are corollaries of these identities, not separate Lean statements. The local permutation in the signed-permutation statement is not the table σ.

### (N, M) scale identity (`QuasicrystalNMScale_2026-11-10.lean`)

For every n ∈ ℤ⁶, with N and M as computed by `ico_NM` of the same script: ∑_j(∑_i n_i(A_ij+τB_ij))² = N+τM, and the same with τ replaced by 1−τ; |n·P∥|² = (N+τM)/(2(2+τ)) and |n·P⊥|² = (N+(1−τ)M)/(2(3−τ)); plus the generic identity for any x with x² = x+1 used to prove them [P, Lean, scratch, not peer reviewed].

### Facet normals of the cut-and-project construction (`QuasicrystalFacetNormals_2026-11-10.lean`)

'Facet normal' here means exactly the normals that the polytope constructor of the script `qc/cutproject.py` (not in this repository; see the 6D section above) computes: for the 15 index pairs i < j of the six generators, u_p = perp_i ⨯₃ perp_j. The 15 crosses are nonzero over ℤ[√5] and, after transfer, over ℝ (u_p equals (20−4√5)⁻¹ times the exact cross); two of them are parallel iff the pairs are equal; normalised, |û_p·û_q| = 1 iff p = q; and the signed normals ±û_p are 30 distinct vectors [P, Lean, scratch, not peer reviewed]. So, for the exact normals, no two are identified. That the constructor's 1e-9 tolerance filter keeps all 15 in floating point is a separate [C] statement: the largest off-diagonal |û·û′| is about 0.809, so its distance from 1 (about 0.19) is far larger than that tolerance [C]. That these are the facet normals of the polytope the constructor builds, and any triacontahedron reading, is not proved in Lean; it is supported only by a floating-point check [C]. Not claimed: polytope facet structure, the containment tolerance, a Monte-Carlo check, transitivity.

### Relation to the numerical code and to published comparisons

The three results above are exact algebraic statements about ℤ[√5] values, transferred through the real embedding, for the matrices of the script `qc/cutproject.py` (not in this repository). As exact warrants they cover the orthonormality and (N, M) checks of that script, and they show that the 15 normals the constructor computes are pairwise non-parallel. They do not cover the following, which stay [C] float computations: the orthonormality tolerance 1e-12 used in the numerical tests, the window membership tolerance 1e-9, the 1e-9 normal-deduplication tolerance, the 1% Monte-Carlo volume check, IEEE rounding of the numpy matrices, the vertex enumeration and tiling construction, and finite-radius boundary effects. The numerical tests of those matrices stay [C] smoke tests.

Computed powder diffraction models for Zn75Ni10Sc15 (compared with Maezawa, Kashimoto and Ishimasa, arXiv:cond-mat/0308480, Table 1) and for icosahedrite Al63Cu24Fe13 (compared with Bindi et al. 2011, Table 1) are [C] computed models against [E] published lists. The Lean results support only the embedding and the exact identities for |n·P∥|² and |n·P⊥|² in terms of (N, M) used to assign indices; they do not support intensities, rank correlations or peak matching. Interpretive sentences about those comparisons are [X], and assumptions are [A]. No comparison to any other measured quasicrystal is claimed, and the comparison tables and numerical code are not in this folder.

### Extreme points and a free orbit (`IcosahedralExtremeOrbit_2026-11-10.lean`)

For any S ⊆ (n → ℝ) whose points share a common value y⬝y = c, the extreme points (Mathlib Set.extremePoints) of convexHull S are exactly S; the same holds for norm-equal sets in any real inner product space (stated generically, not applied in this file); the official vertex set has v⬝v = (5+√5)/2 and is exactly the extreme-point set of its convex hull. A point with trivial stabiliser in I has an orbit of size 60; only the identity fixes (1, 2, 3), so its orbit has size 60 [P, Lean, scratch, not peer reviewed].

## Files

| File | sha256 of the redacted copy in this folder | sha256 of the pinned source |
|---|---|---|
| `IcosahedralFramesReal_2026-11-10.lean` | f436970a79c0280c6f05f5ff139c634c72c2c5a4065ac88c05cab9cb58e9a1e7 | 2e84adfe1d5c745dd1642a0c08b46bc787e64754f23f8dcfe7d4b91a380020a0 |
| `IcosahedralFramesInvolutions_2026-11-10.lean` | b484fd372518c33009c76e8a805a5f67fcf5672fb4b9ab0978d465836c3a0446 | 70c3e9f0b0037cb7695c9d28668c657444df0e55b6e3d7ce0723eeec81c40927 |
| `IcosahedralCubesInvolutions_v2_2026-11-10.lean` | 2925a8879498aed0fa38eca89e711a49ae989468f976eb8c08a3883bda2b0048 | 340f820417fd3d367317b982eb5eb92f5ae6ef1a62928ef914c9aecf5da6561e |
| `IcosahedralCubeCompletion_2026-11-10.lean` | 18f7bd9ead406a9d9c743d776b5d56bdfb953add06369c0c9b334ca458d333f9 | 8d46d6cbdcbc6d2f944abd219bf3e3576df72fd7fea3cf54e5cd230bddd4ac29 |
| `IcosahedralAbstractions_2026-11-10.lean` | b48166a5e0824cc63c1997d0159dc1424aa9669547c820ee48f347b93b427dca | dc045da6fc6d8a4cc0cb8fd88a0cec98c8a6861b1ddfc4ff3075bf2d83fee0bb |
| `IcosahedralClassOrders_2026-11-10.lean` | f2e511880a6b3c8e9afa3c5387c5c58fd9aea180073055e2aaa067a0a8c6b9f8 | 4c855de3d26b2da74563f602b7b73aaf617962658b6dcb6396584ca75d5a0010 |
| `BinaryIcosahedralIcosians_2026-11-10.lean` | 116663e65a75eaeb51140f3cd5d66460492fce7998fc8b693d0412a550ef227e | 9c9c6451741b4659c9bc8eb42217f3aac41657e22f3b69e5d5fe4fdcc3e6d0b9 |
| `BinaryIcosahedralOrders_2026-11-10.lean` | 6df25be422da005f9869d3ec546dec825fcfee333f0738e00ec15682bf70d220 | 9c5b4f8452bc60774b6ad9d5aebb3aa46d0ae762bc24c82b0e44d3fcd72533d8 |
| `IcosianQ8FrameLift_2026-11-10.lean` | 32060ee5137e36d40dff2699634a918c035906909c807531e3d156de3c55d626 | 186b52da8996fc38eaf74649a5b425b31a24ef9f0763e366fbf24a0ac3d5e057 |
| `QuasicrystalCutProject6D_2026-11-10.lean` | ca6f6d3ea35823940f0d82c00a70f02928a3a0b99535627ec70f089fc94af4de | 35a6d46c382b10bf9a7c818481db5b3ac2826657e286fae45972724d4bfe2b1c |
| `QuasicrystalFacetNormals_2026-11-10.lean` | 4e2a5621d1154846d66209e5bb46022f7efd2231e87b05769f0b97f744da5810 | 3b7e3ed0d64da2b063bfa31ddb63a68b00b222f15e8c5006707831b53cc186d9 |
| `QuasicrystalNMScale_2026-11-10.lean` | bfb5ba617136bcc67db61a6c0ab5140c152a5604d1cb97041c55a47becc60fbb | 3562bc7732b87860b33b74fa3637745c8e39265f6b71264659105de149b788e7 |
| `IcosahedralExtremeOrbit_2026-11-10.lean` | 23948523290d982cc247798a16f621fe4f3ae28604850c8244ef5f94422590cf | a084a85719079e6a7a312827e78b5d1747d0bf41a66c5fab1c2b683dab3a1346 |

Hash prefixes written `src xxxxxxxx…` in the header comments of the copies are prefixes of the pinned-source hashes in the last column of this table, not hashes of the redacted copies.

`README.md` (this file), `SHA256SUMS` (sha256 of every file except `SHA256SUMS` and `MANIFEST`) and `MANIFEST` (every file except itself, including `SHA256SUMS`) complete the folder.

## Depends on

Every module needed to build this folder is either in this folder or already public on main (commit b94c7687e525cfecfcac6d5cfb7de72c61b568f8), plus Mathlib. Each `import` name equals the file name of the module it refers to.

| Module | Where | Direct imports |
|---|---|---|
| `IcosahedralRotationGroup_2026-11-09` | main: `lean/c1-lean-chain-2026-11-10/` (fe54b0312e751037ca217ab7e84657c4e0e8b230051bfc818b954184efd597c9) | Mathlib only |
| `IcosahedralRotationGroupImportedMulEquiv_2026-11-10` | main: `lean/c1-lean-chain-2026-11-10/` (72424b02c07958f7ec5f6827c215c5f51cdd05381287b96fe2481dd0153b5c90) | `IcosahedralRotationGroup_2026-11-09`, Mathlib |
| `IcosahedralRotationGroupIsoAlternatingFive_v2_2026-11-10` | main: `lean/c1-lean-chain-2026-11-10/` (37faea30eb0caccd3712fe3cd7f54b620ee862b6e6b3b9380adfb0bf15b86278) | `IcosahedralRotationGroupImportedMulEquiv_2026-11-10`, Mathlib |
| `IcosahedralFramesGeometric_v2_2026-11-10` | main: `lean/c1-geometric-frames-addendum-2026-11-10/` (67c898ed267e0abc91c688cedfcb6b33cf1f5bf5400ac257d76ce700fba2d60f) | `IcosahedralRotationGroupIsoAlternatingFive_v2_2026-11-10` |
| `IcosahedralFramesReal_2026-11-10` | this folder | `IcosahedralFramesGeometric_v2_2026-11-10`, `Mathlib.LinearAlgebra.CrossProduct` |
| `IcosahedralFramesInvolutions_2026-11-10` | this folder | `IcosahedralFramesReal_2026-11-10` |
| `IcosahedralCubesInvolutions_v2_2026-11-10` | this folder | `IcosahedralFramesInvolutions_2026-11-10` |
| `IcosahedralCubeCompletion_2026-11-10` | this folder | `IcosahedralCubesInvolutions_v2_2026-11-10` |
| `IcosahedralAbstractions_2026-11-10` | this folder | `IcosahedralCubeCompletion_2026-11-10` |
| `IcosahedralClassOrders_2026-11-10` | this folder | `IcosahedralAbstractions_2026-11-10` |
| `BinaryIcosahedralIcosians_2026-11-10` | this folder | `IcosahedralAbstractions_2026-11-10`, `Mathlib.Algebra.Quaternion` |
| `BinaryIcosahedralOrders_2026-11-10` | this folder | `BinaryIcosahedralIcosians_2026-11-10` |
| `IcosianQ8FrameLift_2026-11-10` | this folder | `BinaryIcosahedralIcosians_2026-11-10`, `Mathlib.GroupTheory.SpecificGroups.Quaternion`, `Mathlib.GroupTheory.SpecificGroups.KleinFour` |
| `QuasicrystalCutProject6D_2026-11-10` | this folder | `IcosahedralAbstractions_2026-11-10` |
| `QuasicrystalFacetNormals_2026-11-10` | this folder | `QuasicrystalCutProject6D_2026-11-10`, `Mathlib.LinearAlgebra.CrossProduct`, `Mathlib.LinearAlgebra.Matrix.DotProduct` |
| `QuasicrystalNMScale_2026-11-10` | this folder | `QuasicrystalCutProject6D_2026-11-10`, `Mathlib.Tactic.LinearCombination` |
| `IcosahedralExtremeOrbit_2026-11-10` | this folder | `IcosahedralAbstractions_2026-11-10`, `Mathlib.Analysis.Convex.Extreme`, `Mathlib.Analysis.InnerProductSpace.Convex`, `Mathlib.LinearAlgebra.Matrix.DotProduct` |

The public frames module on main is itself a comment-redacted copy whose comment-stripped code is byte-identical to its original. The modules live in three directories (this folder and the two public folders above), so all three must be on the Lean module search path, together with Mathlib. No `import` statement needs to change. The simplicity module in the C1 Lean-chain public copy is not needed.

## Build record

**Clean rebuild of the redacted copies in this folder: done, against public main plus Mathlib.** The twelve copies other than the facet-normals copy were each built one at a time in a clean tree from the files of this folder, Mathlib, and the four public base modules on main that are not in this folder: `IcosahedralRotationGroup_2026-11-09`, `IcosahedralRotationGroupImportedMulEquiv_2026-11-10` and `IcosahedralRotationGroupIsoAlternatingFive_v2_2026-11-10` (in `lean/c1-lean-chain-2026-11-10/`), and `IcosahedralFramesGeometric_v2_2026-11-10` (in `lean/c1-geometric-frames-addendum-2026-11-10/`), each with the hash listed under Depends on. The facet-normals copy was built on top of the compiled modules from that clean build, which were not rebuilt in that run. Each build exited 0 with empty stderr, the emitted output is byte-identical to the recorded build text of the pinned source in the table below, and every `#print axioms` result is within `propext`, `Classical.choice` and `Quot.sound`.

The pre-redaction pinned sources were also each rebuilt cleanly in independent review (review notes are not listed here), with the same result. The table gives those recorded build texts.

| Module | Pre-redaction recorded build text sha256 |
|---|---|
| Real frames | b9c6d8ce394e376e76cfdb78c56d62abf9eb8aba3fce7e24fd58980b2f1cd5d6 |
| Involutions fix edge vectors | d88d2effd580343d471d01318e0d69e83b1f0c09c94ca87c33f3a081502e71d1 |
| Face-sum sets and involutions | 4abd202aa4d096ef69cf8c0855417807fc7da0c3b9cb318f9d0038d7d97b2ae8 |
| Cube completion | 05c0a90610428246da1e3e26ffd4b387c8e53cd39c5bdc24bd432673e3eb638a |
| Abstractions | 6be18eb9d2741038ae60d629d54e1483ae0892c06cecb7c0828a3524f1434af9 |
| Class orders | 5e967828928db12dfa13b855b85993278253840c1a47d371df48f6b46de93111 |
| Icosians | 054d4880f0c785619bcb695b0f0b66a651e117cefaf5d11eb5384778374cdc6d |
| 2I orders | 39c465ec990cc6f04e0e77c3dabf1a108afdc4a4f446f59149ac4248cd67d29c |
| Q8 lift | ef41a57fa86b54c300ee8552b78f4fddf4aee38d401493b77c1d0bfe63cd8980 |
| 6D cut-and-project | 58f85d3c94c37f1c4ec33250c90a38cbbe490ab0d032dbe43b3f3b8f5f43a8f0 |
| Facet normals | 24386c0aa4ead16773aa9b146bd858f92a9398c838d631a254ff14f474ca1978 |
| (N, M) scale | 7b7528d537b4dc808592f7e23b5f78fbcbcb92393415fbbbac4a3e1d52662196 |
| Extreme points / orbit | 1ecde05772f51ff87b59b4bd9bb8c380f0da84b6ebdd8df9680cd8eb1dc4d5e3 |

Toolchain recorded for the official chain: Lean 4 v4.36.0-rc2, Mathlib v4.36.0-rc2 at git 9d581dfff2e41de989072ea63abf3daf69311520. Recorded build texts and compiled artifacts are omitted.

## Provenance

Each copy differs from its pinned source in comments and docstrings only. Edits: authorship and work-tracking references, frozen-statement filenames, private build paths and compiled-artifact references, and descriptions of transitive imports were removed from header comments; in the 6D cut-and-project module an internal record reference was replaced with "the exact projector identities for the icosahedral cut-and-project basis"; in the (N, M) module the script path was shortened to `qc/cutproject.py`; the facet-normals module is a new comment-only copy (header comment: authorship, frozen-statement filename, handoff reference and private build path removed; 'facet normal' defined as the constructor's normals); in the face-sum module, comments that named two legacy identifiers were reworded, and one comment states that the identifier names are historical; in the real-frames and involutions modules, comments were reworded to describe edge sign-pairs {p, −p} without classical-solid wording, and the involutions module carries the same historical-names comment. Comment-stripped code (all `--` and `/- … -/` comments removed, trailing whitespace and empty rows dropped) of each copy is byte-identical to that of its pinned source.

## Not in this folder

Working notes, frozen statement files, recorded build texts, compiled artifacts and the script cited above are omitted. Modules already public on main are cited, not copied. Earlier public folders and frozen preprint files are not modified by this folder.
