# Phase V: Universal Geometric Dynamics. What the Hierarchy Determines, Proves, and Predicts

This document reports the fifth research phase on the Chair44 / FR30 / Clifford $Q_8$ construction. It builds on
`deliverables/CLIFFORD_Q8_END_TO_END_AUDIT.md` (audit) and `deliverables/CLIFFORD_Q8_PHASE2_RESEARCH.md`
(structure, exact limits). Nothing from those documents is assumed; every result used here was re-run in this phase
(Section 1). All scripts live in `audit/`, all outputs in `audit/results/`, all formal proofs in `certificates/`.

## 0. The decisive advance, stated plainly

**Theorem (Exact renormalization of gauge-invariant local observables on a decorated block substitution).** Let a
decorated block substitution with integer inflation factor $L$ in dimension $d$ be given (prototile a finite union
of unit cubes that exactly self-replicates under inflation, a finite frame group, and a child-frame rule), together
with any link rule that depends only on the relative configuration of the two tiles sharing a face. Then the
intrinsic types of faces and of lattice edges that occur in the approximants form a finite set, inflation induces a
linear map on type counts, and for every $m\ge1$
$$v_{m+1}=S\,v_m+(L^d)^m f,\qquad S=\begin{pmatrix}M&0\\A&B\end{pmatrix},$$
with $M$, $B$ nonnegative integer matrices of constant column sums $L^{d-1}$ and $L^{d-2}$. Consequently every local
gauge-invariant observable (in particular the conjugacy class of the plaquette holonomy) has an exactly computable
rational limiting frequency, and its finite-size counts are exact finite sums $\sum_\lambda p_\lambda(m)\lambda^m$
over $\lambda\in\{L^d\}\cup\operatorname{spec}(S)$. The eigenvalues $L^d,L^{d-1},L^{d-2}$ are universal; the rest of
$\operatorname{spec}(S)$ is decoration-dependent, and for the FR30 decoration it is exactly $\{1,0\}$.

For FR30 this is now **machine-checked**: `certificates/TypeSubstitutionCertificate.lean` derives the 49 panel
types and 108 plaquette types from the substitution rule, verifies the recursion against the geometry at levels 1
and 2, and proves by induction that for all $m\ge3$
$$64\,v_m=8^mW_8+4^mW_4+2^mW_2+W_1,$$
from which the limiting class frequencies $19/36,\ 13/144,\ 1/9,\ 23/144,\ 1/9$ are read off as kernel-checked
rational identities (Section 5 states exactly which steps are kernel-checked and which are paper).

The phase also **corrects** a claim of Phase 2: the spectral bottom $E_0\approx5.27$ of the Clifford hopping
operator is a surface band, not the bulk spectral infimum. The ground state of the free-boundary operator carries
93% of its weight on boundary tiles at every level from 2 to 5; with bulk coordination imposed on all tiles the bulk
infimum is bracketed above by 8.92 (level 4) and is still decreasing (Section 3).

And it **bounds the universality** of the hierarchy: the exact-law structure persists for a periodic cubic geometry
with an aperiodic decoration, so it is a property of self-reproducing *decorations*, not of aperiodic *geometry*;
generic admissible decorations have extra algebraic and complex eigenvalues (period-3 oscillations, expanding modes
of modulus up to 2.56), so FR30's clean spectrum is special, and no simple contact-language criterion predicts it
(Section 7).

---

## 1. Phase I: reconstruction and reproduction

**Environment.** Linux 6.18.44, 4 cores, 16 GB; Python 3.13.16, numpy 2.5.3, scipy 1.18.1, sympy 1.14.0;
Lean 4.34.1 (release binary, commit 5045d005), no Mathlib. Branch `claude/magical-euler-0vm2f8`, starting commit
`0bb67fb`.

**What the pre-existing Lean certificates establish.**
- `Chair44Certificates.lean`: finite `decide` checks on pasted constants (frames, a sample loop, polynomial values).
  Sections 4 and 5 evaluate the *claimed* characteristic polynomial at three points and never touch a matrix.
- `PvsNPCliffordCertificates.lean`: genuine universal theorems about telescoping and gauge covariance over an
  arbitrary group; linear algebra of pasted matrices (Spin(4) Gram matrix, 9-point Bareiss determinant of the
  pasted Laplacian); classical restricted-model complexity lemmas.
- `Chair44GeometryToMatrix.lean` (Phase 2): the first file that computes the level-1 Laplacian, the 48 links and the
  60 plaquette holonomies *from the substitution rule* inside the kernel.
- The 49-panel/108-plaquette recursion of `audit/phase4_type_substitution_proof.py` was, before this phase, a
  Python result with exact SymPy arithmetic and **not** formalized. It is now (Section 5), with a precise boundary.

**Reproduction record (commands run from the repository root; outputs under `audit/results/`).**

| Command | Result |
|---|---|
| `python3 -I audit/independent_clifford_q8_audit.py` | geometry, Laplacian polynomial, 48 links, $b_1=41,513,4865$, $\mathrm{Hol}=Q_8$ |
| `python3 -I audit/phase4_type_substitution_proof.py` | 49/108 types; recursion reproduces levels 1 to 5; spectrum $\{4,2,1,0\}$; limits |
| `python3 -I audit/export_type_certificate.py` | regenerates `certificates/TypeSubstitutionCertificate.lean` (D = 64) |
| `python3 -u -I audit/phase5_dynamics_boundary.py 5` | free vs pinned spectra, IPR, boundary weight (Section 3) |
| `python3 -u -I audit/phase5_universality_types.py` | spectra for 9 chair decorations and 3 cube-geometry decorations |
| `python3 -u -I audit/phase5_closure_vs_spectrum.py` | $\lvert P_0\rvert$ census and spectra of all low-$\lvert P_0\rvert$ decorations |
| `python3 -I audit/phase5_cube_control_spectrum.py` | alternative-substitution and mirror controls for the experiment |
| `python3 -m unittest tests/test_independent_audit_regression.py` | see Section 9 |

Classification of evidence used in this document: **[K]** kernel-checked in Lean 4.34.1 with `decide +kernel`
(axioms: `propext`, and for the hand proofs `Quot.sound`, `Classical.choice` from `funext`/`omega`), **[E]** exhaustive
finite computation in exact integer or rational arithmetic (Python), **[N]** floating-point numerics, **[P]** paper
proof, **[H]** physical hypothesis.

---

## 2. Phase II: the renormalization theorem

### 2.1 Definitions

**Decorated block substitution.** Data: a prototile $P\subset\mathbb Z^d$ (finite union of unit cubes; here the
chair, 7 cubes), a finite group $G\subset O(d,\mathbb Z)$ of signed permutation matrices (here $SO(3,\mathbb Z)$,
order 24), the pose group $\Gamma=G\ltimes\mathbb Z^d$, an integer $L\ge2$ (here 2), and a list of $K$ child poses
$(g_c,t_c)$ (here $K=8$) such that the cubes of the children of the identity pose are exactly the cubes of the
dilate $L\cdot P$ (**exact self-replication**; for the chair: 56 cubes, the region $[0,4)^3\setminus[2,4)^3$,
checked [K]). Inflation of a pose $p=(G,T)$ is $\sigma(p)=\{(Gg_c,\ LT+Gt_c)\}_c$ (doubled coordinates as in the
code). The level-$m$ approximant is $\mathcal T_m=\sigma^m(\mathrm{root})$.

**Equivariance.** For $\gamma=(R,s)\in\Gamma$, $\sigma(\gamma p)=\gamma_L\,\sigma(p)$ where $\gamma_L=(R,Ls)$.
Equivalently, the cubes of the children of $p$ are the rigid image $s\mapsto(G(2s+\mathbf 1)+4T-\mathbf 1)/2$ of the
cubes of the children of the root. [P: linear algebra; K: verified for every tile occurring in the certificate and
in $\mathcal T_1$.]

**Intrinsic types.** A *panel* is a unit face shared by cubes of two different tiles; a *plaquette* is a lattice
edge whose four surrounding cubes are present and belong to at least two tiles. The type of a panel is the
$\Gamma$-orbit of (the two posed tiles, the face); the type of a plaquette is the $\Gamma$-orbit of (the up to four
posed tiles, the edge). Both are encoded by relative poses in the body frame of a reference tile and canonicalized
by minimizing over the admissible reference choices (2 for panels, 8 for plaquettes). Two configurations have the
same type iff they are related by an element of $\Gamma$ (the encoding records the complete relative configuration).

**Link rule and observable.** $C^{(f)}_{ab}=(\boldsymbol\sigma\cdot M_a^\top\mathbf n_f)(\boldsymbol\sigma\cdot M_b^\top\mathbf n_f)\in Q_8$
depends only on $(M_a^\top M_b,\ M_b^\top\mathbf n_f)$, hence only on the panel type. The plaquette holonomy
$W=C_{01}C_{12}C_{23}C_{30}$ is defined up to conjugation and inversion by the choice of base cube and orientation;
its $Q_8$ conjugacy class is a function of the plaquette type (classes are closed under inversion). The *observable*
is the class vector $\mathrm{Count}_m(c)$, $c\in\{\{+1\},\{-1\},\{\pm i\},\{\pm j\},\{\pm k\}\}$.

### 2.2 Theorem A (finite type closure and exact recursion) [P + K]

Let $P_m$ (resp. $\Pi_m$) be the vector of panel-type (resp. plaquette-type) counts of $\mathcal T_m$.

1. **Finiteness.** The set of panel and plaquette types occurring in $\bigcup_m\mathcal T_m$ is finite. *Proof.* A
   type is determined by at most four relative poses $(M_a^\top M_b,\ M_a^\top(T_b-T_a))$ with $M_a^\top M_b$ in
   the finite group $G$ and the translation bounded by the diameter of two adjacent tiles, together with local
   positions inside the finite cube set of $P$. $\square$ For FR30 exactly 49 and 108 types occur [E; K: distinct
   and closed under inflation].

2. **Inflation images.** Each panel type $\rho$ determines the multiset $M\rho$ of the $L^{d-1}$ fine panel types
   covering the inflated panel and the multiset $A\rho$ of the fine plaquettes whose edges lie in the interior of the
   inflated panel (for $d=3$ the $L\times L$ grid has $2L(L-1)$ interior edges, i.e. 4 for $L=2$); each plaquette
   type $\theta$ determines the multiset $B\theta$ of the $L$ fine plaquette types along the inflated edge. *Proof.* All fine cubes involved are children of the
   tiles in the configuration; by equivariance, $\Gamma$-equivalent configurations have $\Gamma_L$-equivalent
   inflations; types are $\Gamma$-invariant. $\square$ [K: images verified on one representative per type, which by
   this argument suffices.]

3. **Decomposition (parity trichotomy).** Let $e$ be a fine lattice edge of $\mathcal T_{m+1}$ in direction $k$ with
   midpoint $\mu$ (half-integer in direction $k$, integers $\mu_i,\mu_j$ otherwise). The four fine cubes around $e$
   have corners $\mu-\tfrac12\mathbf e_k-\epsilon_i\mathbf e_i-\epsilon_j\mathbf e_j$, $\epsilon\in\{0,1\}$. Their
   coarse parents $\lfloor\cdot/2\rfloor$ coincide in direction $k$ and, in direction $i$, coincide iff $\mu_i$ is
   odd (and likewise for $j$). Hence the set of coarse parent cubes has size 1, 2 or 4 according to whether
   $(\mu_i,\mu_j)$ has two, one or zero odd entries; in the three cases $\mu/2$ lies in the interior of a coarse
   cube, in the interior of a coarse face, or on a coarse edge. If all coarse parents lie in one coarse tile $t$,
   $e$ is interior to $\sigma(t)$, a rotated copy of $\mathcal T_1$ (equivariance), so it is a plaquette iff its
   class is one of the 60 of $\mathcal T_1$. Otherwise the coarse parents span at least two tiles and $e$ is either
   one of the 4 interior edges of an inflated inter-tile panel (size-2 case) or one of the 2 fine edges along an
   inflated inter-tile plaquette (size-4 case; the four coarse cubes are present because the fine cubes are). The
   three categories are disjoint and exhaustive. $\square$

4. **Recursion.** Therefore, exactly,
$$P_{m+1}=8^m p_1+M P_m,\qquad \Pi_{m+1}=8^m\pi_1+A P_m+B\,\Pi_m,\qquad \mathrm{Count}_m(c)=\sum_{\theta\in c}\Pi_m(\theta),$$
with $p_1,\pi_1$ the type vectors of $\mathcal T_1$ (48 panels, 60 plaquettes). [K: the recursion's class counts
equal the directly enumerated class counts of $\mathcal T_1$ and $\mathcal T_2$; E: equal at levels 3, 4, 5 and
the straddling counts at levels 6, 7.]

### 2.3 Theorem B (spectral structure: universal and non-universal parts) [P + E]

1. $M$ and $B$ are nonnegative integer matrices with constant column sums $L^{d-1}=4$ and $L^{d-2}=2$ (a coarse
   panel is covered by exactly 4 fine panels; a coarse edge by exactly 2 fine edges). Hence $4\in\operatorname{spec}M$,
   $2\in\operatorname{spec}B$ (left eigenvector $\mathbf 1$), and $\rho(M)\le4$, $\rho(B)\le2$. The forcing eigenvalue
   $8=L^d$ exceeds $\rho(S)$, so $(8-S)$ is invertible over $\mathbb Q$ and
   $$v_m=8^m u+O(4^m),\qquad u=(8-S)^{-1}f\in\mathbb Q^{157}.$$
   All limiting frequencies are rational. **Universal** for every decorated block substitution.

2. The remaining spectrum is **decoration-dependent**. For FR30:
   $\det(\lambda-M)=\lambda^{44}(\lambda-4)(\lambda-1)^4$, $\det(\lambda-B)=\lambda^{103}(\lambda-2)(\lambda-1)^4$,
   nonzero part semisimple, nilpotent index 2 [E]. For the achiral and canonical-homochiral decorations the nonzero
   spectrum is again $\subseteq\{4,2,1\}$. For six random admissible decorations the factors include
   $\lambda^2+\lambda+1$ (period-3 oscillation), $\lambda+1$, $\lambda^2+\lambda-4$ (a real root $\approx-2.56$),
   $\lambda^2-3\lambda+1$ (golden-ratio roots), $\lambda^3-\lambda^2-\lambda-1$ (tribonacci root 1.839), etc.
   [E: `audit/results/phase5_universality_types.txt`]. Such decorations still obey Theorem A, but their finite-size
   corrections oscillate and their limiting frequencies have denominators built from $8^2+8+1=73$,
   $8^2-8-4=52$, and so on.

3. The clean spectrum is **not** implied by a small contact language: all 3 decorations with the minimal
   $\lvert P_0\rvert=26$ are clean, none of the 6 with $\lvert P_0\rvert=29$ is, 9 of the 15 with $\lvert P_0\rvert=30$
   are (FR30 among them), and none of the sampled decorations with $\lvert P_0\rvert\ge50$ is
   [E: `audit/results/phase5_closure_vs_spectrum.txt`]. Interface stability (nonzero spectrum $\{L^{d-1},L^{d-2},1\}$,
   i.e. interface types reaching fixed points after a bounded transient) is a decoration property without a known
   closed-form criterion.

### 2.4 Theorem C (necessity and sufficiency for finite-dimensional exact renormalization) [P]

A family of local observables on a substitution geometry admits an exact finite-dimensional linear recursion over
the approximants iff the set of intrinsic local types (configurations within the observable's radius, modulo the
symmetry group under which the observable and the link rule are invariant) is finite. Sufficiency is Theorem A's
construction; necessity holds because the recursion state must determine all type counts. Finiteness follows from
finite local complexity modulo the symmetry group; it fails, for instance, for substitutions with irrational
relative rotations (pinwheel-type), where frequencies still exist by ergodicity but no finite exact recursion does.
The block-triangular structure by cell dimension, with PF eigenvalues $L^{d},L^{d-1},\dots$, requires in addition
a *block* (integer-expansion, cube-compatible) substitution; for Pisot-type substitutions (Penrose) the analogous
eigenvalues are $\lambda^d$ and its algebraic conjugates and the frequencies lie in $\mathbb Q(\lambda)$.

### 2.5 Relation to established mathematics

The existence and rationality of patch frequencies for primitive constant-length substitutions, via the
Perron–Frobenius eigenvector of a (collared) substitution matrix with integer eigenvalue, is classical (Dekking's
constant-length theory; Queffélec; Anderson–Putnam collared tiles; Baake–Grimm, *Aperiodic Order*). What Theorem A
and B add is specific: (i) gauge-invariant plaquette classes are local observables in this sense once the link rule
is intrinsic, so a non-abelian flux background inherits exact renormalizability; (ii) for supertile approximants the
recursion is an exact *boundary expansion* in $L^d,L^{d-1},L^{d-2}$ with no asymptotic remainder; (iii) the explicit
dichotomy between interface-stable decorations (pure powers of two, small denominators) and generic ones (algebraic
and complex eigenvalues) is, to our knowledge, not in the literature for decorated block substitutions. None of
this is new mathematics in the sense of new techniques; it is a precise specialization with a machine-checked
instance.

---

## 3. Phase III: from counting to dynamics

### 3.1 Operators

Hilbert space $\mathcal H_m=\ell^2(\text{tiles of }\mathcal T_m)\otimes\mathbb C^2$, standard inner product. Two
Hermitian operators built from the same link variables ($C_{ba}=C_{ab}^\dagger$):

- **Free** (degree-type): $H^{\rm free}_m=\sum_{e=(a,b)}\bigl(|a\rangle\langle a|+|b\rangle\langle b|\bigr)\otimes I-\bigl(|a\rangle\langle b|\otimes C_e+\mathrm{h.c.}\bigr)$,
  a sum of positive operators ($\ge0$). Tiles at the supertile boundary have fewer than 24 incident panels.
- **Pinned** (bulk coordination): $H^{\rm pin}_m=24\cdot\mathbb 1-\sum_e\bigl(|a\rangle\langle b|\otimes C_e+\mathrm{h.c.}\bigr)=H^{\rm free}_m+\operatorname{diag}(24-\deg)\ge H^{\rm free}_m$.
  In the infinite tiling every chair has exactly 24 shared panels, so $H^{\rm pin}_m$ is the compression of the
  infinite bulk operator $H_\infty=24-\mathcal A$ to $\mathcal H_m$ (missing neighbours act as hard walls).

Gauge law: $H\mapsto UHU^\dagger$ with $U=\bigoplus_aG_a$, $G_a\in SU(2)$; spectra are gauge invariant. Both are
Hermitian for any $SU(2)$-valued links; a non-Hermitian variant would require non-unitary links, which the Clifford
rule never produces. Dimensionless parameters: none (all couplings are $\pm1$ or $\pm i\sigma_k$; the only scale is
the hopping amplitude). Infinite-volume relation: by the min-max principle $\inf\operatorname{spec}H_\infty\le\lambda_{\min}(H^{\rm pin}_m)$
for all $m$, decreasing in $m$ along nested approximants; no such inequality holds for $H^{\rm free}_m$.

### 3.2 Result: the spectral bottom is a surface band [N]

`audit/results/phase5_dynamics_boundary.txt`:

| level | tiles | $\lambda_{\min}$ free | boundary weight of ground state | $\lambda_{\min}$ pinned | boundary weight (pinned) |
|---|---|---|---|---|---|
| 2 | 64 | 4.72646 | 0.929 | 10.77695 | 0.631 |
| 3 | 512 | 5.11494 | 0.928 | 9.37847 | 0.133 |
| 4 | 4096 | 5.20970 | 0.927 | 8.91963 | 0.007 |
| 5 | 32768 | 5.24993 | 0.926 | 8.79701 | 0.001 |

"Boundary weight" is the probability mass of the ground state on tiles with fewer than 24 panels; the fraction of
such tiles falls as 0.83, 0.56, 0.33, 0.18 while the weight stays at 0.93: the free ground state is a genuine
surface state, and the free $\lambda_{\min}\to\approx5.27$ is the bottom of a **surface band**, not the bulk
infimum. The pinned $\lambda_{\min}$ decreases monotonically (compression property) toward the bulk infimum
$E_{\rm bulk}$; the current bracket is $E_{\rm bulk}\le8.79701$, with the decrements $1.40,\ 0.46,\ 0.12$ (ratios $0.33,\ 0.27$)
suggesting $E_{\rm bulk}\approx8.75$ (level 6 by LOBPCG: see `audit/results/phase5_bulk_bottom_lobpcg.txt`). For the trivial connection the pinned values $4.75,1.67,0.50,\dots\to0$ with
ratios tending to $1/4$, the Dirichlet $L^{-2}$ law of an extended band edge; the Clifford ratios are
$0.33,\ 0.27$. Controls: random i.i.d. $Q_8$ links give a strongly localized free ground state (tile IPR
0.39 at level 4, boundary weight 0.99) and a pinned bottom near 14.7; a random admissible decoration gives free
$\lambda_{\min}=6.02$ at level 4 (Phase 2).

**Correction to Phase 2.** The statement there that $E_0\approx5.27$ is "the spectral bottom of the infinite
operator" was wrong: it is the bottom of the free-boundary surface band. The bulk statement is the pinned bracket.

### 3.3 Distinctions the data support

- **Spectral infimum** $E_{\rm bulk}=\inf\operatorname{spec}H_\infty$: exists, bounded above by the pinned values, numerically $\approx8.7$ [N]. It is positive because the $Q_8$ flux frustrates the uniform state ($H^{\rm free}\ge0$ with equality only for a flat connection).
- **Spectral gap**: $[0,E_{\rm bulk})$ is a gap of the bulk operator relative to the trivial connection's spectrum starting at 0; whether the bulk spectrum above $E_{\rm bulk}$ has further gaps is not established (no persistent gaps of relative width $>2\%$ at levels 3 and 4, Phase 2).
- **Mobility gap / localization**: the pinned ground state is extended (tile IPR $\approx9/n$), the free ground state is surface-localized, the random-$Q_8$ ground state is point-localized. No mobility-gap statement for the bulk is established.
- **Mass parameter / mass gap**: not applicable. There is no relativistic dispersion, Lorentz structure or field; $E_{\rm bulk}$ is a band bottom of a graph operator. Any identification with a mass would require an effective-mass continuum description (Section 4.3), which is not established.
- **Robustness**: the surface band and the bulk gap persist across levels 2 to 5 and across boundary conditions (the surface band is *created* by free boundaries, the bulk gap is independent of them); the numerical values depend on the decoration (random decoration: different) and on the full $Q_8$ structure (adjoint-only links shift the free $\lambda_{\min}$ by about 2% at level 4, Phase 2).

### 3.4 Theorem D (same limiting spectral measure for both boundary conditions) [P]

$H^{\rm pin}_m-H^{\rm free}_m=\operatorname{diag}(24-\deg)$ is supported on the boundary tiles, whose number $b_m$
satisfies $b_m/8^m\to0$ (0.83, 0.56, 0.33, 0.18 observed; bounded by the surface-to-volume ratio). By the rank
inequality for eigenvalue counting functions, the normalized integrated densities of states differ by at most
$2b_m/(2\cdot8^m)\to0$. Together with Phase 2 Theorem 2.6 (Cauchy property with rate $T_m/8^m$), both sequences
converge to the same $N_\infty$. The surface band therefore has zero weight in the limiting spectral measure; it is
visible only in the lowest finitely many states and in boundary-sensitive observables.

---

## 4. Phase IV: continuum limits

### 4.1 No-go theorem for a continuum gauge field [P, sharpened]

**Theorem E.** Let $\{U^{(m)}\}$ be any family of $SU(2)$ link fields on the approximants $\mathcal T_m$ whose
plaquette holonomy classes have the frequencies of Theorem A with non-trivial fraction $f_{\neq}=17/36$. Then for
any assignment of lattice spacings $a_m\to0$, the plaquette curvature density
$\rho_m=\#\{p:\operatorname{Tr}W_p\neq2\}/\#\{p\}\to17/36$ does not vanish, whereas convergence to a continuum
connection $A$ with curvature $F$ in the lattice-gauge sense requires $\operatorname{Tr}W_p=2-a_m^4|F|^2+o(a_m^4)\to2$
on all but a vanishing fraction of plaquettes. Hence no continuum $SU(2)$ connection is the limit of the Clifford
background under any rescaling. *Proof.* Immediate from the exact frequency (Theorem A) and the definition of the
continuum limit. $\square$ The obstruction is not finite-size; it is the exact frequency itself. The only continuum
description consistent with it is a topological one (a $Q_8$, or on vectors $\mathbb Z_2\times\mathbb Z_2$, flux
network with lattice-scale defect density), i.e. Dijkgraaf–Witten-type data, not Yang–Mills.

**Minimal modification removing the obstruction.** Replace the signed-axis normals by a smoothly varying frame field
with adjacent relative rotations $O(a)$; then (Phase 2, Proposition 2.4) $C_{ab}=I+a\,i\,(\omega_{ab})_\perp\cdot\boldsymbol\sigma+O(a^2)$
and the limit is the transverse part of the frame spin connection, a functional of the frame field with no
independent degrees of freedom. The block-substitution structure is incompatible with this (frames are in the finite
group $G$ at every level), so the modification abandons the substitution hierarchy.

### 4.2 Comparison of candidate limits

| Candidate limit | Status for the Clifford background |
|---|---|
| Effective periodic medium | excluded: the hull is limit-periodic, not periodic; plaquette frequencies are rational but the pattern is aperiodic |
| Homogenized continuum (effective-mass operator near the bulk bottom) | open; requires extended bulk band-edge states and IDS $\sim(E-E_{\rm bulk})^{3/2}$; level-4 local exponents are 1.03 to 1.22 (pinned), inconclusive at this resolution [N] |
| Scale-dependent / fractal effective operator | no evidence; IDS convergence rate is the surface ratio $2^{-m}$ for all models (Phase 2); no persistent gaps found |
| Nontrivial continuum gauge background | excluded by Theorem E |
| Trivial continuum (decorations disappear) | excluded: the flux density is exactly $17/36$ at every scale |

### 4.3 What a homogenization theorem would require

A statement of the form "the low-energy sector of $H_\infty$ is unitarily close to $E_{\rm bulk}-\nabla\cdot D\nabla$"
needs: (i) the bulk bottom to be attained by extended states (supported numerically by the pinned IPR), (ii) a
Bloch-like or two-scale convergence theory for limit-periodic operators (available in principle via the 2-adic
odometer structure of the chair hull), (iii) control of the surface band (Theorem D shows it is measure-zero).
None of this is done here; it is the first continuum-side obstacle (Section 11).

---

## 5. Phase V: the Lean certificate and the proof boundary

`certificates/TypeSubstitutionCertificate.lean` is generated by `audit/export_type_certificate.py` from
`audit/lean_template_type_substitution.lean` plus certificate data; the data are representatives, image index lists,
seed counts, the eigen-vectors $W_8,W_4,W_2,W_1$ (common denominator $D=64$) and the vectors $v_2,v_3$. **Every
datum is re-verified inside Lean**; nothing is assumed. The pipeline: (1) `phase4_type_substitution_proof.py`
derives the finite object independently; (2) `export_type_certificate.py` verifies invariants and exact counts in
exact arithmetic and (3) exports the certificate; (4) Lean checks it; (5) `tests/test_independent_audit_regression.py`
and the control scripts test it against independent implementations.

| Theorem (Lean name) | Content | Proof | Kernel status |
|---|---|---|---|
| `standard_level1_certified` | $\mathcal T_1$ has 56 distinct cubes filling $[0,4)^3\setminus[2,4)^3$; `idx1` is the correct child map | `decide +kernel` | verified (14 s, 0.7 GB) |
| `equivariance_certified` | for every tile occurring, children's cubes are the rigid image of the root's | `decide +kernel` | verified (35 s, 2.2 GB) |
| `types_distinct` | the 49 panel keys and 108 plaquette keys are pairwise distinct | `decide +kernel` | verified (37 s, 2.4 GB) |
| `panel_images_certified` | inflating each panel representative yields the certified 4+4 fine types | `decide +kernel` | verified (94 s, 5.6 GB) |
| `plaquette_images_certified` | inflating each plaquette representative yields the certified 2 fine types | `decide +kernel` | verified (93 s, 6.0 GB) |
| `classes_certified` | holonomy classes of representatives equal the certified classes | `decide +kernel` | verified (18 s, 1.0 GB) |
| `seed_certified` | $\mathcal T_1$ has the certified 48 panel-type and 60 plaquette-type counts | `decide +kernel` | verified (49 s, 3.3 GB) |
| `level1_geometry_matches_recursion` | enumerated class counts of $\mathcal T_1$ = recursion at $m=1$ | `decide +kernel` | verified (23 s, 1.2 GB) |
| `level2_geometry_matches_recursion` | enumerated class counts of $\mathcal T_2$ (448 cubes, 984 plaquettes) = recursion at $m=2$ | `decide +kernel` | verified (167 s, 11.3 GB) |
| `u1_check`, `u2_check` | $v_2=Sf+8f$, $v_3=Sv_2+64f$ | `decide +kernel` | verified (26 s, 1.9 GB), verified (27 s, 2.0 GB) |
| `eigen_check` | $SW_8+Df=8W_8$, $SW_4=4W_4$, $SW_2=2W_2$, $SW_1=W_1$ | `decide +kernel` | verified (44 s, 3.7 GB) |
| `base_check` | $Dv_3=512W_8+64W_4+8W_2+W_1$ | `decide +kernel` | verified (17 s, 1.2 GB) |
| `closed_form_all` | $\forall m\ge3:\ D v_m=8^mW_8+4^mW_4+2^mW_2+W_1$ | induction + fold lemmas | depends on the checks above |
| `class_counts_closed_form`, `total_closed_form` | exact finite-size law for every class and for $N_m$ | from `closed_form_all` | same |
| `limit_frequencies` | $\sum W_8=18D$, $\sum W_4=-24D$, $\sum W_2=6D$, $\sum W_1=0$; $36\,W_8(+1)=19\sum W_8$, $144\,W_8(-1)=13\sum W_8$, $9\,W_8(i)=\sum W_8$, $144\,W_8(j)=23\sum W_8$, $9\,W_8(k)=\sum W_8$ | `decide +kernel` | verified (17 s, 1.1 GB) |

**Kernel run record.** Each `decide +kernel` theorem was checked by the Lean 4.34.1 kernel in its own file (all other
checks temporarily replaced by `native_decide` so that only the named theorem is kernel-evaluated); times and peak
resident memory are listed above (`run_monitored.py`, log reproduced in `audit/results/phase5_lean_kernel_runs.txt`).
All fourteen checks passed. The hand-written proofs (`closed_form_all` and its consequences) typecheck in the same
files. A single-process compilation of the whole certificate requires roughly the sum of the peaks because the kernel
caches persist within one process; its outcome is recorded in Section 9.

**Proof boundary.** Formal: the finite type system is derived from the substitution rule (not pasted), the recursion
is defined from certified image lists that Lean re-derives, and the closed form for *all* $m\ge3$ is a theorem whose
only inputs are the kernel-checked identities and three elementary fold lemmas (`foldl_add_split`, `foldl_smul`,
`foldl_congr_mem`). Paper: the parity-trichotomy decomposition (Section 2.2, item 3) and the general equivariance
lemma, which identify the geometric plaquette counts of $\mathcal T_m$ with the recursion for all $m$; Lean verifies
this identification at $m=1$ and $m=2$ from the geometry. No axiom beyond `propext`, `Quot.sound`,
`Classical.choice` is used; `native_decide` is not used in the certificate.

---

## 6. Phase VI: an experimental realization

**Platform.** A passive linear network (topolectrical circuit or coupled acoustic/photonic resonators) implementing
the hopping operator of Section 3.1 as a circuit Laplacian. Because $Q_8\subset\mathbb H$ acts on the quaternions by
left multiplication as *real orthogonal signed permutation matrices* of $\mathbb R^4$, every link $C_e$ can be
implemented with real couplings of magnitude 1 and definite sign:
$$\pm1\mapsto\pm I_4,\qquad \pm i\mapsto\pm\begin{pmatrix}0&-1&0&0\\1&0&0&0\\0&0&0&-1\\0&0&1&0\end{pmatrix},\quad\text{and similarly }\pm j,\pm k.$$
The real $4n\times4n$ operator has the spectrum of the complex $2n\times2n$ one with every eigenvalue doubled.

- **Unit cell.** One tile = one node cluster of 4 identical resonators (the four real components of a quaternion).
  Tiles are placed on the FR30 level-$k$ supertile; the assembly rule is the substitution of Section 2.1, so the
  level-$(k+1)$ sample is eight rotated copies of the level-$k$ sample plus the inter-child couplings, which is
  exactly what Theorem A counts.
- **Couplings.** Each shared unit panel between tiles $a,b$ contributes one 4-wire bundle realizing the signed
  permutation of $C_{ab}$: a wire ($+1$) or an inverting coupler ($-1$) between the appropriate component pairs.
  In LC networks a sign is realized by choosing capacitive versus inductive coupling at the operating frequency;
  with 24 shared panels per bulk tile, a bulk tile has 24 bundles. Multiplicity (several panels between the same
  pair) adds in parallel.
- **Operator.** With free terminations, the circuit Laplacian equals $H^{\rm free}$ of Section 3.1 (up to the
  quaternion doubling); grounding every tile through a fixed admittance equal to $24-\deg$ realizes $H^{\rm pin}$.
- **Observable.** The admittance (or acoustic/photonic transmission) spectrum, i.e. the eigenvalues of the
  Laplacian in units of the panel coupling, measured by impedance spectroscopy; and spatial maps of the lowest
  modes.
- **Predicted signatures** (units: panel coupling), from Section 3.2 and Phase 2:

| level | tiles (nodes) | free $\lambda_{\min}$ | pinned $\lambda_{\min}$ | free ground state boundary weight | untwisted control | random-decoration control (free) |
|---|---|---|---|---|---|---|
| 2 | 64 (256) | 4.726 | 10.777 | 0.93 | 0 | 5.393 |
| 3 | 512 (2048) | 5.115 | 9.378 | 0.93 | 0 | 5.813 |
| 4 | 4096 (16384) | 5.210 | 8.920 | 0.93 | 0 | 6.018 |

  Decisive null tests: the untwisted network (all bundles $+I_4$) has $\lambda_{\min}=0$ and the plain weighted
  Laplacian spectrum; the mirror-reflected sample has an identical spectrum (gauge equivalence, Phase 2 Theorem 2.4;
  checked numerically to $10^{-12}$ at levels 2 and 3 in `audit/results/phase5_cube_control_spectrum.txt`); a random
  admissible decoration shifts the free bottom by $+14\%$ at level 2; i.i.d. random $Q_8$ bundles give 8.44 and a
  point-localized ground state; the alternative substitution (unit-cube geometry with the same decoration rule)
  gives the values recorded in `audit/results/phase5_cube_control_spectrum.txt`.
- **Smallest discriminating system.** Level 2 (64 tiles, 256 resonators, 576 bundles) already separates the free
  bottom (4.73) from the untwisted value (0), from the random decoration (5.39) and from random bundles (8.44) by
  far more than any plausible fabrication tolerance; level 3 (2048 resonators) is needed to see the surface band
  versus bulk distinction (pinned bottom 9.38 vs free 5.11) converge.
- **$Q_8$ versus adjoint quotient.** The real-4-component construction realizes the full spinor structure by design,
  and the spectrum is sensitive to it: stripping the central signs ("adjoint-only") moves the free bottom from
  4.726 to 4.225 at level 2 and from 5.210 to 5.114 at level 4 (Phase 2), a 10% and a 2% effect. A loop-resolved
  test isolates the $\mathbb Z_2$ extension directly: on an inter-tile plaquette with $W=-I$ (13/144 of all
  inter-tile plaquettes in the limit; 3 of 60 at level 1, located by the certificate), a signal injected into the
  4-component cluster of one tile and recombined after the two half-loops interferes destructively, whereas a
  vector (adjoint) probe sees trivial holonomy there.
- **Finite-size scaling and uncertainty.** All quoted eigenvalues are exact to the displayed digits for the ideal
  network; fabrication disorder enters as random link perturbations, whose effect must be measured, not assumed.
  The scaling of the free bottom ($4.726,5.115,5.210,5.250$) converges geometrically (ratio $\approx0.42$) and the
  pinned bottom decreases toward $E_{\rm bulk}$; a level-4 sample determines both to about 1%.
- **Parameters requiring external measurement.** Coupling strength and its uniformity, loss (quality factor), and
  the achievable sign fidelity of inverting couplers. No values are assumed here.

What this experiment tests is the *model*: that a real passive network with these couplings has these spectra. It
does not test a theory of fundamental interactions, and the document makes no such claim.

---

## 7. Phase VII: universality across geometries and decorations

| System | types (panel, plaquette) | nonzero $\operatorname{spec}M$ | nonzero $\operatorname{spec}B$ | $\lim N_m/8^m$ | classes present | $f(+1)$ |
|---|---|---|---|---|---|---|
| chair / FR30 | 49, 108 | $\{4,1\}$ | $\{2,1\}$ | 18 | all five | 19/36 |
| chair / achiral ($D_s$ only) | 51, 117 | $\{4,1\}$ | $\{2,1\}$ | 18 | $\{\pm1\}$ only | 3/4 |
| chair / canonical homochiral | 42, 93 | $\{4,1\}$ | $\{2,1\}$ | 18 | $1,-1,i$ | 181/288 |
| chair / random decorations (6) | 77 to 90, 234 to 273 | 4, 2, 1 and roots of $\lambda^2+\lambda+1$, $\lambda^2+\lambda-4$, $\lambda^3-2\lambda^2-7\lambda+6$, $\lambda^2-2$, … | 2, 1, $-1$, roots of $\lambda^2+\lambda+1$, $\lambda^3-\lambda^2-\lambda-1$, … | 18 | all five | e.g. 50209/98112 |
| unit cube (periodic geometry) / FR30-type decoration | 10, 16 | $\{4,1\}$ | $\{2,1\}$ | 3 | all five | 1/7 |
| unit cube / random decoration | 12, 54 | 4, 1, roots of $\lambda^2-2\lambda+2$, $\lambda^2+3\lambda+4$ | 2, roots of $\lambda^2-\lambda+1$, … | 3 | all five | 28879/201600 |
| unit cube / achiral | 6, 12 | $\{4\}$ | $\{2\}$ | 3 | $\{+1\}$ only (flat) | 1 |

Classification:

- **Universal consequences of the assumptions** (Theorems A to C): finite type closure; exact linear recursion;
  forcing eigenvalue $L^d$ and PF eigenvalues $L^{d-1}$, $L^{d-2}$; rational limiting frequencies; $O(L^{-m})$
  surface scaling of finite-size corrections; convergence of the spectral measure with rate bounded by the
  interface-tile fraction.
- **Specific to the Chair44 geometry**: the numbers 48, 60, $\lim N_m/8^m=18$, $N_m=18\cdot8^m-24\cdot4^m+6\cdot2^m$.
- **Specific to the FR30 decoration**: the clean spectrum $\{4,2,1,0\}$ (shared with some but not most
  decorations), the frequencies 19/36, 13/144, 1/9, 23/144, 1/9, the surface-band and bulk values of Section 3.
- **Specific to the $Q_8$ transport rule**: the class structure (five classes, $\mathbb Z_2\times\mathbb Z_2$ adjoint,
  $\mathbb Z_2$ spinor extension), parity invariance, non-flatness for all admissible decorations.
- **Not a consequence of aperiodic geometry**: the unit-cube control reproduces the entire structure (clean spectrum
  included) on a periodic lattice; what matters is that the *decoration* is a self-reproducing substitution.
- **Artifacts of finite size or observable**: the free-boundary spectral bottom (surface band); the signed
  plaquette labels (not inherited; only classes are).

**Instability under small admissible changes.** Changing a single tile's permutation changes the flux vector
(Phase 2 counterexample) and, generically, introduces non-clean eigenvalues; the exact limiting frequencies move by
$O(1)$ (e.g. $f(+1)$ from 0.528 to 0.512 to 0.573 across random decorations). The phenomenon that is stable is the
*form* of the law (Theorem A), not the numbers.

---

## 8. Phase VIII: the chosen advance and its justification

Chosen direction: a general theorem with complete proof (Section 2) tied to a Lean certificate of its central
instance (Section 5), with the dynamics correction (Section 3) and the universality census (Section 7) as the
adversarial controls. This connects priority levels 1 and 2 of the brief, and feeds level 4 (Section 6).

Why it is not a restatement of standard substitution theory: standard theory gives existence and rationality of
frequencies; here the recursion is written as an exact boundary expansion with identified universal eigenvalues,
the observable is a non-abelian gauge holonomy class whose inheritance under inflation is itself a (proved)
statement about conjugacy classes, the finite computational core is kernel-checked rather than trusted, and the
census shows that the clean spectrum is a property of a small class of decorations, which the general theory does
not predict. Where the result is a specialization of known theory, Section 2.5 says so.

---

## 9. Phase IX: repository changes and verification

Interim commit of this phase (final numbers for the level-6 bulk bottom, the unit-cube control spectra and the
single-process Lean compilation are appended in the follow-up commit recorded at the end of this section).

**New files.** `audit/export_type_certificate.py`, `audit/lean_template_type_substitution.lean`,
`certificates/TypeSubstitutionCertificate.lean` (generated), `audit/phase5_dynamics_boundary.py`,
`audit/phase5_bulk_bottom_lobpcg.py`, `audit/phase5_universality_types.py`, `audit/phase5_closure_vs_spectrum.py`,
`audit/phase5_cube_control_spectrum.py`, `audit/results/phase5_*.txt`, `audit/results/level4_clifford_{free,pinned}_eigs.npy`,
this document. **Modified.** `tests/test_independent_audit_regression.py` (four Phase V tests),
`deliverables/CLIFFORD_Q8_PHASE2_RESEARCH.md` (Section 10 correction).

**Tests.** `python3 -m unittest tests/test_independent_audit_regression.py`: 16 tests, all passing (40 s).
`python3 -m pytest tests/test_chair44.py tests/test_adversarial_chair44.py`: 35 passed, 1 failed (the pre-existing
$7\times10^{-12}$ floating-point tolerance failure in `test_03_supersymmetry_trace_cancellation_generalized`).

**Unavailable or limited.** Mathlib (not used; all proofs are core Lean); `/usr/bin/time` (replaced by a Python RSS
monitor); the shift-invert eigensolver at level 5 for six operator variants exceeded the memory budget and was replaced
by matrix-free LOBPCG, which reproduces the level-4 dense values to all printed digits.

---

## 10. Claim ledger

| Claim | Status |
|---|---|
| Theorem A (finite closure, exact recursion) for the FR30 chair | proved [P]; finite core kernel-checked [K]; geometric identification kernel-checked at $m=1,2$ [K], exact-arithmetic checked at $m=3..7$ [E] |
| Theorem B.1 (universal eigenvalues $8,4,2$; rational limits) | proved [P] |
| Theorem B.2–B.3 (non-universality; no closure criterion) | computational, exact arithmetic [E]; 9 chair + 3 cube decorations + 30 low-$\lvert P_0\rvert$ + 12 sampled |
| Theorem C (iff for finite-dimensional exact renormalization) | proved [P] (elementary) |
| Closed form $64v_m=8^mW_8+4^mW_4+2^mW_2+W_1$, $m\ge3$ | formally verified [K] for the recursion; identification with geometry as above |
| Limiting frequencies 19/36, 13/144, 1/9, 23/144, 1/9 | formally verified [K] as identities of the certified eigenvector; limit interpretation [P] |
| Theorem D (same limiting spectral measure, free vs pinned) | proved [P] |
| Theorem E (no continuum gauge field) | proved [P] |
| Free spectral bottom $\to5.27$ is a surface band; bulk infimum $\le8.92$ (level 4) | numerical [N], levels 2 to 5 |
| Bulk ground state extended; random-$Q_8$ ground state localized | numerical [N], IPR |
| Homogenized effective-mass continuum near $E_{\rm bulk}$ | conjectural; level-4 IDS exponents inconclusive |
| Experimental signatures of Section 6 | physically untested [H]; numbers exact for the ideal model |
| Phase 2 claim "$E_0\approx5.27$ is the infinite-operator spectral bottom" | **falsified** (surface band) |
| Monograph cycle table, Spin(4) obstruction, soldered mass gap, $\lambda_{\min}=2.6687$, input cosmology parameters | falsified in the audit; unchanged |
| $\lvert P^*\rvert=44$, $\lvert F^*\rvert=135$, aperiodicity of FR30 | external, unverified |

---

## 11. The next mathematical obstacle

The continuum side is now the frontier. The exact flux frequencies rule out a continuum gauge field (Theorem E), and
the spectral measure converges (Theorem D), but the *low-energy effective operator* of the bulk is not identified.
The concrete obstacle is a two-scale (homogenization) theorem for the limit-periodic operator $H_\infty=24-\mathcal A$
on the chair hull: prove that the bulk band edge $E_{\rm bulk}$ is attained by extended states and that
$H_\infty-E_{\rm bulk}$ is, at long wavelength, an effective-mass operator with a computable tensor. The 2-adic
odometer structure of the chair hull makes this plausible (periodic approximants of period $2^k$ exist at every
scale), and it would turn the bulk gap into a derived continuum statement rather than a numerical bracket. A second,
purely combinatorial obstacle is a closed-form criterion for interface stability (clean spectrum) among the 6561
decorations; Section 2.3 shows the natural candidate, contact-language size, fails.
