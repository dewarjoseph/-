# What the Verified Structure Permits: The Chair44 Clifford $Q_8$ Background as a Mathematical Object

This document continues from `deliverables/CLIFFORD_Q8_END_TO_END_AUDIT.md`. It does not repeat that audit. It
takes the surviving objects, reproduces the one result on which any physical reading depends, and then determines,
by proof and by controlled computation, exactly what theory those objects support. Every number below was produced
by the scripts in `audit/` (which do not import `src/`), with outputs saved under `audit/results/`, or by the Lean
file `certificates/Chair44GeometryToMatrix.lean`.

## 0. Result in one paragraph

The surviving structure is a frozen, decoration-determined $Q_8$ flux background on a primitive constant-length
substitution tiling. Three things about it are now established that were not before. (i) Non-trivial holonomy is a
property of the Clifford rule on the chair substitution, not of the FR30 decoration: all 6561 parity-admissible
homochiral decorations give non-flat connections at level 1 (6552 with holonomy group $Q_8$, 9 with an order-4
subgroup, none flat), and FR30 is unexceptional among them. (ii) On vector matter the connection reduces exactly to
an abelian Klein-group ($\mathbb Z_2\times\mathbb Z_2$) flux; the non-abelian content is a $\mathbb Z_2$ central
extension seen only by spinors; Wilson-loop traces are invariant under mirror reflection of the tiling, so the
background carries no chirality. (iii) The gauge-invariant plaquette curvature obeys an exact inheritance recursion
across the hierarchy (proved), its boundary terms follow closed forms verified at levels 3 to 7 with two
out-of-sample confirmations, and the implied limiting frequencies are the exact rationals
$19/36,\ 13/144,\ 1/9,\ 23/144,\ 1/9$ for the classes $\{+1\},\{-1\},\{\pm i\},\{\pm j\},\{\pm k\}$; the normalized
spectral measure of the associated hopping operator converges with a proved rate, and its spectral bottom converges
numerically to $E_0\approx5.27$ against $0$ for the trivial connection. What the structure does not permit is any
gauge dynamics, continuum limit, chirality, matter content, or coupling: those must be added as a new model, and
nothing in the geometry constrains them.

---

## 1. Phase 1: reproduction record

**Environment.** Linux 6.18.44, Python 3.13.16, numpy 2.5.3, scipy 1.18.1, sympy 1.14.0, Lean 4.34.1 (release
binary, commit 5045d005). Repository head at start: `d1d26d4`.

**Commands and outcomes** (all run from the repository root):

| Command | Outcome |
|---|---|
| `python3 -I audit/independent_clifford_q8_audit.py` | exact supertiles at levels 1 to 3; $L$ and its characteristic polynomial; 48 links in $Q_8$ (24 equal $-I$); $b_1=41,513,4865$; $\mathrm{Hol}=Q_8$ at levels 1 to 3; Kramers pairs; exact $P(\lambda)^2$ |
| `python3 -I audit/phase2_structure_census.py` | 6561-decoration census, adjoint reduction, mirror test, cycle-count reconciliation (`audit/results/phase2_structure_census.txt`) |
| `python3 -I audit/phase3_plaquette_recursion.py 5` | class-level inheritance exact at levels 2 to 5; $N_k,B_k$ closed forms; rigorous limit bounds (`audit/results/phase3_plaquette_recursion_levels1-5.txt`) |
| `python3 -u -I audit/phase3_level6_straddle.py 3 4 5 6 7` | straddling class counts to level 7 (37.4 M plaquettes), closed forms match at every level (`audit/results/phase3_straddle_closed_form_levels3-7.txt`) |
| `python3 -I audit/phase3_spectral_convergence.py 4` (+ level-5 shift-invert) | spectra of five models to dimension 8192, Kolmogorov distances, gap scan, $\lambda_{\min}$ to level 5 (`audit/results/phase3_spectral_convergence_levels1-5.txt`) |
| `lean certificates/Chair44GeometryToMatrix.lean` | 0 errors; four theorems, axioms `[propext]` only |
| `python3 -m unittest tests/test_independent_audit_regression.py` | 11 tests OK (2.4 s) |
| `python3 -m pytest tests/test_chair44.py tests/test_adversarial_chair44.py` | 35 passed, 1 failed (the pre-existing $7\times10^{-12}$ tolerance failure) |

**The single most consequential result, reproduced.** Any physical reading rests on the connection being a genuine
non-flat $Q_8$ configuration rather than pure gauge. Reproduced independently: at level 1 the 41 fundamental cycles
realize all eight elements of $Q_8$, 60 inter-tile canonical plaquettes carry $26$ trivial, $3$ central and $31$
traceless holonomies, and the Lean file below derives these same counts from the substitution rule inside the
kernel. The result holds and is the starting point for everything else.

**Cycle-count reconciliation (audit finding re-examined).** The monograph's "48 / 416 / 3424 cycles" matches none
of the natural graphs: panel multigraph $b_1 = 41, 513, 4865$; simple tile graph $b_1=9,120,1152$; cube graph
$b_1=65,705,6401$; directed panel edges $96,1152,10752$. At level 1 the published "cycles" equals the number of
panels, not the cyclomatic number. No boundary, orientation or basis convention produces the published triple.
Verdict: error, not convention.

**Lean certificates re-examined.** The two stored-constant files prove abstract propositions (telescoping,
covariance over any group) and arithmetic about pasted matrices. The new file
`certificates/Chair44GeometryToMatrix.lean` closes the gap they left: it defines the seven-cube chair, the eight
FR30 child poses, computes the 56 cubes and 48 shared panels, derives the $8\times8$ contact Laplacian, computes
every link as an integer quaternion, and evaluates the 60 inter-tile plaquette holonomies, all by `decide`. Its
four theorems (`level1_geometry`, `level1_laplacian_from_geometry`, `level1_links_in_Q8`,
`level1_plaquette_curvature`) depend on `propext` only. This is the first machine-checked statement in the
repository that connects geometry to the matrices.

---

## 2. Phase 2: the mathematical model

### 2.1 Specification

- **Prototile and substitution.** $C_3=[0,2]^3\setminus(1,2]^3$ with cubes indexed by
  $U_3=\{0,1\}^3\setminus\{(1,1,1)\}$. A pose is $(G,\mathbf T)\in SO(3,\mathbb Z)\ltimes\mathbb Z^3$ (doubled
  coordinates). Inflation $\sigma$: $(G,\mathbf T)\mapsto(G\pi_0,\,2\mathbf T+G\mathbf 1)$ and
  $(G\,D_s(\mathbf v)\pi_{\mathbf v},\,2\mathbf T+4G\mathbf v)$, $\mathbf v\in U_3$. The level-$k$ approximant
  $\mathcal T_k=\sigma^k(I,\mathbf 0)$ has $8^k$ tiles and is the chair of side $2^{k+1}$ (verified $k\le5$).
- **Decoration.** A map $\pi:\{0\}\cup U_3\to S_3$ with $\operatorname{sgn}\pi_{\mathbf v}=(-1)^{|\mathbf v|}$,
  $\operatorname{sgn}\pi_0=+1$. There are $3^8=6561$ admissible decorations; FR30 is one. Because $C_3$ is
  $S_3$-invariant, the point set $\mathcal T_k$ is the same for all decorations; only the frames differ.
- **Panel multigraph $\Gamma_k$.** Vertices: tiles. One edge per shared unit square, with ambient normal
  $\mathbf n_f$ directed from $a$ to $b$. $|V_k|=8^k$, $|E_k|=48\cdot 12^{k-1}$ (verified $k\le3$: 48, 576, 5376).
- **Link variables.** $C^{(f)}_{ab}=(\boldsymbol\sigma\cdot M_a^\top\mathbf n_f)(\boldsymbol\sigma\cdot M_b^\top\mathbf n_f)\in Q_8$,
  $C_{ba}=C_{ab}^{\dagger}$. Gauge transformations: $C_{ab}\mapsto G_aC_{ab}G_b^{-1}$, $G\in SU(2)$.
- **Observables.** Wilson loops $W(\gamma)$ up to conjugacy; canonical plaquettes: the four unit cubes around a
  lattice edge, with link $I$ inside a tile; a plaquette is *inter-tile* if its cubes lie in at least two tiles.
  The gauge-invariant datum of a plaquette is the conjugacy class of $W\in Q_8$, one of
  $\{+1\},\{-1\},\{\pm i\},\{\pm j\},\{\pm k\}$; the sign inside a non-central class depends on orientation and
  base point and is not an invariant.
- **Hopping operator.** $H_k=\sum_{e=(a,b)}\bigl(|a\rangle\langle a|+|b\rangle\langle b|\bigr)\otimes I-\bigl(|a\rangle\langle b|\otimes C_e+\mathrm{h.c.}\bigr)$
  on $\mathbb C^{8^k}\otimes\mathbb C^2$; normalized integrated density of states $N_k(E)=\#\{\lambda\le E\}/(2\cdot8^k)$.

### 2.2 Theorems (proved here)

**Theorem 2.1 (link classification).** With $V_{ab}=M_a^\top M_b$ and $\mathbf u_b=M_b^\top\mathbf n_f$:
$C_{ab}=+I$ iff $V_{ab}\mathbf u_b=\mathbf u_b$; $C_{ab}=-I$ iff $V_{ab}\mathbf u_b=-\mathbf u_b$; otherwise
$C_{ab}=\pm i\sigma_m$ with $\mathbf e_m\parallel\mathbf u_a\times\mathbf u_b$. *Proof.* $\mathbf u_a=V_{ab}\mathbf u_b$
and the Pauli identity. $\square$ (At level 1: 6, 24, 18 links respectively, machine-checked.)

**Theorem 2.2 (adjoint reduction).** Let $O\cong S_4$ be the octahedral group and $V_4\lhd O$ its Klein subgroup
of $\pi$-rotations about coordinate axes. In the ambient gauge $G_a=U_a$ (spin lifts of $M_a$), the adjoint
connection is $\mathrm{Ad}(C'_{ab})=R_{\mathbf n_f}(\pi)\,M_aM_b^\top\,R_{\mathbf n_f}(\pi)=M_aM_b^\top\cdot k_{ab}$
with $k_{ab}=R_{M_bM_a^\top\mathbf n_f}(\pi)R_{\mathbf n_f}(\pi)\in V_4$. Consequently: the adjoint connection is
an $O$-connection whose image in $O/V_4\cong S_3$ is the coboundary of the frames (flat), its holonomy lies in the
abelian group $V_4$, and on vector (spin-1) matter the Clifford background is a $\mathbb Z_2\times\mathbb Z_2$
flux. *Proof.* $R_{\mathbf n}VR_{\mathbf n}=V\,(V^{-1}R_{\mathbf n}V)R_{\mathbf n}=V\,R_{V^{-1}\mathbf n}R_{\mathbf n}$,
and $V^{-1}\mathbf n$ is a signed axis because $V\in O$. $\square$ (Checked on all 48 links; adjoint holonomy image
has order 4.)

**Theorem 2.3 (spinor content is a central extension).** $Q_8\to V_4$ has kernel $\{\pm I\}$, so the full
connection is a lift of the $V_4$ flux to the non-split extension $Q_8$. Loops with trivial adjoint holonomy can
carry $W=-I$; these occur (1 of 41 fundamental cycles, 3 of 60 plaquettes at level 1). The sign on such loops is
a well-defined invariant (independent of the choice of spin lifts $\pm U_a$, since $C$ is quadratic in each lift).
This is the precise sense in which the background is "non-abelian": it acts non-abelianly only on spinors.

**Theorem 2.4 (parity invariance).** Let $P=\operatorname{diag}(-1,1,1)$ and reflect the tiling,
$M_a\mapsto PM_aP$, cubes $c\mapsto Pc-\mathbf e_1$. The reflected links are $\sigma_1C_{ab}\sigma_1$ on
corresponding panels. Hence all Wilson-loop traces and plaquette classes are identical for the tiling and its
mirror image. *Proof.* $\boldsymbol\sigma\cdot(P\mathbf u)=-\sigma_1(\boldsymbol\sigma\cdot\mathbf u)\sigma_1$;
the two minus signs cancel in the product. $\square$ (Checked: all 48 links; plaquette trace multisets equal at
levels 1 and 2. The fundamental-cycle *label* multisets differ because the spanning tree differs, which is a
further demonstration that per-cycle label statistics are not invariants.)

**Theorem 2.5 (exact inheritance of plaquette classes).** Let $\mathrm{Count}_k(c)$ be the number of inter-tile
canonical plaquettes of $\mathcal T_k$ in conjugacy class $c$, and $b_k(c)$ the number of those whose four cubes
lie in at least two of the eight level-$(k-1)$ children. Then for $k\ge2$
$$\mathrm{Count}_k(c)=8\,\mathrm{Count}_{k-1}(c)+b_k(c).$$
*Proof.* $\mathcal T_k$ is the union of eight children $G_c\mathcal T_{k-1}+\mathbf t_c$. Inside a child the tile
frames are $G_cM$ and the panel normals $G_c\mathbf n$, so the local normals $M^\top\mathbf n$ and therefore the
link quaternions are literally unchanged. A plaquette interior to a child corresponds to a plaquette of
$\mathcal T_{k-1}$ traversed with possibly reversed orientation and a different base point, so its holonomy is
conjugate to $W$ or $W^{-1}$, which lies in the same class ($Q_8$ classes are closed under inversion). Every
inter-tile plaquette is either interior to one child or straddles children. $\square$ (Verified exactly for the
five classes at levels 2 to 5; the signed labels are *not* inherited, as predicted.)

**Theorem 2.6 (convergence of the spectral measure with explicit rate).** Let $T_k$ be the number of tiles of
$\mathcal T_k$ incident to a panel joining two different children. Then for every $E$,
$$|N_k(E)-N_{k-1}(E)|\le T_k/8^k,$$
and $N_k$ converges uniformly to a distribution function $N_\infty$ with $\|N_k-N_\infty\|_\infty\le\sum_{j>k}T_j/8^j$.
*Proof.* By the invariance in Theorem 2.5, $H_k=\bigoplus_{c}H_{k-1}^{(c)}+K$ with each $H^{(c)}_{k-1}$ unitarily
equivalent to $H_{k-1}$ and $K$ (interface degree terms and interface hoppings) supported on the $2T_k$-dimensional
span of the spinor components of interface tiles, so $\operatorname{rank}K\le2T_k$. Eigenvalue counting functions
of Hermitian matrices differing by rank $r$ differ by at most $r$. Divide by $2\cdot8^k$. Since
$T_k\le2\times(\text{interface squares})=24\cdot4^k$, the series converges geometrically. $\square$
Measured $T_k=8,53,269,1277,5597$ (ratios tending to 4), so the actual increments are far below the crude bound;
measured $d_K(N_{k},N_{k+1})=0.359,0.170,0.075$ for $k=1,2,3$, ratio $\approx0.45$ per level.

### 2.3 What depends on the tiling and what on the decoration (census)

All $3^8=6561$ admissible decorations were enumerated at level 1 (`phase2_structure_census.py`, 353 s):

| Quantity | Result |
|---|---|
| Decorations with flat connection | 0 |
| Holonomy group $=Q_8$ | 6552; order-4 subgroup: 9 |
| Non-trivial inter-tile plaquette fraction | min 41.7%, median 53.3%, max 61.7%; FR30 56.7% (77th percentile) |
| $\lvert P_0\rvert$ at level 2 | ranges 26 to 54; FR30 $=30$ attained by 15 decorations; minimum 26 attained by 3 |

Conclusions. Non-flatness is forced by the chair substitution plus the Clifford rule and is independent of the
decoration; the *amount* and *pattern* of flux is a decoration property; FR30 is distinguished by neither. The
repository's statement that FR30's $|P_0|=30$ is a certified minimum is not what the census shows at level 2 (the
closure criterion attributed to Kamenetsky, if different, is not implemented anywhere and cannot be checked here).

### 2.4 Does the hierarchy produce anything beyond graph topology, finite-group holonomy, or boundary effects?

Yes, in one precise sense and no in another. The flux statistics are not boundary artifacts: they converge to exact
rationals determined by a self-similar recursion (Section 3.2), which is a hierarchical property of the
substitution. Spectrally, however, every measured convergence rate is $\approx2^{-k}$, exactly the surface-to-volume
ratio, for all five models alike; no persistent spectral gaps appear at levels $\ge3$ (threshold 2% of the range)
for the Clifford model or any control; and the Clifford spectral measure differs from that of the trivial
connection by $d_K=0.053$ and from the adjoint-only model by $0.019$ at level 4. The hierarchy is therefore visible
in the flux frequencies and in the lifted spectral bottom, not in any Cantor-like or log-periodic spectral
structure at the resolutions reached.

---

## 3. Phase 3: limits

### 3.1 Scale and approximants

The natural scale is the level $k$: $\mathcal T_k$ is a chair of side $2^{k+1}$ with $8^k$ tiles. Links are fixed
elements of $Q_8$ at every level; the geodesic distance of every link from $I$ is $0,\pi/2$ or $\pi$ at every level
(by Theorem 2.1 the three cases are decided by integer vector identities that do not depend on $k$). No sequence of
Lie-algebra-valued connections $A^{(k)}$ with $C_e=\exp(a_kA_e)$, $a_k\to0$ exists. The limiting description is not
a continuum connection but (i) a limiting flux-frequency vector and (ii) a limiting spectral measure. Both exist.

### 3.2 Exact flux frequencies

Counts measured directly (levels 1 to 5 by full enumeration, 6 and 7 by interface enumeration):

| $k$ | $N_k$ inter-tile plaquettes | $B_k$ straddling | $b_k(+1)$ | $b_k(-1)$ | $b_k(\pm j)$ | $b_k(\pm i)$ | $b_k(\pm k)$ |
|---|---|---|---|---|---|---|---|
| 1 | 60 | 60 | 26 | 3 | 7 | 12 | 12 |
| 2 | 792 | 312 | 177 | 18 | 61 | 28 | 28 |
| 3 | 7 728 | 1 392 | 865 | 194 | 277 | 28 | 28 |
| 4 | 67 680 | 5 856 | 3 601 | 1 154 | 1 045 | 28 | 28 |
| 5 | 565 440 | 24 000 | 14 833 | 4 994 | 4 117 | 28 | 28 |
| 6 | 4 620 672 | 97 152 | 60 337 | 20 354 | 16 405 | 28 | 28 |
| 7 | 37 356 288 | 390 912 | 243 505 | 81 794 | 65 557 | 28 | 28 |

**Proposition 3.1 (closed forms; verified $k\le7$, two of them out of sample).**
$N_k=18\cdot8^k-24\cdot4^k+6\cdot2^k$ and $B_k=24\cdot4^k-18\cdot2^k$ for $k\ge1$; for $k\ge3$,
$b_k(+1)=15\cdot4^k-18\cdot2^k+49$, $b_k(-1)=5\cdot4^k-126$, $b_k(\pm j)=4\cdot4^k+21$, $b_k(\pm i)=b_k(\pm k)=28$.
The class forms were fitted on $k=3,4,5$ and then predicted the measured values at $k=6$ (60 337 / 20 354 / 16 405
/ 28 / 28) and $k=7$ (243 505 / 81 794 / 65 557 / 28 / 28) exactly; their coefficients sum to those of $B_k$ and
their constants sum to zero, as they must. Status: conjecture with strong evidence; a proof requires showing that the
inter-child interface pattern of $\mathcal T_k$ is the level-3 pattern scaled, which is plausible from the
constant-length substitution but is not written here.

**Corollary 3.2 (exact limits, conditional on Proposition 3.1).** Solving the recursion of Theorem 2.5 with these
boundary terms, $\mathrm{Count}_k(c)=A_c8^k+B_c4^k+C_c2^k+D_c$ with $A_c$ fixed by the level-3 counts, and
$f_\infty(c)=A_c/18$:
$$f(+1)=\tfrac{19}{36},\quad f(-1)=\tfrac{13}{144},\quad f(\pm i)=f(\pm k)=\tfrac19,\quad f(\pm j)=\tfrac{23}{144};$$
non-trivial fraction $17/36=0.4722$, traceless fraction $55/144=0.3819$. The $\pm i,\pm k$ limits were fixed from
level 2 alone and reproduce levels 3 to 7 independently.

**Theorem 3.3 (unconditional bounds).** Using only Theorem 2.5, $0\le b_k\le B_k$ and the verified $B_k$ formula
through level 5, the limits satisfy: non-trivial $\in[0.4566,0.4980]$, traceless $\in[0.3750,0.4163]$,
central $\in[0.0816,0.1230]$. With the assumption-free bound $B_j\le48\cdot4^j$ the interval widths become
$0.083$. The conditional exact values lie inside every interval.

**Finite-size scaling.** Observed non-trivial fractions $0.5667,0.5139,0.4895,0.4805,0.4763,0.4743,0.4732$ for
$k=1..7$ (the last two via Theorem 2.5 from the measured straddling counts) approach $17/36=0.47222$ with deviations $0.0944,0.0417,0.0173,0.0083,0.0041,0.0020,0.0010$, consistent
with the $4^k/8^k=2^{-k}$ surface term of the recursion. Sensitivity: the same recursion applies to every
decoration (Theorem 2.5 uses only ambient-rotation invariance), so the exact limits are decoration-specific numbers
while the rate $2^{-k}$ is universal.

### 3.3 Spectral limits and matched controls

Five models on identical graphs at each level (`phase3_spectral_convergence.py`): FR30 Clifford; trivial
connection ($C\equiv I$); i.i.d. random $Q_8$ links (seed 11); "adjoint-only" (each Clifford link with its central
sign stripped, isolating the $V_4$ content); FR30 geometry with a random admissible decoration (seed 7).

| level | dim | $\lambda_{\min}$ Clifford | trivial | random $Q_8$ | adjoint-only | random decoration |
|---|---|---|---|---|---|---|
| 1 | 16 | 2.88942 | 0 | 6.63769 | 3.05301 | 3.85937 |
| 2 | 128 | 4.72646 | 0 | 8.44078 | 4.22471 | 5.39306 |
| 3 | 1024 | 5.11494 | 0 | 8.95123 | 4.92919 | 5.81252 |
| 4 | 8192 | 5.20970 | 0 | 8.96816 | 5.11356 | 6.01793 |
| 5 | 65536 | 5.24993 (shift-invert) | 0 | — | — | — |

The Clifford spectral bottom converges ($\Delta=1.84,0.39,0.095,0.040$) to $E_0\approx5.27\pm0.02$ (geometric
extrapolation). This is the one spectral quantity in which the background is sharply visible: a frustration gap
$[0,E_0)$ that is absent for the trivial connection. It is not a mass: the operator is a graph Laplacian with
$SU(2)$ twists and $E_0$ is its spectral infimum, with no dispersion, Lorentz structure or particle interpretation.
Mean eigenvalue $=$ average degree ($12,18,21,22.5$) for all models at all levels, as it must. Kolmogorov distances
between successive IDS decrease by $\approx0.45$ per level for every model. At level 4:
$d_K(\text{Clifford},\text{trivial})=0.053$, $d_K(\text{Clifford},\text{adjoint-only})=0.019$,
$d_K(\text{Clifford},\text{random }Q_8)=0.150$, $d_K(\text{Clifford},\text{random decoration})=0.033$. No gap of
relative width $>2\%$ persists at levels 3 and 4 in any model.

Interpretation with controls. The spectral signature of the Clifford background is intermediate between no flux
and i.i.d. flux, as its 47% non-trivial plaquette fraction would suggest; the random decoration (a different
admissible frame field on the same tiling) is spectrally closer to FR30 than FR30 is to the trivial model; the
central $\mathbb Z_2$ content changes the IDS by less than $0.02$. Nothing here is specific to FR30 beyond its
particular flux pattern.

### 3.4 A dynamical model, if one wants one

Nothing in the geometry provides an action. The only principled dynamical completion is a finite-group lattice
gauge theory on $\Gamma_k$ with configuration space $Q_8^{E_k}$ (or $SU(2)^{E_k}$), Wilson action
$S_\beta[U]=\beta\sum_p\bigl(1-\tfrac12\operatorname{Re}\operatorname{Tr}U_p\bigr)$ over canonical plaquettes,
Haar (counting) measure, and the Clifford configuration entering only as a background or as a defect boundary
condition. Its continuum content is topological (the quantum double of $Q_8$ for the finite-group case), with a
confinement transition in $\beta$ and no propagating gauge bosons. On the frozen Clifford configuration the action
is a number: $S_\beta/(\beta N_k)\to\tfrac{55}{144}+2\cdot\tfrac{13}{144}=\tfrac{81}{144}=0.5625$ per inter-tile
plaquette (conditional on Corollary 3.2). This is labeled a new model; every element of it is an assumption, and
none is constrained by the tiling.

---

## 4. Phase 4: physical conclusions

| Question | Answer | Basis |
|---|---|---|
| Does a gauge symmetry emerge from the geometry? | No. Any $G$-valued connection on a graph admits $G$-valued gauge transformations formally; the geometry supplies a *configuration*, not a symmetry principle. The frame changes that the geometry does admit are not gauge transformations (Audit Thm 1.3). | Sections 2.1, 2.2 |
| What is the gauge content? | An abelian $\mathbb Z_2\times\mathbb Z_2$ flux (vector matter) lifted to $Q_8$ (spinor matter) by a non-split central extension; a decoration-dependent background with exact rational flux frequencies. | Thms 2.2, 2.3, Cor. 3.2 |
| Can fermions / spin structure be defined? | A two-component hopping field with $T^2=-1$ exists and the central $\mathbb Z_2$ sign on adjoint-trivial loops is a well-defined "spin-twist" invariant. There is no Dirac operator, no signature, no chirality operator. | Thm 2.3, Section 3.3 |
| Is there chirality? | No. Wilson-loop traces and plaquette classes are identical for a tiling and its mirror image. Any claim of handedness from this background (including the birefringence story) is excluded. | Thm 2.4 |
| Local dynamics? | None derivable. Only the kinematic hopping operator on a frozen background. | Section 3.4 |
| Particle spectrum or couplings without fitting? | No. The one derived number, $E_0\approx5.27$ in units of the hopping amplitude, is a spectral infimum of a tight-binding operator, not a mass. | Section 3.3 |
| Quantitative predictions differing from a baseline, testable in principle? | Yes, two, at the level of the mathematical model and of synthetic-gauge metamaterials: exact flux frequencies $(19/36,13/144,1/9,23/144,1/9)$ and $E_0\approx5.27$ versus $0$ for the untwisted lattice. | Sections 3.2, 3.3 |
| Cosmological observables derived from the tiling? | No. $\beta_0=0.35^\circ$ is an input; the "Q8 transport" in the cosmology code is a continuous non-unitary operator; the inflation eigenvalue used is the icosahedral $\tau^3$, not the chair's $8$. Theorem 2.4 independently rules out the tiling as a source of parity violation. | Audit Section 6.1, Thm 2.4 |

**Standard Model.** Not derivable; the exact missing structures are unchanged from the audit: a 12-dimensional gauge
Lie algebra (the holonomy group is finite), any abelian flux at all ($\det C_e=1$ everywhere), complex triplets,
chiral fermions in Lorentzian signature, generations, and a Higgs/Yukawa sector. The minimum additional assumption
set is the full Standard Model on a lattice whose only role would be to supply a $\mathbb Z_2\times\mathbb Z_2$
background flux inside $SU(2)$.

**The most defensible physical reading** of what survives: the FR30 tiling is an aperiodic polycrystal of cubic
grains with misorientations in the octahedral group, and the Clifford link is a coarse ($Q_8$-valued) function of the
standard grain-boundary character (misorientation plus boundary-plane normal). A spinor hopping across boundaries
acquires boundary-dependent $SU(2)$ rotations. That is a legitimate synthetic-gauge or spin-orbit-scattering model
for an engineered medium. It is not a theory of fundamental interactions.

---

## 5. Theorem ledger

| Statement | Status | Artifact |
|---|---|---|
| Exact supertiles, frames in $SO(3,\mathbb Z)$, 56 cubes, 48 panels, $L$ and its factorization | proved; Lean (geometry-derived) | `Chair44GeometryToMatrix.lean`, `independent_clifford_q8_audit.py` |
| Links in $Q_8$: 24 central-negative, 6 trivial, 18 traceless; plaquette classes 26/3/31 | proved; Lean (geometry-derived) | same |
| Universal telescoping, gauge covariance over any group | proved; Lean | `PvsNPCliffordCertificates.lean` §1 |
| Thm 2.1 link classification | proved | §2.2 |
| Thm 2.2 adjoint reduction to $V_4$; Thm 2.3 central extension | proved | §2.2, census script part B |
| Thm 2.4 parity invariance of Wilson traces | proved; checked levels 1, 2 | census script part C |
| Thm 2.5 class inheritance recursion | proved; checked levels 2 to 5 | `phase3_plaquette_recursion.py` |
| Thm 2.6 IDS convergence, rate $T_k/8^k$ | proved | §2.2 |
| Thm 3.3 unconditional limit intervals | proved (given $B_k$ formula to level 5, which is measured) | `phase3_plaquette_recursion.py 5` |
| Non-flatness for all 6561 decorations at level 1 | proved by exhaustive computation | `phase2_structure_census.py` |
| $\mathrm{Hol}=Q_8$ at levels 1 to 3 | computational (exact arithmetic) | audit script |
| Prop. 3.1 closed forms for $N_k,B_k,b_k(c)$ | conjecture, verified $k\le7$, two out-of-sample | `phase3_level6_straddle.py` |
| Cor. 3.2 exact limits $19/36,13/144,1/9,23/144,1/9$ | conditional on Prop. 3.1 | §3.2 |
| $E_0\approx5.27$ | numerical extrapolation from levels 1 to 5 | `phase3_spectral_convergence.py` |
| Absence of persistent spectral gaps | numerical, levels 3 to 4, 2% threshold | same |
| Monograph cycle table (48/416/3424, 100%) | refuted | §1 |
| FR30 $\lvert P_0\rvert=30$ as a distinguished minimum | refuted at level 2 (minimum is 26) | census |
| Spin(4) rank obstruction; soldered mass gap; $\lambda_{\min}=2.6687$ | refuted (audit) | regression tests pin the counterexamples |
| $\lvert P^*\rvert=44$, $\lvert F^*\rvert=135$, aperiodicity of FR30 | external, unverified | — |

---

## 6. Open problems, ranked

1. **Prove Proposition 3.1** (interface self-similarity of the chair substitution from level 3 on). Feasible: a
   finite case analysis of the eight child interfaces; would make Corollary 3.2 a theorem.
2. **Identify $N_\infty$.** Is the limiting spectral measure of the Clifford hopping operator absolutely
   continuous, and is $E_0$ an algebraic number? Feasible numerically to level 6 with sparse methods; the
   gap-labeling group of the chair hull ($\mathbb Z[1/2]$) predicts dyadic IDS values at any gap that does open.
3. **Decoration-independent invariants.** Which functions of the flux pattern are the same for all 6561
   decorations (the census suggests non-flatness is; the class frequencies are not)? Feasible by extending the
   census to level 2 and to class frequencies.
4. **The 9 exceptional decorations** with order-4 holonomy: characterize them and whether the order-4 group is
   $\mathbb Z_4$ or $V_4$-lifted. Easy.
5. **Finite-group gauge dynamics on $\Gamma_k$.** Phase structure of $Q_8$ lattice gauge theory on the aperiodic
   graph with the Clifford defect background; whether the background shifts the confinement transition. Hard,
   Monte Carlo; this is a new model, not a derivation.
6. **Kamenetsky's closure criterion and Open Problem 9.1.** Implement the actual contact-language closure and the
   4D frame-closure search; neither exists in the repository. Hard; depends on external definitions.

---

## 7. Final assessment

**Genuinely new (this phase).** The adjoint reduction of the Clifford connection to an abelian Klein-group flux with a
$\mathbb Z_2$ spinor extension; parity invariance of its Wilson loops; the exact class-inheritance recursion and the
exact rational limiting flux frequencies $(19/36,13/144,1/9,23/144,1/9)$ with out-of-sample validation to 37
million plaquettes; the proved convergence of the spectral measure with an explicit rate; the census showing
non-flatness is substitution-forced and FR30 is unexceptional; and a Lean certificate that derives the Level-1
matrices from the substitution rule rather than pasting them.

**Already standard mathematics.** Telescoping of coboundaries and conjugation covariance of Wilson loops; closure
of $Q_8$ under multiplication; Kramers degeneracy for $SU(2)$ hoppings; rank-perturbation bounds on eigenvalue
counting; convergence of patch frequencies for primitive substitutions; the fact that finite-group gauge theories
are topological in the continuum.

**Speculative or excluded.** Any continuum gauge field (excluded for these link values); chirality from the
background (excluded by Theorem 2.4); emergent gauge symmetry, matter content, masses, couplings, or cosmological
parameters from the tiling (not derivable; where numbers appear in the repository they are inputs); the Standard
Model (excluded, with the missing structures itemized).

**Evidence that would change this assessment.** A proof or disproof of Proposition 3.1; discovery of persistent
dyadic-labeled spectral gaps at higher levels (which would make the hierarchy spectrally visible); a demonstration
that some admissible decoration yields a flux pattern with a decoration-independent, geometrically forced
invariant beyond non-flatness; or an explicit mechanism, with an action, by which frozen $V_4$ flux on an aperiodic
lattice produces propagating gauge degrees of freedom. None of these is suggested by the present computations.

## 8. Artifacts

- `deliverables/CLIFFORD_Q8_PHASE2_RESEARCH.md` (this document)
- `certificates/Chair44GeometryToMatrix.lean` (new; geometry-derived Level-1 certificate)
- `audit/phase2_structure_census.py`, `audit/phase3_plaquette_recursion.py`, `audit/phase3_level6_straddle.py`,
  `audit/phase3_spectral_convergence.py` (new), building on `audit/independent_clifford_q8_audit.py`
- `audit/results/*.txt` (saved outputs of the long computations)
- `tests/test_independent_audit_regression.py` (11 regression tests, 2.4 s, no imports from `src/`)
