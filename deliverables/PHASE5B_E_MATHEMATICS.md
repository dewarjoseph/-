# Phase V-B, Workstream E — Theorem ledger: excess mechanism, radius-2 census, recursion constraints

Branch `claude/phase5b-excess-mechanism`. Everything below was computed or proved in this session; nothing is quoted
from earlier phases without saying so. Status labels: **[K]** kernel-checked in Lean (none new in this session);
**[P]** proved here, outside Lean, with the argument written out; **[X]** exact computational certificate (integer /
rational arithmetic, independent of floating point); **[N]** numerical evidence (floating point); **[C]** conjecture
or dependence on a result marked [C] in `PHASE5A_INFINITE_VOLUME_FRAMEWORK.md` (unique ergodicity, §1.8 there).
Framework = `deliverables/PHASE5A_INFINITE_VOLUME_FRAMEWORK.md`; Recursion theorem = `deliverables/PHASE5A_RECURSION_THEOREM.md`.

Machine: 4 cores shared, `OMP_NUM_THREADS=1`, `python3 -u -I`, every job single-threaded, peak RSS 1.0 GB (level-6 solve).

## 0. The new bracket

$$\frac{72147403}{18000000}=4.008189056\;\le\;E_{\rm bulk}\;\le\;\mathrm{E1\_RATIONAL}=\mathrm{E1\_DECIMAL}$$

Both ends are exact rational numbers produced by exact integer arithmetic (status [X] on top of [P] theorems from the
framework). Previous rigorous bracket: $3.2014583\le E_{\rm bulk}\le 8.797011333$. The level-6 float value
$8.7701336$ (LOBPCG Rayleigh quotient) is now backed by an exact certificate; the lower bound moved from the 72
one-star types (vertex blocks) to the 165 two-star types (3-blocks), and the float value $4.008198$ of the C2 referee
check is now certified to within $9\cdot10^{-6}$.

## 1. E1 — Level-6 exact upper bound

**Theorem 1.1 [X on P].** Let $p\in\mathbb Z[i]^{524288}$ be the Gaussian-integer vector
$p=\operatorname{round}(2^{26}\psi)$, $\psi$ the LOBPCG ground vector of $H^{\rm pin}_6=24-A$ on $\mathcal T_6$. Then
$$E_{\rm bulk}\ \le\ \lambda_{\min}(H^{\rm pin}_6)\ \le\ \frac{\langle p,(24-A)p\rangle}{\langle p,p\rangle}
=\mathrm{E1\_RATIONAL}=\mathrm{E1\_DECIMAL}.$$
*Hypotheses.* Framework Theorem 3.2(a) (compression: $\lambda_{\min}(H^{\rm pin}_m)\ge E_{\rm bulk}$, [P] there, needs
only that $\mathcal T_6$ occurs in every hull element, Theorem 1.10) and the Rayleigh principle.
*Certificate.* $\langle p,p\rangle$ and $\langle p,Ap\rangle=2\operatorname{Re}\sum_f\langle p_a,C_fp_b\rangle$ are
integers ($A$ has entries in $\{0,\pm1,\pm i\}$). They were evaluated twice independently — (A) numpy `int64`
per-panel products grouped by $Q_8$ label with chunked accumulation in Python integers under an explicit overflow bound
($4\cdot2^{14}\cdot p_{\max}^2<2^{62}$), and (B) a pure-Python loop over the panels in a different order (sorted by
tile, accumulated per tile) — and agree bit for bit; a float evaluation with the scipy operator agrees to
$\mathrm{E1\_FLOATDIFF}$. The operator itself is the vectorised grid builder of `phase5a_level6_structure.py`, re-validated
entry by entry at level 4 against the object builders (`tiles_at_level`/`panel_edges`/`clifford_link`) before the run,
Hermitian to $0.0$, with 3096576 panels and the same $Q_8$ label census as the Phase V-A run.
*Solver (status [N], only affects tightness).* LOBPCG, block 4, diagonal preconditioner, seed 0, chunks of $\le600$
iterations with warm restart; E1_ITERS iterations, final ground-state residual $\|H\psi-\lambda\psi\|=\mathrm{E1\_RES}$,
Kramers split E1_SPLIT, gap to the next pair $1.08\cdot10^{-4}$; E1_TIME s wall, 1.0 GB. Float Rayleigh quotient
E1_FLOAT; certificate minus float $=\mathrm{E1\_GAP}$.
*Files.* `audit/phase5b_e_level6_certificate.py`, `audit/results/phase5b_e_level6_certificate.txt`,
`audit/results/phase5b_e_fr30_level6_groundstate.npy` (complex128, unit norm, depth-first tile order, 2 spinor
components per tile).

The decrements of the certified upper bounds are now $1.398,0.459,0.123,0.027$ (levels 2→6), consistent with but not
proving a $4^{-m}$ Dirichlet law (framework §5.4 remains open).

## 2. E2 — Radius-2 collared census, closure theorem, certified 3-block bound

### 2.1 Definitions

**Definition 2.1 ($r$-star).** For a tile $a$ of a tiling $\omega$ and $r\ge1$, the **$r$-star** of $a$ is the set of
tiles of $\omega$ owning at least one unit cube at Chebyshev ($\ell_\infty$) distance $\le r$ from some cube of $a$, i.e.
the tiles meeting $N_r(a)=\{c\in\mathbb Z^3:\operatorname{dist}_\infty(c,\operatorname{cubes}(a))\le r\}$. For the
chair, $|N_1(a)|=63$ and $|N_2(a)|=215$ (the $2\!\times\!2\!\times\!2$ bounding box grown by $r$, minus the one corner
cube at distance $r+1$ from every chair cube). The **type** of an $r$-star is the set of relative poses
$(M_a^\top M_b,\ M_a^\top(T_b-T_a))$ of its members (a complete rigid-motion invariant since $\Gamma=SO(3,\mathbb Z)\ltimes\mathbb Z^3$
acts freely on poses). The 1-star is the vertex-star of framework §3.3 (72 legal types, Lemma 3.5 there). This is the
definition used by the C2 referee check (165 types in $\mathcal T_5,\mathcal T_6$); it is **not** the graph-distance-2
neighbourhood (a tile at panel-graph distance 2 can be at Chebyshev distance 3, since a chair spans a $2\times2\times2$ box).

### 2.2 Closure

**Lemma 2.2 (parent radius) [P].** If $x,x'\in\mathbb Z^3$ with $|x-x'|_\infty\le r$ then
$|\lfloor x/2\rfloor-\lfloor x'/2\rfloor|_\infty\le\lceil r/2\rceil$. In particular $r=2\Rightarrow1$.
Consequently, if $\omega=\sigma(\omega')+z$ and $a$ is a child of $A\in\omega'$, then the $r$-star of $a$ is contained
in $\sigma(\lceil r/2\rceil\text{-star of }A)+z$; the 2-star of a child is determined by the **1-star** of its parent
(the parent's 2-star is not needed).
*Proof.* Per coordinate, $x'\in[x-r,x+r]$ gives $\lfloor x'/2\rfloor\in[\lfloor(x-r)/2\rfloor,\lfloor(x+r)/2\rfloor]
\subset[\lfloor x/2\rfloor-\lceil r/2\rceil,\lfloor x/2\rfloor+\lceil r/2\rceil]$. A member $b$ of the $r$-star of $a$
owns a fine cube $x'$ with $|x-x'|_\infty\le r$ for some cube $x$ of $a$; the parent cube of $x$ lies in $A$ and the
parent cube of $x'$ lies in the parent tile of $b$, at Chebyshev distance $\le\lceil r/2\rceil$ from a cube of $A$. $\square$

Hence the **collared maps** $\Phi_2:\mathcal V_1\to2^{\{\text{2-star types}\}}$ (1-star type of $A$ $\mapsto$ the 8 two-star
types of the children of $A$, read off inside $\sigma(\text{1-star})$) and $\Phi_{22}$ (2-star type $\mapsto$ 8 two-star
types of the children; well defined because the 1-star of $A$ is part of its 2-star) are well defined on legal types.

**Theorem 2.3 (closure of 2-stars) [P + X].** Let $\mathcal V_1$ be the set of legal 1-star types (= the forward
$\Phi$-orbit of any legal 1-star, framework Lemma 3.5; $|\mathcal V_1|=72$). Then the set $\mathcal V_2$ of legal 2-star
types satisfies
$$\mathcal V_2=\Phi_2(\mathcal V_1)=\bigcup_{s\in\mathcal V_1}\Phi_2(s),$$
and $\mathcal V_2$ also equals the forward $\Phi_{22}$-orbit of any single legal 2-star.
*Proof.* ($\supseteq$) An element of $\Phi_2(s)$ is the 2-star of a tile of $\sigma(Q)$, $Q$ the patch of $s$; $Q$ legal
($Q+x\subset\mathcal T_m$) implies $\sigma(Q)+2x\subset\mathcal T_{m+1}$ legal, so the 2-star is legal (its patch is a
sub-patch of a legal patch). ($\subseteq$) Let $\tau$ be a legal 2-star type, realised by a tile $a$ with complete 2-star
in some legal patch, hence (framework Theorem 1.10) in some $\omega\in\Omega$. By recognizability (Theorem 1.8)
$\omega=\sigma(\omega')+z$ and $a$ is a child of a tile $A\in\omega'$. By Lemma 2.2 the 2-star of $a$ lies in
$\sigma(\text{1-star}(A))+z$, and it is determined by that patch together with the child index. The 1-star of $A$ is a
complete star in the tiling $\omega'$ of $\mathbb R^3$, hence a legal patch, so its type $s$ lies in $\mathcal V_1$, and
$\tau\in\Phi_2(s)$. For the orbit statement: the forward $\Phi_{22}$-orbit of a legal 2-star $s_0$ with centre $t_0$ is
$\{s_0\}\cup\{\text{2-star types of tiles of }\sigma^n(t_0),\,n\ge1\}$, and the 1-star types of the tiles of
$\sigma^{n-1}(t_0)$, $n\ge1$, exhaust $\mathcal V_1$ (the proof of Lemma 3.5), so the orbit is
$\{s_0\}\cup\Phi_2(\mathcal V_1)=\mathcal V_2$. $\square$

*Computation (`phase5b_e_radius2_bound.py`, §1–2).* The forward orbit of the most frequent complete 1-star of
$\mathcal T_4$ closes after 5 rounds with 72 types; for every one of the 72 types the 2-stars of the 8 children are
complete inside $\sigma(\text{1-star})$ (the assertion in `Phi_r` is the computational form of Lemma 2.2);
$|\Phi_2(\mathcal V_1)|=\mathbf{165}$ types (35 to 65 tiles each); $\Phi_{22}(\mathcal V_2)\subset\mathcal V_2$; the
$\Phi_{22}$-orbit of one 2-star is the same 165. Census of complete 2-stars: $\mathcal T_5$: 25648 complete, 165 types;
$\mathcal T_6$: 232560, 165; $\mathcal T_7$: 1976560 complete 2-stars among 2097152 tiles, 165 types — all equal to
$\mathcal V_2$ (272 s, 0.67 GB for $\mathcal T_7$). Agrees with the 165 of the C2 check.

### 2.3 The 3-block decomposition and the certified bound

**Lemma 2.4 (3-block identity) [P + X].** For $c\in\mathbb Z^3$ let $B_c=c+\{-1,0,1\}^3$ and
$k_c(\psi)=\sum_{f\subset B_c}\|\psi_a-C_f\psi_b\|^2$, the sum over inter-tile unit faces whose two cubes lie in
$B_c$. Then for finitely supported $\psi$, $\langle\psi,H_\omega\psi\rangle=\frac1{18}\sum_ck_c(\psi)$.
*Proof.* A face between cubes $q,q+e_i$ lies in $B_c$ iff $c_i\in\{q_i,q_i+1\}$ and $|c_j-q_j|\le1$ for $j\ne i$:
exactly $2\cdot3\cdot3=18$ blocks. Framework Prop. 2.2 gives $\langle\psi,H\psi\rangle=\sum_f\|\psi_a-C_f\psi_b\|^2$. $\square$
(Checked exactly on $\mathcal T_3$: on the 160 tiles all of whose 63 blocks lie inside, the rows of
$\frac1{18}\sum_cK_c$ and of $24-A$ coincide to $0.0$.)

**Lemma 2.5 (localisation) [P].** $k_c\ge\lambda_{\min}(k_c)\,\Pi_{V(c)}$, $V(c)$ the tiles meeting $B_c$, hence
$$H_\omega\ \ge\ \frac1{18}\sum_aS_3(a)\,\Pi_a,\qquad S_3(a)=\sum_{c\in N_1(a)}\lambda_{\min}(k_c),\qquad
E_{\rm bulk}\ \ge\ \frac1{18}\inf_aS_3(a),$$
and $S_3(a)$ depends only on the 2-star type of $a$: the tiles of $B_c$ for $c\in N_1(a)$ own cubes within Chebyshev
distance 2 of $a$, and each $k_c$ is determined by the poses of those tiles (framework Prop. 2.3(c)). The forms
$k_c$ are invariant under the global rotation $(M,T)\mapsto(gM,gT)$, $g\in SO(3,\mathbb Z)$ (links depend on
$M_a^\top\mathbf n$, Prop. 2.3(b)), so $\lambda_{\min}(k_c)$ is a function of the rotation-canonical block signature. $\square$

**Theorem 2.6 (certified lower bound) [X on P].**
$$E_{\rm bulk}\ \ge\ \frac{72147403}{18\,000\,000}=4.008189056>4.$$
*Proof.* Lemmas 2.4–2.5 and Theorem 2.3 reduce the claim to the 165 types. Over $165\times63$ blocks there are 162
distinct rotation-canonical signatures (8 to 10 tiles per block, matrix dimension $\le20$); for each, with
$\lambda=\lambda_{\min}(k_c)$ in floating point, $\mu_c=(\lfloor10^6\lambda\rfloor-2)/10^6$ and the Hermitian
Gaussian-integer matrix $10^6k_c-(10^6\mu_c)I$ was shown positive definite **exactly**: by Sylvester's criterion a
Hermitian matrix is positive definite iff all leading principal minors are positive, and the minors were computed
by fraction-free Bareiss elimination over $\mathbb Z[i]$ in Python integers (self-tested on 600 random Hermitian
Gaussian-integer matrices against `eigvalsh`, including indefinite ones). All 162 certificates succeeded (no flat
block: $\lambda_{\min}\in[0.586840,1.752998]$), and the test rejects $\mu_c+10^{-5}$ for the sampled blocks, so the
pivots detect $\lambda_{\min}$. Then $\min_{\mathcal V_2}\sum_c\mu_c=72147403/10^6$, attained by one type (35 tiles). $\square$

Float value of the same minimum: $4.008197841$ (C2 reported $4.008198$ uncertified); the certified value is smaller
by $8.8\cdot10^{-6}$, the price of $63\times2\cdot10^{-6}$ roundings plus the floor. Over the 165 types $S_3/18$
ranges from 4.0082 (min) through 4.7107 (median) to 5.2625 (max).

*Hypothesis chain (all [P] in the framework, none [C]):* Theorem 1.8 (recognizability), Theorem 1.10 (repetitivity),
Lemma 3.5 ($\mathcal V_1$ = 72), Prop. 2.2–2.3 (form identity, locality, rotation invariance), Theorem 3.2 is not
needed for the lower bound. Unique ergodicity is **not** used. Files: `audit/phase5b_e_radius2_bound.py`,
`audit/results/phase5b_e_radius2_bound.txt`, `audit/results/phase5b_e_radius2_types.json` (the 165 types, their
exact $\sum_c\mu_c$, census counts, $\Phi_2$).

*Remarks.* (i) The remaining gap to the upper bound (factor $\approx2.19$) is the interference discarded by
$k_c\ge\lambda_{\min}\Pi$ between overlapping blocks; the C2 slack diagnostic showed a loss factor $\approx3.9$ for the
edge decomposition. Larger blocks ($4^3$, weight $1/(3\cdot4^2)=1/48$) need 3-stars (445 types, §3.4) and
$\le 2\cdot27$-dimensional exact certificates; this is the natural next step. (ii) Convex mixing of the edge, vertex
and 3-block decompositions cannot help (C2: optimum is the pure 3-block weight).

## 3. E3 — Exact constraints from the type recursion

### 3.1 Box-object recursion

**Theorem 3.1 (box objects) [P + X for $m\le4$].** Call a **box object** an axis-aligned box of unit cubes, all present
and owned by $\ge2$ tiles, with its owner tiles and frames, modulo $\Gamma$. Shapes used: $P=1\!\times\!1\!\times\!2$
(inter-tile panel), $Q=1\!\times\!2\!\times\!2$ (the 4 cubes around a lattice edge: a plaquette), $R=1\!\times\!2\!\times\!3$
(two parallel plaquettes sharing a panel), $W=1\!\times\!3\!\times\!3$ (a $2\times2$ rectangle of four parallel lattice
edges; its boundary is an 8-cube loop), $V=2\!\times\!2\!\times\!2$ (the 8 cubes around a lattice point, carrying the 6
plaquettes incident to it). The coarse parents of a box form a box (a row of length 1 has 1 parent, length 2 has 1 or 2,
length 3 exactly 2), so with $v^Y_m$ the type-count vector of shape $Y$ in $\mathcal T_m$,
$$v^Y_{m+1}=8^m f_Y+\sum_{Y'}S_{YY'}\,v^{Y'}_m\qquad(m\ge1),\qquad f_Y=v^Y_1,$$
where $S_{YY'}[\tau',\tau]$ counts the fine objects of type $\tau'$ whose parent set is exactly the cube set of the coarse
object $\tau$, and $Y'$ runs over the inter-tile parent shapes: $P\leftarrow P$; $Q\leftarrow P,Q$; $V\leftarrow P,Q,V$;
$R\leftarrow P,Q$; $W\leftarrow Q$. *Proof.* Identical to the parity trichotomy of the Recursion theorem, Statement 1:
if all parents lie in one coarse tile the object lies inside one inflated tile (a rigid copy of $\mathcal T_1$, and the
$\Gamma$-type is rotation invariant), giving $8^mf_Y$; otherwise the parent box is an inter-tile coarse object of a
parent shape and the fine object is one of the finitely many fine placements over it. $\square$

*Computation (`phase5b_e_recursion_correlations.py`, Part A).* Independent re-derivation with its own canonical form
(minimum over base tiles of the encoded relative configuration): type counts after inflation closure $P$: **49**, $Q$:
**108** (the Phase V-A numbers, re-obtained), $V$: 66, $R$: 366, $W$: 266; column sums $S_{PP}$: 4, $S_{QP}$: 4,
$S_{QQ}$: 2, $S_{VP}=S_{VQ}=S_{VV}$: 1, $S_{RP}=S_{RQ}$: 8, $S_{WQ}$: 8; the recursion holds coordinate-wise for all five
shapes for $m=1,2,3$ against direct enumeration of $\mathcal T_2,\mathcal T_3,\mathcal T_4$ (totals 48/576/5376/46080
panels, 60/792/7728/67680 plaquettes, 19/279/2863/25695 vertex blocks, 96/1632/17088/153984 $R$, 24/672/7872/74112 $W$);
$\operatorname{charpoly}S_{PP}=\lambda^{44}(\lambda-4)(\lambda-1)^4$, $S_{QQ}=\lambda^{103}(\lambda-2)(\lambda-1)^4$ (as
in the Recursion theorem), $S_{VV}=\lambda^{64}(\lambda-1)^2$.

**Corollary 3.2 (exact limits) [P + X].** $u_Y=\lim8^{-m}v^Y_m$ exists and is rational (Statements 2–3 of the Recursion
theorem; $\rho(S_{YY})\le4<8$), $u_P=(8-S_{PP})^{-1}f_P$, then $u_Q,u_V,u_R,u_W$ in dependency order. Totals per tile:
$P$: 12, $Q$: 18, $V$: 7 (every lattice point is inter-tile, a chair having 7 cubes), $R$: 42, $W$: 21. Class
observables (exact; $Q_8$ conjugacy classes $1,-1,\{\pm i\},\{\pm j\},\{\pm k\}$):

* $Q$: $19/36,\ 13/144,\ 1/9,\ 23/144,\ 1/9$ — **Theorem A of Phase V re-derived independently.**
* $R$ (two parallel adjacent plaquettes; one of them may be intra-tile, so the single-edge marginal is over all 21
  lattice edges per tile, $(18p_\kappa+3\delta_{\kappa,1})/21$, which the pair distribution reproduces exactly):
  joint distribution of the unordered class pair $(1,1)$: $461/1344$; $(1,j)$: $85/448$; $(-1,1)$: $53/448$; $(1,i)=(1,k)$:
  $11/112$; $(i,j)=(j,k)$: $11/448$; $(i,i)=(k,k)$: $9/448$; $(i,k)$: $13/672$; $(j,j)$: $3/224$; $(-1,i)=(-1,j)=(-1,k)$:
  $11/1344$; $(-1,-1)$: $1/168$. The classes of adjacent parallel plaquettes are **not independent**: e.g. $(-1,-1)$ occurs
  with ratio $0.73$, $(-1,j)$ with ratio $0.28$ and $(i,i)$ with ratio $1.63$ relative to the product of marginals
  (conditional laws: given a $-1$ plaquette, the parallel neighbour is flat with probability $0.764$ (marginal $0.595$) and
  $-1$ with $0.077$; given $\{\pm i\}$, the neighbour is $\{\pm i\}$ with $0.211$ (marginal $0.095$); full tables in the result file).
* $W$ (8-cube loop around a $2\times2$ rectangle of parallel edges): holonomy class $1$: $151/1344$, $-1$: $205/1344$,
  $\{\pm i\}$: $3/16$, $\{\pm j\}$: $121/336$, $\{\pm k\}$: $3/16$. Number of $-1$ plaquettes among its four: $0$:
  $487/672$, $1$: $27/112$, $2$: $23/672$ (never 3 or 4).
* $V$ (lattice point, 6 incident plaquettes): number of $-1$ plaquettes $0$: $23/32$, $1$: $59/448$, $2$: $17/128$,
  $4$: $15/896$ (never 3, 5, 6); number of non-flat plaquettes $0$: $27/112$, $2$: $37/112$, $3$: $19/112$, $4$:
  $85/896$, $5$: $47/448$, $6$: $53/896$ (never exactly 1 — a single non-flat plaquette at a vertex is impossible, as
  the product of the six holonomies around a vertex is constrained). Mean number of $-1$ plaquettes per lattice point
  $13/28=2\cdot(13/8)/7$, the forced value.

### 3.2 Star frequencies and per-tile distributions

**Theorem 3.3 (1-star frequencies) [P + X].** Let $\Phi$ be the $72\times72$ collared substitution matrix on
$\mathcal V_1$ (column sums 8). Then $\operatorname{charpoly}\Phi=\lambda^{70}(\lambda-8)(\lambda-1)$; the eigenvalue 8
is simple and no other eigenvalue has modulus 8, so $(\Phi/8)^k$ converges to the rank-one projector onto the Perron
vector. Let $N_m(s)$ be the number of tiles of $\mathcal T_m$ with complete 1-star of type $s$. Then
$N_{m+1}=\Phi N_m+r_m$ with $|r_m|_1\le8\cdot\#\{\text{tiles of }\mathcal T_m\text{ with incomplete star}\}=O(4^m)$, and
$$\lim_m8^{-m}N_m=u_1,\qquad \Phi u_1=8u_1,\quad \textstyle\sum_su_1(s)=1,$$
the unique normalised Perron vector (all entries positive, denominators dividing 512, ten distinct values from
$1/512$ to $1/8$).
*Proof.* Children of a tile with complete star have complete stars of the types $\Phi$ prescribes (Lemma 2.2 with $r=1$);
only children of tiles with incomplete stars can escape this bookkeeping, and those tiles lie within distance 1 of the
boundary. Writing $8^{-m}N_m=(\Phi/8)^{m-1}8^{-1}N_1+\sum_{j<m}(\Phi/8)^{m-1-j}8^{-j-1}r_j$, the first term converges to
a multiple of $u_1$, each summand with $m-1-j\to\infty$ converges to a multiple of $u_1$ with summable weights
$O(2^{-j})$, and the tail with $j$ close to $m$ is $O(2^{-m})$; the total mass $8^{-m}\sum_sN_m(s)\to1$ fixes the
normalisation. $\square$ (Census check: $\max_s|N_m(s)/\sum N_m-u_1(s)|=2.97\cdot10^{-2}$ at $m=5$, $1.48\cdot10^{-2}$
at $m=6$: halving per level as the $O(2^{-m})$ surface term predicts.) If unique ergodicity holds ([C], framework §1.8),
$u_1$ is also the hull frequency of the 1-star types; nothing here depends on that.

**Cross-check [X].** Weighting each of the 48 inter-tile plaquettes touching the centre by $1/\#\{\text{tiles around
it}\}$ and summing with $u_1$ returns per tile $1$: $19/2$, $-1$: $13/8$, $\{\pm i\}$: $2$, $\{\pm j\}$: $23/8$, $\{\pm k\}$:
$2$, total 18 — **exactly** $18\times$ the Theorem A frequencies, obtained by a completely different route
(collared stars vs. panel/plaquette types).

**Corollary 3.4 [X].** (a) The per-tile distribution of the number $n_{-1}$ of class $-1$ plaquettes among the 48
inter-tile plaquettes touching a tile is exactly $n_{-1}=2$: $5/64$; $4$: $3/8$; $5$: $9/64$; $6$: $3/32$; $7$:
$1/64$; $8$: $13/64$; $9$: $3/32$; mean $11/2$. Number of non-flat plaquettes: $19$: $3/32$, $24$: $7/32$, $26$: $1/16$,
$27$: $7/64$, $28$: $19/64$, $31$: $1/16$, $32$: $1/64$, $33$: $1/64$, $37$: $1/8$. (b) 2-star frequencies
$u_2=\Phi_2u_1/8$ on the 165 types (denominators $\le512$; census deviation $1.28\cdot10^{-2}$ at $m=6$); 3-star types
$\mathcal V_3=\Phi_3(\mathcal V_2)$: **445** types (73–133 tiles, Chebyshev radius 3), $u_3=\Phi_3u_2/8$ (denominators
$\le4096$). Files: `audit/results/phase5b_e_recursion_correlations.txt`, `audit/results/phase5b_e_star_frequencies.txt`.

*Why the panel/plaquette recursion alone does not give (a).* The 157-type system records each plaquette with its own
$\le4$ tiles only; two different joint laws of the 48 plaquettes around a tile can have the same 108 marginal plaquette
counts. The per-tile law is a radius-1 collared observable and needs the collared (1-star) type system — which the
closure Lemma makes finite and exactly computable. The same holds for every observable of bounded radius: extend to
$\lceil\text{radius}\rceil$-stars.

### 3.3 Exact IDS moments

**Theorem 3.5 [P + X].** Let $m_k=\lim_m8^{-m}\operatorname{Tr}(H^{\rm pin}_m)^k$ (trace on $\ell^2\otimes\mathbb C^2$).
Then
$$m_0=2,\quad m_1=48,\quad m_2=1296,\quad m_3=37908,\quad m_4=1169988,$$
i.e. per state $\langle E\rangle=24$, $\langle E^2\rangle=648$, $\langle E^3\rangle=18954$, $\langle E^4\rangle=584994$;
variance $72$, third central moment $-54$ (skewness $-0.0884$), fourth central moment $9570$ (kurtosis $1.846$). These
are the moments of the limiting IDS $N_\infty$ of framework Theorem 4.3 (convergence in distribution of bounded
measures gives convergence of moments).
*Proof.* $(H^k)_{aa}$ is a sum over closed walks of length $k$; for $k\le3$ every tile visited is $a$ or a panel
neighbour of $a$ (within the 1-star), for $k=4$ the middle tile is a neighbour of a neighbour, within Chebyshev
distance 3 (the 3-star). Tiles whose relevant star is incomplete number $O(4^m)$ and contribute $\le2\cdot48^k$ each,
so $8^{-m}\operatorname{Tr}H^k=\sum_s8^{-m}N^{(r)}_m(s)\,t_k(s)+O(2^{-m})\to\sum_su_r(s)t_k(s)$ by Theorem 3.3 (and its
radius-2, 3 extensions). The $t_k(s)$ were computed exactly in Gaussian integers; $m_2,m_3$ agree between the 1-star and
3-star computations, $m_0=2$ and $m_1=48$ come out as they must. $\square$ Finite-size check: $8^{-m}\operatorname{Tr}H^k$
on $\mathcal T_5$ is $1290.0,\ 37476,\ 1147799$ for $k=2,3,4$ (boundary tiles lack panels), approaching the limits at
rate $2^{-m}$. The trivial connection on the same tiling has the same walk counts but all holonomies 1; from the same
$u_1$ its moments are $m_2^{\rm triv}=1314$, $m_3^{\rm triv}=38826$ (variance per state $81=\sum_b\operatorname{mult}(a,b)^2$,
third central moment $-243$), versus $72$ and $-54$ for the Clifford connection: the holonomies reduce the second moment
by $9$ per state through the cross terms $\operatorname{Re}\operatorname{tr}(C_fC_{f'}^\dagger)$ of panel pairs joining the
same two tiles (file `audit/phase5b_e_ids_moments.py`, output `audit/results/phase5b_e_ids_moments.txt`).

### 3.4 What the recursion can and cannot say about the operator spectrum

**Proposition 3.6 [P].**
1. *Can:* every $\Gamma$-invariant observable of bounded radius $r$ (holonomy classes of loops, joint laws of
   neighbouring plaquettes, per-tile counts, IDS moments $m_k$ for $k\le2r+1$ in the sense above) has an exact rational
   supertile-limit frequency, computable by extending the type system to $\lceil r\rceil$-collared types, whose number
   is finite by Lemma 2.2 and the closure argument (72, 165, 445 for $r=1,2,3$). In particular all moments of the IDS
   are rational, and the IDS as a measure is determined by the full collared frequency data.
2. *Cannot:* the spectrum $\{8,4,2,1,0\}$ of the type substitution $S$ (and $\{8,1,0\}$ of $\Phi$) carries **no
   information about the location of $\sigma(H_\omega)$**, for three reasons. (i) $S$ and $\Phi$ depend on the poses only;
   the link rule enters only through the class function on types. The trivial connection $C\equiv1$ has the *identical*
   recursion, the identical $S$, $\Phi$, frequencies and clean spectrum, and $E^{\rm triv}_{\rm bulk}=0$ (framework §3.4),
   while $E_{\rm bulk}\ge4.008$ here: the quantity that produces the gap is invisible to the recursion's spectrum.
   (ii) There is no renormalisation map on $\ell^2$: $H_{m+1}$ is not a function of $H_m$ (the substitution acts on
   pattern counts, not on the Hilbert space), so eigenvalues of $S$ are growth rates of counts (volume 8, surface 4, edge
   2, conserved 1, transient 0) and nothing else; they control the $O(4^{-m})$ convergence of *frequencies*, not of
   eigenvalues. (iii) $E_{\rm bulk}=\inf\operatorname{supp}dN_\infty$ is not determined by any finite set of moments
   (any finite moment sequence is compatible with measures whose support extends down to the Chebyshev–Markov limit), and
   nothing proved here shows $E_{\rm bulk}$ to be rational or algebraic; the bracket of §0 is the only rigorous
   information on it.

## 4. Ledger

| # | statement | hypotheses | status |
|---|---|---|---|
| 1.1 | $E_{\rm bulk}\le$ E1_RATIONAL $=$ E1_DECIMAL (level 6) | compression Thm 3.2(a) [P], Rayleigh | **[X]** two bit-identical exact evaluations; solver residual E1_RES [N] |
| 2.2 | $r$-star of a child $\subset\sigma(\lceil r/2\rceil$-star of parent$)$ | none (parity) | **[P]**, checked for $r=1,2,3$ on all types |
| 2.3 | $\mathcal V_2=\Phi_2(\mathcal V_1)=\Phi_{22}$-orbit of any seed; $|\mathcal V_2|=165$ | Thms 1.8, 1.10, Lemma 3.5 [P] | **[P + X]**; census $\mathcal T_5,\mathcal T_6,\mathcal T_7$ identical |
| 2.4 | $\langle\psi,H\psi\rangle=\frac1{18}\sum_ck_c(\psi)$ | Prop. 2.2 | **[P]**, exact check on $\mathcal T_3$ |
| 2.5 | $S_3(a)$ is a function of the 2-star type; $k_c$ rotation invariant | Prop. 2.3 | **[P]**, $\lambda_{\min}$ invariance re-checked on 162 repeats |
| 2.6 | $E_{\rm bulk}\ge72147403/18000000=4.008189056$ | 2.3–2.5 + Sylvester/Bareiss over $\mathbb Z[i]$ | **[X on P]**; float 4.008198 [N] |
| 3.1 | box-object recursion for $P,Q,V,R,W$ | exact block substitution (H1–H2 of the Recursion theorem) | **[P]**; exact for $m\le4$ [X] |
| 3.2 | exact limits; Theorem A re-derived; $R,W,V$ class laws | 3.1, Statements 2–3 | **[X]** |
| 3.3 | $\operatorname{charpoly}\Phi=\lambda^{70}(\lambda-8)(\lambda-1)$; $8^{-m}N_m\to u_1$ (Perron vector) | 2.2, Perron–Frobenius | **[P + X]**; identification with hull frequencies needs unique ergodicity [C] |
| 3.4 | per-tile $n_{-1}$ law, $u_2$ (165), $\mathcal V_3$ (445), $u_3$ | 3.3 | **[X]** |
| 3.5 | $m_k=2,48,1296,37908,1169988$ | 3.3 + walk locality + Thm 4.3 | **[P + X]** |
| 3.6 | recursion spectrum says nothing about $\sigma(H)$ | §3.4 of framework (trivial connection) | **[P]** |

No Lean kernel checks were produced in this session; the Lean certificate of Phase V-A (class counts at levels 1–2) is
unchanged.

## 5. Files, commands, wall times, caveats

New files (all with prefix `phase5b_e_`): `audit/phase5b_e_level6_certificate.py`, `audit/phase5b_e_radius2_bound.py`,
`audit/phase5b_e_recursion_correlations.py`, `audit/phase5b_e_ids_moments.py`; results
`audit/results/phase5b_e_level6_certificate.txt`, `audit/results/phase5b_e_fr30_level6_groundstate.npy`,
`audit/results/phase5b_e_radius2_bound.txt`, `audit/results/phase5b_e_radius2_types.json`,
`audit/results/phase5b_e_recursion_correlations.txt`, `audit/results/phase5b_e_star_frequencies.txt`,
`audit/results/phase5b_e_ids_moments.txt`; `tests/test_phase5b_e_results.py` (regression on the result files);
this ledger.

Commands (repository root, `OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 python3 -u -I …`, three jobs ran concurrently on 4 cores):
* `audit/phase5b_e_level6_certificate.py 6 3300` — E1_TIME s, 1.0 GB (geometry 3 s, $H$ 5 s, LOBPCG E1_LOBPCG s, exact
  certificate E1_CERTTIME s). A level-4 smoke test (4.5 s) reproduced the Phase V-A certificate $8.919634360$.
* `audit/phase5b_e_radius2_bound.py 7` — 387 s and 517 s in two runs (the second concurrent with two other jobs), 0.67 GB
  (of which the $\mathcal T_7$ census 272 s, the 162 exact Sylvester certificates < 1 s, canonicalisation 51 s). A first
  run aborted on a bug in a (since removed) zero-pivot shortcut of the Bareiss routine; the final routine has no shortcut
  and passed 600 randomized self-tests; the second run only corrected the reporting of the sharpness sanity line.
* `audit/phase5b_e_recursion_correlations.py` — 70–130 s, 0.35 GB (three runs; the first two fixed a transpose in the
  canonical form, which had produced 715 instead of 49 panel types with correct totals, and two reporting lines).
* `audit/phase5b_e_ids_moments.py` — 203–213 s, < 0.3 GB (160 s for the 445 three-star types).
* `python3 -m unittest tests/test_phase5b_e_results.py` — < 1 s.

Caveats. (1) The upper bound is the Rayleigh quotient of a *rounded LOBPCG vector*; its tightness (not its validity)
depends on the solver residual E1_RES. (2) The lower bound uses $\lambda_{\min}$ in floating point only to *choose*
$\mu_c$; validity rests on the exact Sylvester certificates. Both bounds depend on the [P] theorems of the framework
(recognizability, repetitivity, the 72-type closure), not on unique ergodicity. (3) All "frequencies" are limits along
the supertile sequence $\mathcal T_m$; their identification with hull frequencies (and the IDS moments with the hull IDS of
the literature) is [C] exactly as in the framework §1.8/§2.7. (4) The recursion verifications are exact for $m\le4$;
the all-$m$ statements are paper proofs. (5) Nothing new is kernel-checked.
