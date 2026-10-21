# Phase 5a, Task B3: The Infinite-Volume Framework for the FR30 Clifford Operator (H1)

Scope. This document defines the FR30 substitution hull, the infinite-volume operator $H_\omega=24-\mathcal A_\omega$,
proves its basic operator-theoretic properties, proves the compression theorem that turns the pinned supertile
computations into a rigorous upper-bound sequence for $E_{\rm bulk}=\inf\sigma(H_\omega)$, proves a rigorous
*positive lower bound* on $E_{\rm bulk}$ by a certified local decomposition, proves boundary independence of the
integrated density of states, and lists what remains open for H2–H5. Status labels: **[P]** proved here in full;
**[P+E]** proved here with a finite computation whose output is in `audit/results/`; **[C]** cited (every citation in
this document is an *unverified citation* in the sense of the task: full texts could not be opened from this
container; bibliographic metadata and abstracts were confirmed through web-search snippets where indicated);
**[N]** numerical evidence only; **[open]** not established.

Scripts written for this task: `audit/phase5a_frame_substitution.py`, `audit/phase5a_certified_upper_bound.py`,
`audit/phase5a_star_closure_lower_bound.py`; outputs `audit/results/phase5a_frame_substitution.txt`,
`audit/results/phase5a_frame_matrix.txt`, `audit/results/phase5a_certified_upper_bound.txt`,
`audit/results/phase5a_star_closure_lower_bound.txt`. All primitives (`tiles_at_level`, `panel_edges`,
`clifford_link`) are those of `audit/independent_clifford_q8_audit.py`.

---

## 0. Results at a glance

| Statement | Status |
|---|---|
| Hull $\Omega$ is a compact $\mathbb Z^3$-subshift of finite local complexity over 168 cube labels | [P] §1.3 |
| All 24 frames of $SO(3,\mathbb Z)$ occur; frame substitution matrix doubly stochastic, spectrum $\{8,2^{(20)},0^{(3)}\}$, primitivity exponent 2 | [P+E] §1.4 |
| Unique composition (recognizability) of every hull tiling via the *notch rule* | [P] §1.5–1.6 (cross-checked at levels 1–4) |
| Aperiodicity: no element of $\Omega$ has a translation period | [P] §1.6 (no external input) |
| Repetitivity, minimality; every supertile $\mathcal T_m$ occurs in every $\omega\in\Omega$ with bounded gaps | [P] §1.7 |
| Unique ergodicity / uniform patch frequencies | [C] Solomyak 1997, Lee–Moody–Solomyak 2002, hypotheses verified here §1.8 |
| $H_\omega$ bounded, self-adjoint, $0\le H_\omega\le 48$, gauge covariance, translation and rotation covariance, quaternionic (Kramers) structure | [P] §2 |
| $\sigma(H_\omega)$ independent of $\omega\in\Omega$ | [P] §2.6 (direct proof, no citation needed) |
| Compression theorem: $\lambda_{\min}(H^{\rm pin}_m)\downarrow E_{\rm bulk}$ | [P] §3.1 |
| Certified: $E_{\rm bulk}\le 8.7970114$ (level 5, exact rational Rayleigh quotient; levels 2–4 likewise certified); $8.77013$ at level 6 is a floating-point Rayleigh–Ritz value | [P+E] / [N] §3.2 |
| **New:** certified $E_{\rm bulk}\ge 1.568725$ (plaquette decomposition over the 72 legal vertex-star types) | [P+E] §3.3 |
| $0\in\sigma$ for the trivial connection: the gap $[0,E_{\rm bulk})$ is caused by the $Q_8$ flux | [P] §3.4 |
| Free and pinned IDS converge to the same limit with rate $O(2^{-m})$; equals hull IDS | [P] §4 + [C] for the identification |
| If a covariant effective-mass tensor exists it is isotropic | [P, conditional] §5.3 |
| Nature of edge states, attainment of $E_{\rm bulk}$, further gaps, homogenization | [open] §5 |

---

## 1. The hull

### 1.1 Data

Cubes are unit cubes $[c,c+\mathbf 1)$, $c\in\mathbb Z^3$; a cube is named by its corner $c$ or its center $c+\tfrac12\mathbf 1$.
The prototile is the chair $P=\{u\in\{0,1\}^3\}\setminus\{(1,1,1)\}$ (7 cubes), $G=SO(3,\mathbb Z)$ (24 signed
permutation matrices of determinant 1). A **pose** is $(M,T)\in G\times\mathbb Z^3$; the tile with pose $(M,T)$ occupies
the cubes with centers $M(u+\tfrac12\mathbf 1)+T$, $u\in P$ (so its cube corners are $(M(2u+\mathbf 1)+2T-\mathbf 1)/2$,
exactly the formula in `tiles_at_level`). $M$ is the **frame**; it is a genuine decoration: the cube set of a pose is
invariant under the order-3 stabilizer of $P$ in $G$ (cyclic coordinate permutations), so the 24 frames give only 8
geometric orientations (`phase5a_frame_substitution.txt`, §1), and the Clifford link depends on the frame
(`independent_clifford_q8_audit.py`, §3 "change frame of tile 3").

The FR30 **child maps** are $\varphi_c(M,T)=(Mg_c,\;2T+Mt_c)$, $c=0,\dots,7$, with $(g_0,t_0)=(I,\mathbf 1)$ (central
child) and, for $v\in P$, $(g_v,t_v)=(D_vP_v,\,4v)$, $D_v=\operatorname{diag}(\mathbf 1-2v)$, $P_v$ the permutation
matrix of `FR30[v]`. All $g_c\in G$ (checked). The inflation of a pose is $\sigma(M,T)=\{\varphi_c(M,T)\}_c$, of a set of
poses the union. **Equivariance:** the cube centers of the children of $(M,T)$ are $M(\text{centers of }\sigma(I,0))+2T$,
i.e. $\sigma(M,T)$ is the rigid image $x\mapsto Mx+2T$ of the root supertile. The level-$m$ supertile is
$\mathcal T_m=\sigma^m(I,0)$; it has $8^m$ tiles and covers $[0,2^{m+1})^3\setminus[2^m,2^{m+1})^3$ exactly (checked in
the audit script for $m\le3$; it follows for all $m$ from equivariance and the $m=1$ case, since the 8 children of a
scale-$2^m$ chair are scale-$2^{m-1}$ chairs filling it). The root supertile $S_1:=\mathcal T_1$ consists of the
central chair with cubes $[1,3)^3\setminus\{(2,2,2)\}$ and, for each $v\in P$, the outer chair $v$ occupying the
2-block $B_v=[2v,2v+2)^3$ minus the cube $\mathbf 1+v$.

Two elementary facts used throughout. (i) For a signed permutation matrix $M$, $M\mathbf 1\equiv\mathbf 1\pmod 2$
componentwise. (ii) For a chair with pose $(M,T)$, its 2×2×2 **box** has center (a lattice point) $p=T+M\mathbf 1$, and
its **notch** (the missing cube of the box) has center $p+\tfrac12M\mathbf 1$.

### 1.2 Tilings, patches, legality, the hull

A **(decorated) tiling** is a set $\omega$ of poses whose cube sets are pairwise disjoint and cover $\mathbb Z^3$.
A **patch** is a finite set of poses with pairwise disjoint cube sets. $\mathbb Z^3$ acts by translation,
$(M,T)+x=(M,T+x)$. A patch $Q$ is **legal** if $Q+x\subset\mathcal T_m$ for some $m\ge0$, $x\in\mathbb Z^3$.

**Definition 1.1 (hull).** $\Omega$ is the set of all tilings all of whose finite sub-patches are legal.

Each tiling is encoded by the map $\mathbb Z^3\to\mathcal A$, $c\mapsto(M_c,u_c)$, giving for each cube the frame of its
tile and its position $u_c\in P$ in the tile's body frame; $|\mathcal A|=24\cdot7=168$ and the map determines the
tiling (the tile containing $c$ has $T=c+\tfrac12\mathbf 1-M_c(u_c+\tfrac12\mathbf 1)$). We give $\Omega\subset\mathcal A^{\mathbb Z^3}$
the product (local) topology: $\omega_n\to\omega$ iff for every $R$ the two tilings agree on the ball of radius $R$ for
$n$ large.

**Proposition 1.2 (finite local complexity, compactness).** For every $R$ the set of patches of radius $R$ occurring
in elements of $\Omega$ is finite; $\Omega$ is a compact, $\mathbb Z^3$-invariant subset of $\mathcal A^{\mathbb Z^3}$,
i.e. a $\mathbb Z^3$-subshift. *Proof.* A patch of radius $R$ is a configuration of at most $(2R+2)^3$ cubes with
labels in the finite set $\mathcal A$: finitely many. Legality of a finite patch is a condition on finitely many
coordinates, so "all finite sub-patches are legal" is an intersection of clopen conditions, hence closed; it is
translation invariant because legality is. Closed subsets of the compact space $\mathcal A^{\mathbb Z^3}$ are compact. $\square$

**Proposition 1.3 (non-emptiness; fixed point up to translation).**
(a) $\Omega\ne\emptyset$: the translated supertile $\mathcal T_m-2^{m-1}\mathbf 1$ contains every tile meeting the ball
of radius $2^{m-1}$ about the origin (the point $2^{m-1}\mathbf 1$ is at distance $2^{m-1}$ from all faces of
$\mathcal T_m$). By compactness of $\mathcal A^{\mathbb Z^3}$ a subsequence of these configurations converges to a
tiling of $\mathbb R^3$, every finite patch of which agrees with a patch of some $\mathcal T_m-2^{m-1}\mathbf 1$ and is
therefore legal.
(b) Two *non*-examples. The $(0,0,0)$-child map fixes the root, $\varphi_{(0,0,0)}(I,0)=(I,0)$, so
$\mathcal T_m\subset\mathcal T_{m+1}$ with identical poses (verified as pose sets for $m\le3$), but the nested $\mathcal T_m$
exhaust only the octant $[0,\infty)^3$. The pose $s=(I,-\mathbf 1)$ is its own *central* child
($\varphi_0(I,-\mathbf 1)=(I,-\mathbf 1)$, checked), but $\sigma^m(s)=\mathcal T_m-2^m\mathbf 1$ covers exactly
$[-2^m,2^m)^3\setminus[0,2^m)^3$ (checked $m\le3$): the central chair touches the missing block of its own supertile
(Lemma 1.6(i) below), the notches nest at the origin, and $\bigcup_m\sigma^m(s)=\mathbb R^3\setminus[0,\infty)^3$ is not
a tiling. So neither of the two obvious fixed poses yields a tiling of $\mathbb R^3$.
(c) A genuine fixed point of $\sigma^2$ up to translation. Let $w=(\text{central},(0,0,0))$; then $g_w=I$ and the tile
of word $w$ in $\mathcal T_2$ is $(I,(2,2,2))$, which lies in the **interior** of $\mathcal T_2$ (all 26-neighbour cubes
of its cubes are in $\mathcal T_2$; checked). The rational pose $p=(I,T^*)$, $T^*=-\tfrac23\mathbf 1$, satisfies
$p\in\sigma^2(p)$ (since $\sigma^2(I,T)=\mathcal T_2+4T$ and $4T^*+(2,2,2)=T^*$; checked numerically together with
$\sigma^2(p)\subset\sigma^4(p)$). Interiority gives $\operatorname{dist}(p,\partial\sigma^{2n}(p))\ge4^{\,n-1}$, so
$X=\bigcup_n\sigma^{2n}(p)$ is a tiling of $\mathbb R^3$. All its cubes lie on $\mathbb Z^3+T^*$ because
$(4^n-1)T^*\in\mathbb Z^3$; hence $\omega^*:=X-T^*=\bigcup_n\bigl(\mathcal T_{2n}-\tfrac{2(4^n-1)}3\mathbf 1\bigr)$ is an
increasing union of integer translates of supertiles, a tiling of $\mathbb R^3$ with cubes on $\mathbb Z^3$ and legal
patches: $\omega^*\in\Omega$, and $\sigma^2(\omega^*)=\omega^*+(2,2,2)$. $\square$

(So the task's remark is confirmed and sharpened: the nested $\mathcal T_m$ are an octant, the "central-child" seed is a
half-space-like set, and the correct seed is the $(0,0,0)$-child of the central child, at the rational position
$-\tfrac23\mathbf 1$. Every element of $\Omega$ is a tiling of all of $\mathbb R^3$; the supertile structure on
$\omega^*$ is $\mathbb Z^3$-translation-equivariant only after the shift by $T^*$, which is why the nested supertiles of
the task statement cannot be taken literally as a sub-tiling of a hull element.)

### 1.3 Remark on the $\mathbb R^3$ picture

For the operator only the $\mathbb Z^3$-action matters (tiles sit on $\mathbb Z^3$). The $\mathbb R^3$ Delone
dynamical system of the literature is the suspension $\Omega\times_{\mathbb Z^3}\mathbb R^3$; minimality, unique
ergodicity and FLC transfer verbatim. We work with $(\Omega,\mathbb Z^3)$.

### 1.4 Frame substitution and primitivity [P+E]

The frame of a child depends only on the frame of the parent: $M\mapsto Mg_c$. Let $F[M',M]=\#\{c:Mg_c=M'\}$.

**Proposition 1.4.** (a) Starting from the identity, 7 frames occur at level 1 and all 24 frames of $SO(3,\mathbb Z)$ at
level 2; the set $\mathcal H$ of frames occurring in $\bigcup_m\mathcal T_m$ is all of $SO(3,\mathbb Z)$. (b) $F$ is a
$24\times24$ nonnegative integer matrix with all row and column sums 8 (it is the sum of the 8 right-multiplication
permutation matrices $R_{g_c}$). (c) $\operatorname{spec}F=\{8\}\cup\{2^{(\times20)}\}\cup\{0^{(\times3)}\}$; the
Perron–Frobenius eigenvalue 8 is simple with eigenvector $\mathbf 1/24$ (uniform frame frequencies $1/24$).
(d) $F^2>0$ entrywise: the frame substitution is primitive with primitivity exponent 2. (e) The stabilizer of the
chair cube set in $G$ has order 3, so the hull has 8 geometric orientations and 24 decorated prototiles.
*Proof.* Direct computation, `phase5a_frame_substitution.py` §1, matrix saved in `phase5a_frame_matrix.txt`; (b) is
also immediate: for fixed $c$, $M\mapsto Mg_c$ is a bijection of $G$. $\square$

Consequence used below: **every frame occurs among the 64 grandchildren of every tile.**

### 1.5 Structure of supertiles and the notch rule [P]

**Lemma 1.5 (parity).** Let $(M,T)\in\mathcal T_m$ be obtained by the child sequence $c_1,\dots,c_m$ (so
$T=2^{m-1}t_{c_1}+2^{m-2}g_{c_1}t_{c_2}+\dots+g_{c_1}\cdots g_{c_{m-1}}t_{c_m}$). Then the box center $p=T+M\mathbf 1$ is
an even lattice point iff $c_m$ is the central child, and an odd lattice point ($\equiv\mathbf 1$ mod 2) iff $c_m$ is
an outer child. *Proof.* Mod 2, $T\equiv g_{c_1}\cdots g_{c_{m-1}}t_{c_m}\equiv t_{c_m}$ (signed permutations fix
$\mathbf 1$ mod 2 and $4v\equiv0$), and $M\mathbf 1\equiv\mathbf 1$. So $p\equiv\mathbf 1+\mathbf 1\equiv 0$ for the
central child, $p\equiv\mathbf 1$ for outer children. $\square$ (Checked: box-corner parities $(1,1,1)$ for exactly
$8^{m-1}$ tiles and $(0,0,0)$ for $7\cdot8^{m-1}$ tiles, $m\le4$.)

Call a tile of $\mathcal T_m$ **central** or **outer** according to its last child index; the 8 tiles with the same
$c_1,\dots,c_{m-1}$ form a **level-1 supertile** $S=\sigma(M',T')$, the rigid image under $x\mapsto M'x+2T'$ of $S_1$.
Its **center** is $q(S)=2(T'+M'\mathbf 1)=2p(\text{parent})$; by Lemma 1.5 applied to the parent, $q(S)\equiv0$ or
$q(S)\equiv(2,2,2)$ mod 4, with all three coordinates in the same class. (Checked, §5 of the script.)

**Lemma 1.6 (geometry of one supertile).** In $S_1$: (i) the central chair has box $[1,3)^3$, center $(2,2,2)=q(S_1)$,
and its notch is the cube $[2,3)^3$, the corner cube of the missing 2-block $[2,4)^3$; (ii) the outer chair $v$ has box
$B_v$ (an odd-centered 2-block, one of the 7 occupied 2-blocks of the 4-box $[0,4)^3$), and its notch is the cube of
$B_v$ having $q(S_1)$ as a vertex, namely the cube $\mathbf 1+v$, which is a cube of the central chair; (iii) the 7
cubes of the central chair are exactly the 7 notches of the outer chairs. *Proof.* (i),(ii) from §1.1: the outer
chair $v$ has center $p_v=4v+D_vP_v\mathbf 1=\mathbf 1+2v$ and notch center $p_v+\tfrac12(\mathbf 1-2v)=\tfrac32\mathbf 1+v$,
i.e. the cube with corner $\mathbf 1+v$; its vertices are $\mathbf 1+v+\{0,1\}^3\ni\mathbf 1+v+(\mathbf 1-v)=(2,2,2)$.
(iii) $\{\mathbf 1+v:v\in P\}=[1,3)^3\setminus\{(2,2,2)\}$. $\square$ All statements transport to every level-1
supertile of every $\mathcal T_m$ by the rigid motion $x\mapsto M'x+2T'$ (which maps 2-blocks to 2-blocks and preserves
parity classes of centers because $2T'$ is even).

**Theorem 1.7 (notch rule).** In every $\mathcal T_m$, $m\ge1$: (a) every cube is the notch of at most one tile;
(b) each of the 7 cubes of a central tile is the notch of an outer tile of the same supertile; (c) at most one cube
of an outer tile is the notch of another tile; (d) the notch of an outer tile is a cube of the central tile of its own
supertile; the notch of a central tile is a cube of an outer tile of a *different* supertile (if that cube is in
$\mathcal T_m$). Hence a tile is central iff at least two (equivalently all seven) of its cubes are notches of other
tiles, and the supertile of a central tile $t_c$ is $\{t_c\}\cup\{t:\operatorname{notch}(t)\in t_c\}$.

*Proof.* (b),(d, first half) are Lemma 1.6(ii),(iii) transported. Two distinct outer tiles have distinct boxes
(tiles with the same box would share $\ge6$ cubes) which are odd-centered 2-blocks, hence disjoint (centers differ by
a nonzero even vector, so by $\ge2$ in some coordinate); likewise two distinct central tiles have disjoint
even-centered boxes. So a cube lies in at most one outer box and at most one central box.
(d, second half): the notch $x$ of the central tile of $S$ is the corner cube of the missing 2-block $B$ of $S$ nearest
$q(S)$. If $B$ is occupied, it is an occupied 2-block of another supertile $S'\ne S$ (an occupied 2-block of $S$ is
not missing), whose outer tile $t'$ in $B$ has notch the cube of $B$ at vertex $q(S')$. If $q(S')=q(S)$ then $S,S'$
have the same 4-box and overlap in $\ge6$ 2-blocks, impossible; so $x\ne\operatorname{notch}(t')$ and $x\in t'$.
(c): let $t$ be outer in $B$. No cube of $t$ lies in another outer box. A central box (center $q(S')$, even) meets the
odd-centered 2-block $B$ iff $q(S')$ is a vertex of $B$, and then in exactly the cube at that vertex. The vertices of
$B$ are $q(S)+2(s\circ\delta)$, $\delta\in\{0,1\}^3$, where $s\in\{\pm1\}^3$ points from $q(S)$ into $B$. Since all
supertile centers are $\equiv0$ or $(2,2,2)$ mod 4 with equal coordinate classes, and
$q(S)+2(s\circ\delta)\equiv q(S)+2\delta$ mod 4, only $\delta=0$ (giving $q(S)$, whose cube is $t$'s own notch) and
$\delta=\mathbf 1$ (one vertex) qualify. Hence at most one cube of $t$ is a notch of a central tile. (a) follows from
(b),(c),(d): a cube that is the notch of an outer tile lies in a central tile, a cube that is the notch of a central
tile lies in an outer tile, and the box-disjointness statements exclude two notches of the same kind. $\square$

Computational cross-check (`phase5a_frame_substitution.py` §5, levels 1–4): central tiles have exactly 7 notch cubes,
outer tiles have 0 or 1, no cube is the notch of two tiles, and every outer notch lies in the central tile of its
own supertile.

### 1.6 Unique composition and aperiodicity [P]

**Theorem 1.8 (recognizability).** Let $\omega\in\Omega$. Define a tile of $\omega$ to be central iff at least two of
its cubes are notches of other tiles of $\omega$. Then there are $z\in\mathbb Z^3$, unique mod $2\mathbb Z^3$, and a
unique $\omega'\in\Omega$ with $\omega=\sigma(\omega')+z$; the level-1 supertiles of $\omega$ are the sets
$\{t_c\}\cup\{t:\operatorname{notch}(t)\in t_c\}$, $t_c$ central.

*Proof.* Let $t\in\omega$ and let $Q$ be the patch of all tiles within distance 10 of $t$. $Q$ is legal: $Q+x\subset\mathcal T_m$.
The notch relation is translation invariant and involves only tiles within distance 2, so the number of notch cubes of
$t$ equals that of $t+x$ in $\mathcal T_m$, and by Theorem 1.7 it is 7 or $\le1$; central tiles of $\omega$ correspond to
central tiles of $\mathcal T_m$ under the translation. For central $t_c$, the set $S(t_c)=\{t_c\}\cup\{t:\operatorname{notch}(t)\in t_c\}$
is the translate by $-x$ of a level-1 supertile of $\mathcal T_m$, hence $S(t_c)=\sigma(M',T'_0)-x$ for a pose
$(M',T'_0)$, i.e. the rigid image of $S_1$ under $y\mapsto M'y+2T'_0-x$, with the frames of $\sigma(M',T'_0)$. Every
outer tile $t$ of $\omega$ has its notch in a central tile (Theorem 1.7(d) transported), so the sets $S(t_c)$ cover
$\omega$, and they are disjoint because the notch relation is a function. Any two supertiles $S(t_c),S(t_c')$ lie in
a common legal patch, hence their centers (defined by $q(S)=$ center of the 4-box) differ by a difference of centers in
some $\mathcal T_m$, which is even. Choose $z$ with all centers in $z+2\mathbb Z^3$ ($z$ unique mod 2). Then every
$S(t_c)-z$ has even center, so it equals $\sigma(M',T')$ with $T'\in\mathbb Z^3$ (a rigid image $y\mapsto M'y+w$ of $S_1$
with $w$ even is $\sigma(M',w/2)$); set $\omega'=\{(M',T')\}$. Its cube sets are disjoint and cover $\mathbb Z^3$ (the
$S(t_c)-z$ partition $\omega-z$ and $\sigma$ maps a pose onto the cubes of the scale-2 chair it defines). Legality of a
patch $Q'\subset\omega'$: $\sigma(Q')\subset\omega-z$ is contained in a legal patch $R$ with $R+x\subset\mathcal T_m$;
translation by $x$ carries the intrinsic supertile decomposition of $R$ to that of $\mathcal T_m$, whose supertiles
are $\sigma$ of the tiles of $\mathcal T_{m-1}$; centers in $\mathcal T_m$ and in $\omega-z$ are even, so $x$ is even
and $Q'+x/2\subset\mathcal T_{m-1}$. Thus $\omega'\in\Omega$. Uniqueness: the decomposition is intrinsic. $\square$

**Corollary 1.9 (aperiodicity).** No $\omega\in\Omega$ has a nonzero translation period. *Proof.* If
$\omega+p=\omega$, $p\in\mathbb Z^3\setminus0$, the intrinsic decomposition is $p$-invariant, so $p$ maps supertile
centers to supertile centers, whence $p\in2\mathbb Z^3$ and $\omega'+p/2=\omega'$ with $\omega'\in\Omega$ from Theorem
1.8. Iterating, $p/2^k\in\mathbb Z^3$ for all $k$, so $p=0$. $\square$

This settles the item marked "external, unverified" in the Phase 5 claim ledger for the decorated FR30 hull, without
appeal to the literature. (The undecorated chair tiling is a fortiori aperiodic.)

### 1.7 Repetitivity and minimality [P]

**Theorem 1.10.** Let $Q$ be a legal patch, $Q+x\subset\mathcal T_m$. For every $\omega\in\Omega$ and every $k\ge m+2$,
$\omega$ decomposes into level-$k$ supertiles $\sigma^k(t)+z_k$, $t\in\omega_k\in\Omega$, and every one of them contains
a translate of $Q$. Consequently $Q$ occurs in $\omega$ with gaps bounded by the diameter of $\mathcal T_{m+2}$
($\le 2^{m+3}\sqrt3$), every $\omega\in\Omega$ is the $\mathbb Z^3$-orbit closure of any other, and $(\Omega,\mathbb Z^3)$
is minimal. In particular every supertile $\mathcal T_m$ occurs (as a translate) in every $\omega\in\Omega$.

*Proof.* Iterating Theorem 1.8 (using $\sigma(\omega+z)=\sigma(\omega)+2z$) gives $\omega=\sigma^k(\omega_k)+z_k$. Let
$t\in\omega_k$. By Proposition 1.4(d) some grandchild $t_I=(I,T_I)$ of $t$ has the identity frame, and
$\sigma^m(I,T_I)=\mathcal T_m+2^mT_I$ (induction on $m$ from $\varphi_c(I,T)=(g_c,2T+t_c)$ and $\sigma(X+z)=\sigma(X)+2z$). Hence
$Q+x+2^mT_I\subset\sigma^{m+2}(t)$ for every pose $t$. For $k\ge m+2$ every level-$k$ supertile $\sigma^k(t')$ is the
union of the level-$(m+2)$ supertiles $\sigma^{m+2}(s)$, $s\in\sigma^{k-m-2}(t')$, so it contains a translate of $Q$.
The level-$k$ supertiles cover $\omega$ and have bounded diameter, giving bounded gaps. For $\omega,\omega'\in\Omega$ and $R>0$, the radius-$R$ patch of $\omega'$ around
the origin is legal, hence occurs in $\omega$ at some $x_R$, so $\omega-x_R\to\omega'$: $\omega'\in\overline{\omega+\mathbb Z^3}$.
Thus every orbit is dense in $\Omega$. $\square$

### 1.8 Unique ergodicity and patch frequencies [C]

For primitive FLC substitution tilings the tiling dynamical system is uniquely ergodic, equivalently all patch
frequencies exist uniformly (for every element and every van Hove sequence, with the same limit):
Solomyak, *Dynamics of self-similar tilings*, Ergodic Theory Dynam. Systems 17 (1997) 695–738 [unverified citation;
title/journal/abstract confirmed by search snippet, which states unique ergodicity]; the equivalence "uniquely
ergodic $\Leftrightarrow$ uniform patch frequencies" for FLC Delone sets is Lee–Moody–Solomyak, Ann. Henri Poincaré 3
(2002) [unverified citation]. The hypotheses are verified here: primitivity (Prop. 1.4), FLC (Prop. 1.2),
aperiodicity (Cor. 1.9). The frame frequencies are $1/24$ each (Prop. 1.4(c)); the exact recursion of Theorem A in
`PHASE5_UNIVERSAL_GEOMETRIC_DYNAMICS.md` gives panel and plaquette-class frequencies along the supertile sequence.
The subshift $(\Omega,\mathbb Z^3)$ is a constant-length ($2\times2\times2$) block-substitution subshift over
$\mathcal A$, the standard framework of Mozes (J. Anal. Math. 53 (1989) 139–186) [unverified citation; metadata
confirmed]. Whether the decorated hull is limit-periodic in the strict sense (an almost 1–1 extension of the 2-adic
odometer $\mathbb Z_2^3$ with pure point dynamical spectrum) is **expected** from the chair structure but **not proved
here**; only the geometric (undecorated) chair hull's limit-periodicity is standard (Baake–Grimm, *Aperiodic Order* I,
CUP 2013 [unverified citation, not found by search; from recollection]).

---

## 2. The operator

### 2.1 Definition

For $\omega\in\Omega$ let $V(\omega)$ be its set of tiles and $\mathcal H_\omega=\ell^2(V(\omega))\otimes\mathbb C^2$.
A **panel** is a unit face shared by cubes of two different tiles $a,b$; let $\mathbf n_f$ be its unit normal from $a$
to $b$ and $C^{(f)}_{ab}=(\boldsymbol\sigma\cdot M_a^\top\mathbf n_f)(\boldsymbol\sigma\cdot M_b^\top\mathbf n_f)\in Q_8\subset SU(2)$;
reversing orientation gives $C_{ba}=(\boldsymbol\sigma\cdot M_b^\top\mathbf n)(\boldsymbol\sigma\cdot M_a^\top\mathbf n)=C_{ab}^\dagger$
(signs cancel). Define
$$(\mathcal A_\omega\psi)_a=\sum_{f=(a,b)}C^{(f)}_{ab}\psi_b,\qquad H_\omega=24\cdot\mathbb 1-\mathcal A_\omega,$$
the sum over all panels at $a$ (with multiplicity: two tiles may share several panels). **Domain:** all of $\mathcal H_\omega$
(bounded, Prop. 2.2). No boundary conventions are needed in infinite volume; finite-volume conventions (free $D-A$,
pinned $24-A$) are compressions, §3.

**Lemma 2.1 (coordination).** Every chair has exactly 24 external unit faces ($7\cdot6-2\cdot9$, the $2\times2\times2$
block has 12 internal adjacencies and removing a cube removes 3), and in a tiling of $\mathbb R^3$ every external face
is shared with another tile. Hence every tile of every $\omega\in\Omega$ has exactly 24 panels. (Checked: in
$\mathcal T_m$, $m\le5$, every tile with a cube not touching the supertile surface has degree 24, and every tile of
degree $<24$ touches the surface.)

### 2.2 Boundedness, self-adjointness, positivity [P]

**Proposition 2.2.** $\mathcal A_\omega$ is bounded with $\|\mathcal A_\omega\|\le24$ and self-adjoint; $H_\omega$ is
bounded self-adjoint with $0\le H_\omega\le48$, and for finitely supported $\psi$
$$\langle\psi,H_\omega\psi\rangle=\sum_{f=(a,b)}\|\psi_a-C^{(f)}_{ab}\psi_b\|^2 .$$
*Proof.* Schur test: $\|(\mathcal A\psi)_a\|\le\sum_{f\ni a}\|\psi_{b(f)}\|$ (each $C$ is unitary), so by Cauchy–Schwarz
$\|\mathcal A\psi\|^2\le\sum_a24\sum_{f\ni a}\|\psi_{b(f)}\|^2=24\sum_b\|\psi_b\|^2\cdot\#\{f\ni b\}=24^2\|\psi\|^2$.
Symmetry on finitely supported vectors: $\langle\phi,\mathcal A\psi\rangle=\sum_f[\langle\phi_a,C_{ab}\psi_b\rangle+\langle\phi_b,C_{ab}^\dagger\psi_a\rangle]$
is symmetric under $\phi\leftrightarrow\psi$ with conjugation, and a bounded symmetric operator on a dense domain
extends to a bounded self-adjoint one. Expanding $\sum_f\|\psi_a-C\psi_b\|^2=\sum_f(\|\psi_a\|^2+\|\psi_b\|^2)-2\operatorname{Re}\sum_f\langle\psi_a,C\psi_b\rangle=24\|\psi\|^2-\langle\psi,\mathcal A\psi\rangle$
by Lemma 2.1. So $H_\omega\ge0$, and $H_\omega\le24+\|\mathcal A\|\le48$. $\square$

### 2.3 Gauge action [P]

For a family $U_a\in U(2)$, $\mathcal U=\bigoplus_aU_a$ is unitary on $\mathcal H_\omega$ and
$\mathcal UH_\omega\mathcal U^\dagger=24-\mathcal A'$ with links $C'_{ab}=U_aC_{ab}U_b^\dagger$ (still $C'_{ba}=C'^\dagger_{ab}$);
the spectrum and all unitary invariants are gauge invariant; $Q_8$-valuedness is preserved iff $U_a\in Q_8$ up to
phases. Gauge-invariant local observables are functions of holonomies around closed tile cycles (conjugacy classes in
$Q_8$), the objects renormalized exactly by Theorem A of the Phase 5 document.

### 2.4 Covariance [P]

**Proposition 2.3.** (a) *Translations:* for $x\in\mathbb Z^3$ let $(\tau_x\psi)_{a+x}=\psi_a$; then
$\tau_xH_\omega\tau_x^{-1}=H_{\omega+x}$. (b) *Rotations:* $\Omega$ is invariant under $g\in SO(3,\mathbb Z)$ acting by
$(M,T)\mapsto(gM,gT)$, and the relabeling unitary $\rho_g$ satisfies $\rho_gH_\omega\rho_g^{-1}=H_{g\omega}$ with **no spin
rotation**. (c) *Strong pattern equivariance:* the matrix element $(H_\omega)_{ab}$ depends only on the two poses
$a,b$ (radius-1 local rule). *Proof.* (a),(c): $C^{(f)}_{ab}$ depends on $(M_a,M_b,\mathbf n_f)$ only. (b): under
$M\mapsto gM$, $\mathbf n\mapsto g\mathbf n$, so $M^\top\mathbf n\mapsto M^\top g^\top g\mathbf n=M^\top\mathbf n$ and every
link is unchanged; $g\Omega\subset\Omega$ because $g\mathcal T_m=\sigma^m(g,0)\subset\mathcal T_{m+2}$ up to translation
(frame $g$ occurs at level 2). $\square$ (Computationally: for all 24 frames $g$ and $m=1,2$, the orientation-free
panel lists with $Q_8$ labels of $\sigma^m(g,0)$ and $\mathcal T_m$ coincide, script §3.)

### 2.5 Quaternionic structure [P]

**Proposition 2.4 (Kramers).** Let $J=\mathbb 1\otimes(i\sigma_y)\mathcal K$ with $\mathcal K$ complex conjugation in the
standard basis. Then $J$ is antiunitary, $J^2=-1$, and $JH_\omega=H_\omega J$. Consequently every eigenvalue of every
finite approximant has even multiplicity, and every spectral subspace of $H_\omega$ is $J$-invariant, hence of even or
infinite dimension. *Proof.* For $U=a\mathbb 1+i\mathbf b\cdot\boldsymbol\sigma\in SU(2)$ ($a,\mathbf b$ real),
$\sigma_y\bar U\sigma_y=U$ since $\sigma_y\bar\sigma_k\sigma_y=-\sigma_k$. All blocks of $H_\omega$ are $24\mathbb 1$ or $-C$ with
$C\in SU(2)$, so $JH_\omega J^{-1}=H_\omega$; $J^2=(i\sigma_y)(\overline{i\sigma_y})=-\sigma_y^2=-1$. $\square$ (The audit
script verified the symmetry and the Kramers pairing at level 1; the doubly degenerate lowest eigenvalues in
`phase5_dynamics_boundary.txt` are instances.)

### 2.6 Constancy of the spectrum on the hull [P]

**Theorem 2.5.** For all $\omega,\omega'\in\Omega$, $\sigma(H_\omega)=\sigma(H_{\omega'})$.
*Proof.* Let $E\in\sigma(H_{\omega'})$. By Weyl's criterion for bounded self-adjoint operators there are unit
$\phi_n$ with $\|(H_{\omega'}-E)\phi_n\|\to0$; truncating to finite patches and renormalizing (the truncation error
$\|H-E\|\,\|\phi_n-\chi_R\phi_n\|$ tends to 0 for $R\to\infty$) we may take $\phi_n$ finitely supported. Let $Q_n$ be
the patch of tiles within distance 1 of $\operatorname{supp}\phi_n$; it is legal, so by Theorem 1.10 a translate
$Q_n+x_n\subset\omega$. Put $\psi_n=\tau_{x_n}\phi_n$. Since $(H\psi)_a$ for $a\in Q_n$ involves only panels inside
$Q_n$ and the constant 24, and the links are determined by the poses (Prop. 2.3(c)),
$(H_\omega-E)\psi_n=\tau_{x_n}(H_{\omega'}-E)\phi_n$, so $E\in\sigma(H_\omega)$. Exchange roles. $\square$

Hence $E_{\rm bulk}:=\inf\sigma(H_\omega)$ is well defined, independent of $\omega$. (This is the Lenz–Stollmann /
Bellissard constancy theorem for minimal hulls — *Algebras of random operators associated to Delone dynamical systems*,
Math. Phys. Anal. Geom. 6 (2003) [unverified citation; arXiv math-ph/0210031 located by search] — proved here directly
because the hypotheses are exactly those established in §1.)

### 2.7 Integrated density of states [P for the supertile limit, C for the identification]

Let $N^{\rm free}_m(E)$, $N^{\rm pin}_m(E)$ be the eigenvalue counting functions of $H^{\rm free}_m=D-A$ and
$H^{\rm pin}_m=24-A$ on $\mathcal T_m$ divided by $\dim\mathcal H_m=2\cdot8^m$. Theorem 4.3 below proves that both converge
uniformly in $E$ to the same distribution function $N_\infty$ with rate $O(2^{-m})$. The *hull IDS* of the literature is
the uniform-in-$E$ limit of $\#\{\text{eigenvalues}\le E\}/|Q_n|$ for the compressions of $H_\omega$ to any van Hove
sequence of patches $Q_n\subset\omega$, for any $\omega$; its existence for strictly ergodic FLC Delone systems with
uniform patch frequencies is the Banach-space-valued ergodic theorem of Lenz–Stollmann, *An ergodic theorem for Delone
dynamical systems and existence of the integrated density of states*, J. Anal. Math. 97 (2005), arXiv math-ph/0310017
[unverified citation; abstract confirmed by search: "strictly ergodic Delone dynamical systems … IDS exists in the
sense of uniform convergence in distribution"], with the discrete-graph version Lenz–Veselić, Math. Z. 263 (2009),
arXiv 0709.2836 [unverified citation; abstract confirmed]. Its hypotheses hold here (minimality: Thm 1.10; unique
ergodicity: §1.8 [C]; finite range and equivariance: Prop. 2.3). Taking $Q_n=$ the copies of $\mathcal T_n$ inside
$\omega$ (they exist by Thm 1.10 and form a van Hove sequence, surface $24\cdot4^n$ vs. volume $7\cdot8^n$) identifies
the hull IDS with $N_\infty$ (normalized per spinor–tile dimension $2\cdot8^m$; the per-tile IDS is $2N_\infty$, the
per-cube IDS is $2N_\infty/7$). Lenz–Veselić also give: a jump of
the IDS occurs iff there is a finitely supported eigenfunction; the hull IDS is the unique-ergodic-measure trace
(Bellissard's Shubin formula). Gap labelling: on a spectral gap the IDS takes values in the $\mathbb Z$-module of
patch frequencies (Bellissard 1992 [unverified citation]; proved for $\mathbb Z^d$ Cantor actions by
Bellissard–Benedetti–Gambaudo, Comm. Math. Phys. 261 (2006) 1–41, Kaminker–Putnam, Michigan Math. J. 51 (2003),
Benameur–Oyono-Oyono 2003 [all unverified citations; metadata confirmed by search]). For FR30 this module contains the
frame frequencies $1/24$ and the panel/plaquette frequencies of Theorem A.

---

## 3. Theorem (compression) and the two-sided bracket for $E_{\rm bulk}$

### 3.1 Compression [P]

Let $\Pi_m$ be the orthogonal projection of $\mathcal H_\omega$ onto $\ell^2(\text{a copy of }\mathcal T_m\text{ in }\omega)\otimes\mathbb C^2$.

**Lemma 3.1.** $\Pi_mH_\omega\Pi_m$ restricted to its range is unitarily equivalent to $H^{\rm pin}_m$ (the repo's
pinned operator), for every copy of $\mathcal T_m$ in every $\omega$, including rotated copies $\sigma^m(g,T)$.
*Proof.* $(\Pi_mH\Pi_m\psi)_a=24\psi_a-\sum_{f=(a,b),\,b\in\mathcal T_m}C_{ab}\psi_b$ by Lemma 2.1: the diagonal is 24
for every tile and only internal panels survive — exactly `hopping(..., pinned=True)`. Rotated copies have identical
links by Prop. 2.3(b). $\square$

**Theorem 3.2.** (a) $\lambda_{\min}(H^{\rm pin}_m)\ge E_{\rm bulk}$ for every $m$. (b) $m\mapsto\lambda_{\min}(H^{\rm pin}_m)$
is non-increasing. (c) $\lim_m\lambda_{\min}(H^{\rm pin}_m)=E_{\rm bulk}$.
*Proof.* (a) For a unit vector $\psi$ in the range of $\Pi_m$, $\langle\psi,\Pi_mH\Pi_m\psi\rangle=\langle\psi,H_\omega\psi\rangle\ge E_{\rm bulk}$.
(b) $\mathcal T_m\subset\mathcal T_{m+1}$ as the $(0,0,0)$-child with identical poses (verified $m\le3$ as pose sets,
and in general because $\varphi_{(0,0,0)}=(I,0)\mapsto(I,0)$ so the words $c_1=(0,0,0),c_2,\dots,c_{m+1}$ enumerate
$\mathcal T_m$ inside $\mathcal T_{m+1}$), and the panels among the tiles of $\mathcal T_m$ inside $\mathcal T_{m+1}$ are
exactly those of $\mathcal T_m$ with identical links (verified $m\le3$; in general the panels are determined by the
cube sets and the links by the poses). Hence $H^{\rm pin}_m$ is a compression of $H^{\rm pin}_{m+1}$ and
$\lambda_{\min}$ can only increase under compression. (c) $E_{\rm bulk}=\inf\{\langle\psi,H_\omega\psi\rangle:\|\psi\|=1\}$
and, $H_\omega$ being bounded, the infimum over finitely supported unit vectors is the same. A finitely supported
$\psi$ lives on a finite patch $Q$, which is legal: $Q+x\subset\mathcal T_m$; the form $\langle\psi,H_\omega\psi\rangle=24\|\psi\|^2-\sum_{f\subset Q}2\operatorname{Re}\langle\psi_a,C_f\psi_b\rangle$
involves only panels inside $Q$, so it equals $\langle\tau_x\psi,H^{\rm pin}_m\tau_x\psi\rangle\ge\lambda_{\min}(H^{\rm pin}_m)$.
Thus $E_{\rm bulk}\ge\inf_m\lambda_{\min}(H^{\rm pin}_m)$, and with (a),(b) the limit equals $E_{\rm bulk}$. $\square$

Remark. (c) holds for every single $\omega$ without minimality (only legality of patches is used), and (a) needs only
that $\mathcal T_m$ occurs in $\omega$, which Theorem 1.10 guarantees. No analogous inequality holds for $H^{\rm free}_m$:
its boundary tiles have diagonal $<24$ and its bottom ($\to\approx5.25$) is a surface band, as the Phase 5 document found.

### 3.2 Certified upper bounds [P+E]

For any vector $p$, $E_{\rm bulk}\le\lambda_{\min}(H^{\rm pin}_m)\le\langle p,H^{\rm pin}_mp\rangle/\langle p,p\rangle$. The
script `phase5a_certified_upper_bound.py` rounds the LOBPCG (or dense) ground vector to a Gaussian-integer vector
($2^{24}\psi$) and evaluates the Rayleigh quotient **exactly in integer arithmetic** (all matrix entries lie in
$\{0,\pm1,\pm i,24\}$); the result is a rational number that bounds $E_{\rm bulk}$ independently of floating-point error
(`phase5a_certified_upper_bound.txt`):

| level $m$ | $\dim$ | floating $\lambda_{\min}$ (repo) | certified rational Rayleigh quotient | 
|---|---|---|---|
| 2 | 128 | 10.77695 | $3033441878476984/281474975238239=10.776950512$ |
| 3 | 1024 | 9.37847 | $1319902366216346/140737490935935=9.378470210$ |
| 4 | 8192 | 8.91963 | $1255326883536563/140737482371670=8.919634360$ |
| 5 | 65536 | 8.79701 | $2476138622922986/281474983842677=8.797011333$ (LOBPCG tol $10^{-4}$, residual $6.6\cdot10^{-5}$; the bound is rigorous regardless) |
| 6 | 524288 | 8.77013 | not certified (vector not saved; 2742 s run exceeds this task's budget) |

The level-6 value 8.77013 is a Rayleigh–Ritz value (LOBPCG reports Rayleigh quotients of Ritz vectors), hence an upper
bound for $\lambda_{\min}(H^{\rm pin}_6)$ up to double-precision rounding ($\sim10^{-12}$ relative); it is not an
exact-arithmetic certificate. **Theorem 3.2 + the table give the rigorous statement: $E_{\rm bulk}\le8.7970114$
(certified, level 5), and $E_{\rm bulk}\le8.77013$ modulo IEEE rounding (level 6).** The
decrements $1.399,0.459,0.123,0.027$ are consistent with convergence but no rate theorem is available (the Dirichlet
law $\lambda_{\min}(H^{\rm pin}_m)-E_{\rm bulk}\asymp4^{-m}$ would follow from an effective-mass description and is
itself open, §5).

### 3.3 A certified positive lower bound [P+E]

**Lemma 3.3 (plaquette decomposition).** For $\omega\in\Omega$ and each lattice edge $e$ let $c_1,\dots,c_4$ be the four
cubes around $e$ in cyclic order and $h_e(\psi)=\sum_{i=1}^4[\,t(c_i)\ne t(c_{i+1})\,]\;\|\psi_{t(c_i)}-C_{t(c_i)t(c_{i+1})}\psi_{t(c_{i+1})}\|^2$
(the link across the face $c_ic_{i+1}$). Then $\langle\psi,H_\omega\psi\rangle=\tfrac14\sum_eh_e(\psi)$ for finitely
supported $\psi$. *Proof.* Each unit face contains exactly 4 lattice edges and each lattice edge is surrounded by 4
cubes, all present in a tiling of $\mathbb R^3$; so $\sum_eh_e=4\sum_{f\text{ panel}}\|\psi_a-C_f\psi_b\|^2$, and
Prop. 2.2 finishes. $\square$

$h_e$ is a nonnegative Hermitian form on $\ell^2(V(e))\otimes\mathbb C^2$, $V(e)$ the (1 to 4) distinct tiles around $e$,
so $h_e\ge\lambda_{\min}(h_e)\Pi_{V(e)}$ and
$$H_\omega\ \ge\ \tfrac14\sum_aS(a)\,\Pi_a,\qquad S(a)=\sum_{e\ \text{touching }a}\lambda_{\min}(h_e),\qquad
E_{\rm bulk}\ \ge\ \tfrac14\inf_{a}S(a). \tag{3.1}$$
$S(a)$ depends only on the **vertex-star type** of $a$: the tile $a$ together with all tiles sharing at least a vertex
with it, with frames, modulo rigid motion (encoded by the relative poses $(M_a^\top M_b,\,M_a^\top(T_b-T_a))$).

**Lemma 3.4 (closure of vertex-stars).** If $\omega=\sigma(\omega')+z$ and $a$ is a child of $A\in\omega'$, the vertex-star
of $a$ is contained in $\sigma(\text{vertex-star of }A)+z$. *Proof.* Fine cubes $x,x'$ with $|x-x'|_\infty\le1$ have
parents $\lfloor x/2\rfloor,\lfloor x'/2\rfloor$ with $|\cdot|_\infty\le1$. $\square$
Hence the collared map $\Phi$: (legal vertex-star type) $\mapsto$ (the 8 vertex-star types of the children of its
center) is well defined, and the set $\mathcal V$ of legal vertex-star types satisfies $\Phi(\mathcal V)\subset\mathcal V$.

**Lemma 3.5.** $\mathcal V$ equals the forward $\Phi$-orbit of any single legal vertex-star type $s_0$. *Proof.*
The forward orbit $\mathcal O(s_0)$ is the set of vertex-star types of all tiles of $\sigma^n(t_0)$, $n\ge0$, $t_0$ the
center of $s_0$ (induction on $n$ with Lemma 3.4). It is legal, so $\mathcal O(s_0)\subset\mathcal V$. Conversely a legal
star $s\subset\mathcal T_m$ occurs by Theorem 1.10 inside $\sigma^{m+2}(t)$ for *every* tile $t$, in particular
inside $\sigma^{m+2}(t_0)$, as a complete star (its copy is a star of the corresponding tile). $\square$

Computation (`phase5a_star_closure_lower_bound.py`): from one interior tile of $\mathcal T_3$ (star of 27 tiles) the
orbit closes after 3 rounds with $|\mathcal V|=72$ types (9 to 27 tiles each); $\Phi(\mathcal V)\subset\mathcal V$
re-verified; the complete stars of $\mathcal T_3,\mathcal T_4,\mathcal T_5$ number 40, 70, 72 types, all in $\mathcal V$,
and $\mathcal T_5$ realizes all 72; a second seed gives the same 72. Every tile touches exactly 48 inter-tile
plaquettes, of which 19 to 37 are non-flat; 207 distinct plaquette signatures occur, with
$\lambda_{\min}(h_e)\in\{0,\ 2-2\cos\tfrac\pi8,\ 2-\sqrt3,\ 2-\sqrt2,\ 1,\ 2\}$, exactly the values $2-2\cos(\theta/\ell)$
of a simple $\ell$-cycle ($\ell=2,3,4$) with holonomy angle $\theta\in\{\pi/2,\pi\}$ ($W=\pm i,\pm j,\pm k$ resp. $-1$).
For each non-flat signature the script certifies $\lambda_{\min}(h_e)\ge\mu_e:=\lambda_{\min}-2\cdot10^{-6}$ (rounded to
$10^{-6}$) by **exact rational $LDL^*$ elimination** of $h_e-\mu_e$ (positive pivots $\Leftrightarrow$ positive
definite); flat signatures get $\mu_e=0$. The minimum over the 72 types of $\sum_e\mu_e$ is $3137451/500000$.

**Theorem 3.6 (positive bulk gap).** $E_{\rm bulk}\ \ge\ \dfrac{3137451}{2\,000\,000}=1.5687255>0.$ Consequently
$\sigma(H_\omega)\subset[1.5687,\,48]$ for every $\omega\in\Omega$ and $[0,1.5687)$ is a spectral gap. *Proof.* (3.1) with
Lemmas 3.4–3.5 and the certified $\mu_e$. $\square$

Together with §3.2: **$1.5687\le E_{\rm bulk}\le 8.7971$ (fully certified), $E_{\rm bulk}\le8.77013$ (IEEE).**
The lower bound is crude (the plaquette decomposition discards all interference between the 48 plaquettes of a tile);
the method extends to larger clusters (2-blocks of cubes, whole vertex-stars) with weights $1/k_X$ for the covering
multiplicity, at the cost of certifying larger $\lambda_{\min}$ exactly. This is the "positive local decomposition"
route; the periodic-approximant route is discussed in §5.

### 3.4 Comparison: trivial connection [P]

For the trivial connection ($C\equiv\mathbb 1$) on the same hull, $\inf\sigma(24-\mathcal A^{\rm triv}_\omega)=0$: the
normalized indicator of the tiles in a ball of radius $R$ (times a fixed spinor) satisfies
$\|(24-\mathcal A^{\rm triv})\psi_R\|^2\le 24^2\cdot\#\{\text{tiles within distance 1 of the sphere}\}/\#\{\text{tiles in the ball}\}\to0$.
So the gap $[0,E_{\rm bulk})$ of Theorem 3.6 is entirely a flux effect of the $Q_8$ decoration (cf. the pinned trivial
bottoms $4.75,1.67,0.50\to0$ in `phase5_dynamics_boundary.txt`, ratio $\to1/4$).

---

## 4. Theorem (boundary independence of the IDS) [P]

**Lemma 4.1 (rank inequality).** Let $A,B$ be Hermitian $n\times n$ with $\operatorname{rank}(A-B)\le r$ and
$N_A(E)=\#\{i:\lambda_i(A)\le E\}$. Then $|N_A(E)-N_B(E)|\le r$ for all $E$. *Proof.* By the min-max principle
$N_A(E)=\max\{\dim W:\langle\psi,A\psi\rangle\le E\|\psi\|^2\ \forall\psi\in W\}$. Take such a $W$ of dimension $N_A(E)$;
$W\cap\ker(A-B)$ has dimension $\ge N_A(E)-r$ and on it $B=A$, so $N_B(E)\ge N_A(E)-r$. Exchange $A,B$. $\square$

**Lemma 4.2 (boundary tiles).** Let $b_m=\#\{a\in\mathcal T_m:\deg a<24\}$. Every such tile has a cube face on the
surface of $\mathcal T_m$, which has area $24\cdot4^m$ unit faces (a chair of side $2^m$: the cube $[0,2^{m+1}]^3$ has
area $6\cdot4^{m+1}$ and removing the corner cube $[2^m,2^{m+1}]^3$ exposes three faces of the same area as the three
it removes). Hence $b_m\le24\cdot4^m$ and $b_m/8^m\le24\cdot2^{-m}\to0$. Measured: $b_m=8,53,287,1331,5723,23723$
($m=1..6$), $b_m/8^m=1,0.83,0.56,0.33,0.17,0.09$.

**Theorem 4.3.** (a) $\|N^{\rm pin}_m-N^{\rm free}_m\|_\infty\le b_m/8^m\le24\cdot2^{-m}$.
(b) $\|N^{\rm free}_{m+1}-N^{\rm free}_m\|_\infty\le24\cdot2^{-m}$, so $N^{\rm free}_m\to N_\infty$ uniformly with
$\|N^{\rm free}_m-N_\infty\|_\infty\le48\cdot2^{-m}$, and $N^{\rm pin}_m\to N_\infty$ with
$\|N^{\rm pin}_m-N_\infty\|_\infty\le72\cdot2^{-m}$. (c) $N_\infty$ is the hull IDS (§2.7, [C] for the identification).
*Proof.* (a) $H^{\rm pin}_m-H^{\rm free}_m=\operatorname{diag}(24-\deg)\otimes\mathbb 1_2$ has rank $\le2b_m$; divide
Lemma 4.1 by $2\cdot8^m$. (b) $\mathcal T_{m+1}$ is the disjoint union of the 8 children $\sigma^m(\varphi_c(I,0))$, each
carrying a copy of $H^{\rm free}_m$ (Prop. 2.3(b): rotated supertiles have identical links). Thus
$H^{\rm free}_{m+1}=\bigoplus_cH^{\rm free}_m+K$ where $K$ collects the degree terms and hoppings of panels joining two
children; $K$ is supported on the span of the spinor components of tiles having such a panel. Such a tile has a face
on the surface of one of the 8 children, whose total surface is $8\cdot24\cdot4^m$ faces, so there are at most
$192\cdot4^m$ such tiles and $\operatorname{rank}K\le384\cdot4^m$; dividing by $2\cdot8^{m+1}$ gives $24\cdot2^{-m}$.
Summing the geometric series gives the uniform limit and the rates. (c) §2.7. $\square$

This sharpens Phase 5 Theorem D / Phase 2 Theorem 2.6 only by making all constants explicit; the measured interface
counts $T_k=8,53,269,1277,5597$ (Phase 2; re-computed here for $k\le5$ with identical values, giving the actual
increments $T_k/8^k=1,0.83,0.53,0.31,0.17$) are far below the crude bound $192\cdot4^{k-1}$. Consequence: the free surface band
$[\approx5.25,E_{\rm bulk})$ carries zero density of states in the limit; it is invisible in $N_\infty$ and in every
bulk-averaged quantity, visible only in boundary-sensitive observables and in the lowest finitely many free
eigenvalues.

---

## 5. What is not established, and the exact remaining obligations for H2–H5

### 5.1 Open items on the spectrum (H2)

1. **Value of $E_{\rm bulk}$.** Rigorous: $1.5687\le E_{\rm bulk}\le8.7971$ (certified), $\le8.77013$ (IEEE). The
   numerical estimate $E_{\rm bulk}\approx8.76$ rests on extrapolating decrements whose ratios $0.33,0.27,0.22$ are not
   proven to be geometric. **Obligation H2-a:** save the level-6 Ritz vector and certify its Rayleigh quotient exactly
   (same method as §3.2; cost $\approx$ one level-6 LOBPCG run, 2742 s). **Obligation H2-b:** sharpen the lower bound
   by cluster decompositions over $\mathcal V$ (vertex-star clusters: 72 forms of dimension $\le54$, covering
   multiplicities computable exactly). **Obligation H2-c:** a rate theorem for $\lambda_{\min}(H^{\rm pin}_m)\downarrow E_{\rm bulk}$;
   the Dirichlet law $\asymp4^{-m}$ requires extended edge states (H3) and an effective-mass description (H5).
2. **Is $E_{\rm bulk}$ attained?** Unknown whether $E_{\rm bulk}$ is an eigenvalue of $H_\omega$ (an $\ell^2$ state), and
   whether $\sigma(H_\omega)$ near $E_{\rm bulk}$ is absolutely continuous, singular continuous or pure point. By
   Lenz–Veselić [C], an $\ell^2$ eigenvalue of the hull with positive IDS jump would be realized by finitely supported
   eigenvectors; checking the supertile spectra for exact degeneracies growing like $8^m$ would detect this (not done).
3. **Further gaps.** Not established; the Phase 2 observation "no persistent gaps of relative width $>2\%$ at levels
   3–4" is [N]. Gap labelling [C] constrains any gap's IDS value to the patch-frequency module.
4. **Periodic controls.** The chair tiles $\mathbb Z^3$ periodically by translations (the lattice
   $\{x:x_1+2x_2+4x_3\equiv0\bmod7\}$ has $P$ as a complete residue system), so periodic approximants exist: arrange
   level-$k$ supertiles (identity frame) on the scaled lattice $2^k\Lambda_7$. Their seams are *illegal* patches, so
   their spectra may contain seam-localized states; only IDS-type statements survive (rank inequality with seam
   fraction $O(2^{-k})$). This is a precise construction for the H2 "matched periodic controls", not yet computed.

### 5.2 Nature of the states near $E_{\rm bulk}$ (H3) [open]

Only numerical data exist (`phase5_dynamics_boundary.txt`, `phase5_bulk_bottom_lobpcg.txt`): the pinned ground state
has boundary weight $\to0$ and tile IPR $0.0373,0.0125,0.00223,0.00061,0.00016$ at levels 2–6, i.e. $\mathrm{IPR}\cdot n=
2.4,6.4,9.1,20.0,41.9$. **The last three roughly double per level**, i.e. $\mathrm{IPR}\propto n^{-2/3}$ ($D_2\approx2$
in three dimensions), which is *not* the scaling of an extended state ($\mathrm{IPR}\cdot n\to$ const) and not that of
a localized one ($\mathrm{IPR}\to$ const). The Phase 5 text's gloss "extended" is therefore not supported by its own
numbers at face value; the state may be critical (multifractal), or concentrated on a two-dimensional substructure of
the hierarchy (e.g. an interface of level-$(m-1)$ supertiles), or the sequence may not yet be asymptotic. **Obligation
H3:** compute the full multifractal spectrum / $D_q$ of the lowest Kramers pair at levels 4–6, its weight on
supertile interfaces of each level, and its sensitivity to the pinning potential (replace 24 by $24+\epsilon$ on
boundary tiles). Any theorem on extended vs. localized states would need, beyond this, a Fourier/Bloch-type analysis
unavailable for aperiodic hulls, or a Lyapunov/transfer-matrix structure absent in $d=3$.

### 5.3 Homogenization (H4) [open]

A statement of the form "$H_\omega-E_{\rm bulk}$ is unitarily close at long wavelength to $-\nabla\!\cdot D\nabla\otimes\mathbb 1_2$"
requires (i) a Bloch-like or two-scale theory for the hull, (ii) extended generalized eigenfunctions at $E_{\rm bulk}$,
(iii) control of the surface band (Theorem 4.3 shows it is measure zero but not that it does not scatter). Kozlov's
almost-periodic homogenization (Mat. Sb. 107 (1978) 199–217 [unverified citation; metadata confirmed]) and the
Jikov–Kozlov–Oleinik monograph (Springer 1994 [unverified citation]) treat divergence-form operators whose bottom of
spectrum is 0 with *constant* corrector-free ground state; here the bottom is a frustrated edge $E_{\rm bulk}>0$ with a
nontrivial ground state, the analogue of an *internal* band edge, for which even the periodic theory needs
non-degeneracy of the edge (Birman–Suslina, St. Petersburg Math. J. 15 (2004) [unverified citation; metadata confirmed];
Kuchment, Bull. AMS 53 (2016) [unverified citation]; Allaire–Piatnitski, Comm. Math. Phys. 258 (2005) [unverified
citation; not found by search, from recollection]). **Precise obstruction:** no Floquet decomposition exists on
$\Omega$; the natural substitute is the sequence of periodic approximants of §5.1(4), for which one needs
(a) strong resolvent convergence $H^{(k)}_{\rm per}\to H_\omega$ (true for the bulk part; the seams must be shown
spectrally harmless near $E_{\rm bulk}$, i.e. no seam states below the bulk edge), (b) non-degeneracy of the band
edge of $H^{(k)}_{\rm per}$ uniformly in $k$, (c) convergence of the effective-mass tensors $D^{(k)}$. None is done.

**Proposition 5.1 (isotropy, conditional) [P].** Suppose an effective-mass tensor $D$ exists in any sense covariant
under the symmetries of the hull (for instance as the $k\to0$ Hessian of a dispersion relation obtained from
periodic approximants that are themselves $SO(3,\mathbb Z)$-covariant, or as a limit of covariant quadratic forms).
Then $D=D_0\mathbb 1$ is isotropic. *Proof.* By Prop. 2.3(b) the hull and the operator are invariant under the full
rotation group $SO(3,\mathbb Z)$ of the cube, which acts irreducibly on $\mathbb R^3$; an invariant symmetric 2-tensor is
scalar (Schur). $\square$ So "the effective-mass tensor" of H5, if it exists, is a single number; anisotropy can only
enter through the (Kramers-degenerate) spinor structure, i.e. as a $2\times2$ matrix-valued but rotation-invariant
symbol, which Prop. 2.3(b) (no spin rotation needed) forces to be scalar as well.

### 5.4 Effective mass (H5) [open]

Conjectural only. The IDS exponent at the edge ($N(E)-N(E_{\rm bulk})\sim(E-E_{\rm bulk})^{3/2}$ for an isotropic
effective mass) was tested at level 4 with local exponents $1.03$–$1.22$ (Phase 5, [N]), inconclusive. **Obligation
H5:** (a) establish H3 (extended edge states); (b) compute $N_m(E)$ near the edge at levels 5–6 with the rank
inequality error bar $72\cdot2^{-m}$ of Theorem 4.3 (which at level 6 is $1.1$, far too large: the edge region
$N\lesssim10^{-3}$ is **not** resolved by any rigorous finite-volume IDS statement available; only the much smaller
measured interface counts make the level-6 IDS informative, and that is [N]); (c) the periodic-approximant program of
§5.3.

### 5.5 Summary table for the deliverable

| Target | Outcome in this task |
|---|---|
| H1 operator and hull | **proved theorems** (§1–2): hull, FLC, primitivity, recognizability, aperiodicity, minimality; operator bounded self-adjoint, $0\le H\le48$, covariances, Kramers; spectrum constant on $\Omega$ |
| H2 band edge | **proved**: compression theorem, two-sided certified bracket $1.5687\le E_{\rm bulk}\le8.7971$, IEEE $8.77013$; **conjecture** (computationally supported): $E_{\rm bulk}\approx8.76$ |
| H3 edge states | **unresolved**; the existing IPR numbers do not support "extended" (§5.2) |
| H4 homogenization | **obstructed/unresolved**; precise obligations §5.3 |
| H5 effective mass | **conjectural**; isotropy is forced if it exists (Prop. 5.1) |
| H6 clean-spectrum criterion | not part of Task B3 |

---

## 6. Literature assessment and novelty claim

Network status: web search was available; no full text (arXiv, publisher, ar5iv) could be fetched (proxy 403 /
DNS failures). Hence **every citation below is an "unverified citation"**; where a search snippet confirmed title,
venue and abstract this is noted as *(metadata confirmed)*.

**(i) Spectra on substitution / limit-periodic structures.** Bellissard, *Gap labelling theorems for Schrödinger
operators*, in *From Number Theory to Physics* (Springer 1992) 538–630 — gap labelling conjecture, hull/C*-algebra
framework *(metadata confirmed)*. Bellissard–Benedetti–Gambaudo, CMP 261 (2006) 1–41 — gap labelling for FLC tilings
via telescopic approximations *(metadata confirmed)*; Kaminker–Putnam, Michigan Math. J. 51 (2003) 537–546 and
Benameur–Oyono-Oyono (2003) — gap labelling for $\mathbb Z^d$ Cantor actions *(metadata confirmed)*. Lenz–Stollmann
2003/2005 and Lenz–Veselić 2009 — constancy of spectrum, uniform IDS *(metadata confirmed)*. Solomyak 1997 — unique
ergodicity, spectral theory of self-similar tilings *(metadata confirmed)*; Solomyak 1998, DCG 20, 265–279 —
nonperiodicity $\Rightarrow$ unique composition *(metadata confirmed)*; our §1.6 proves the converse direction for
FR30 directly. Anderson–Putnam, ETDS 18 (1998) 509–537 — collared tiles, inverse limits *(metadata confirmed)*; our
Lemma 3.5 is an instance of their collared-substitution primitivity. Mozes 1989 — multidimensional substitution
subshifts *(metadata confirmed)*. Limit-periodic Schrödinger operators in 1D: Avila, CMP 288 (2009), arXiv 0807.4339
(zero-measure spectrum, positive Lyapunov exponent for a dense set) and Damanik–Fillman–Lukic, J. Spectral Theory 7
(2017) 1101–1118 (generic zero-measure Cantor spectrum, continuum case) *(metadata confirmed)*; Damanik–Gorodetski's
work I recall is on Fibonacci/quasiperiodic rather than limit-periodic operators and was not confirmed by search.
These 1D results say that limit-periodic operators can have Cantor spectrum; nothing analogous is known to me in
$d=3$, and the FR30 numerics show no persistent gaps — consistent with the expectation that in $d\ge2$ gaps are rare,
but no theorem either way. Baake–Grimm, *Aperiodic Order* I (2013) — chair tiling as a limit-periodic model set
*(not found by search; recollection)*.

**(ii) Discrete gauge/flux models on aperiodic graphs.** Hofstadter-type models on quasicrystals use Peierls phases
from a uniform external field: Fuchs–Vidal, PRB 94 (2016) (Rauzy tiling butterfly, gaps labelled by four integers);
Tran–Duong–Pham–Nguyen-Ngoc–Hong–Vidal *Landau levels in quasicrystals* (2018); Ghadimi–Sugimoto–Tohyama, PRB 106
(2022) L201113 (Penrose, Bott index, staggered local flux) *(metadata confirmed by search)*. Spin–orbit ($SU(2)$)
hopping on quasicrystals: Huang–Liu, PRL 121 (2018) 126401, spin Bott index on a Penrose lattice *(metadata
confirmed)*. I found no prior work in which an $SU(2)$- or $Q_8$-valued connection is *generated by the substitution
rule itself* through tile frames (an intrinsic, exactly renormalizable flux background in $d=3$), nor a positive
lower bound on a frustrated hopping spectrum certified through collared-tile closure.

**(iii) Critical states and IPR scaling.** Macé–Jagannathan–Kalugin–Mosseri–Piéchon, PRB 96 (2017) 045138 (exact
critical eigenstates on Penrose, Ammann–Beenker, Fibonacci; multifractal spectra); Rieth–Grimm–Schreiber,
cond-mat/9809117 (participation numbers and multifractality on Penrose and the 3D Ammann–Kramer–Neri tiling: power-law
localization on Penrose, not observed in 3D); Olenev–Vekilov, JETP Lett. (1996) (critical wavefunctions in icosahedral
tight-binding) *(metadata confirmed)*. The $\mathrm{IPR}\cdot n$ doubling observed in §5.2 would, in this language,
be $D_2\approx2$; the standard diagnostics (full $D_q$, box counting) are the H3 obligation.

**(iv) Homogenization and effective mass.** Kozlov 1978 (almost-periodic coefficients, rate $O(\varepsilon)$ under a
non-resonance condition) *(metadata confirmed)*; Jikov–Kozlov–Oleinik 1994 *(existence confirmed; the almost-periodic
chapter from recollection)*; Birman–Suslina 2004 (homogenization as a threshold effect at the bottom of a periodic
spectrum, operator error estimates) *(metadata confirmed)*; Kuchment 2016 survey *(metadata confirmed)*;
Allaire–Piatnitski 2005 (effective mass theorems for periodic Schrödinger at internal band edges) *(from recollection)*.
All of these are periodic or almost-periodic *continuum* theories at an edge with a Bloch structure; the FR30 case is
discrete, aperiodic without Bloch waves, with an internal-type edge $E_{\rm bulk}>0$ and Kramers degeneracy — precisely
the configuration none of them covers (§5.3).

**Novelty claim (as far as I can tell).** New in this document: (1) a self-contained proof of recognizability and
aperiodicity of the *decorated* 3D chair hull through the notch rule (Theorems 1.7–1.8, Cor. 1.9); (2) a direct proof
of spectral constancy and the compression theorem for the FR30 Clifford operator, making the repo's pinned sequence a
rigorous upper-bound sequence; (3) exact-arithmetic certification of the upper bounds and, above all, a certified
**positive lower bound $E_{\rm bulk}\ge1.5687$** obtained by combining the plaquette decomposition with the
collared-substitution closure (72 legal vertex-star types) — the first two-sided rigorous bracket of the bulk gap;
(4) the conditional isotropy of any effective-mass tensor (Prop. 5.1); (5) the observation that the existing IPR data
scale as $n^{-2/3}$, contradicting the "extended" label used in Phase 5. The *techniques* (Weyl sequences on minimal
hulls, min-max compression, rank inequalities, collared tiles, local positive decompositions) are all classical.

---

## 7. Reproducibility

```
python3 -u -I audit/phase5a_frame_substitution.py        # ~20 s; frames, F, primitivity, nesting, rotation covariance,
                                                          #        b_m, notch rule, fixed-point seed
OPENBLAS_NUM_THREADS=1 python3 -u -I audit/phase5a_certified_upper_bound.py 2,3,4 1e-6   # 14 s; exact rational Rayleigh quotients
OPENBLAS_NUM_THREADS=1 python3 -u -I audit/phase5a_certified_upper_bound.py 5 1e-4       # level 5; results appended per level
                                                          # (on the shared 4-core machine, multithreaded BLAS made the same runs 30-100x slower)
python3 -u -I audit/phase5a_star_closure_lower_bound.py   # ~45 s; 72 vertex-star types, 207 plaquette signatures,
                                                          #        exact LDL* certification, E_bulk >= 1.5687255
```
Outputs: `audit/results/phase5a_frame_substitution.txt`, `audit/results/phase5a_frame_matrix.txt`,
`audit/results/phase5a_certified_upper_bound.txt`, `audit/results/phase5a_star_closure_lower_bound.txt`.
All runs used $<1$ GB RAM; Python 3.13, NumPy 2.5.3, SciPy 1.18.1.
