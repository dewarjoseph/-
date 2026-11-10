# Single source of truth for every labelled claim in the preprint skeleton.
# Fields: id, label (exactly as in the source), count_as (label used for counting;
# combined labels -> weakest component, ledger.json rule), section key,
# tex (LaTeX statement), short (plain text for claims.csv), evidence (plain text pointer),
# unverified (hand proof, not machine-checked / not peer-reviewed), note (flag).
T = "TOE_ATTEMPT.md"
C_ = "CORE.md"
PR = "PROOF.md"
L = "ledger.json"

CLAIMS = []
def c(id, label, sec, tex, short, ev, count_as=None, unverified=False, note=""):
    CLAIMS.append(dict(id=id, label=label, count_as=count_as or label, sec=sec, tex=tex,
                       short=short, evidence=ev, unverified=unverified, note=note))

# ---------- Section 1: sources (audit facts that carry a label) ----------
c("S1-QIS-PNP","F","s1",
  r"The QIS headline claim of an ``unconditional proof that P $\neq$ NP'' does not survive that repository's own held-out audit.",
  "QIS 'unconditional P != NP' claim is refuted by the repo's own audit",
  f"{T} §8 l.401; {C_} §5 l.84; {L} QIS-322 [F, excluded as falsified]")
c("S1-QIS-PLANNER","F","s1",
  r"The QIS ``64--0 planner'' record does not survive that repository's own audit.",
  "QIS '64-0 planner' record is refuted by the repo's own audit",
  f"{T} §8 l.401; {C_} §5 l.84; {L} QIS-182 [F, excluded as falsified]")

# ---------- Section 2: the core, K1-K15 (CORE.md §2) ----------
K = [
 ("K1","P",r"On a connected finite graph with $SU(2)$ links: flat $\Leftrightarrow$ gauge-trivial $\Leftrightarrow$ $\lambda_{\min}(H_U)=0$.","flat <=> gauge-trivial <=> lambda_min(H_U)=0 on finite connected graphs","Chair44 X1",38),
 ("K2","P",r"$E_* = \inf$ over finite legal patches of $\lambda^D = \lim D_R$; it depends only on the set of legal environments, is order-reversing in it, and does not depend on frequencies.","E_* = inf over legal patches of Dirichlet floor; depends only on legal environments","XII.A",39),
 ("K3","P",r"Exact IMS localisation identity; $\Lambda(\chi)\le E_*\le D_R$ with $D_R-\Lambda\le\varepsilon(\chi)$; rate $R^{-2}$ on doubling or Euclidean graphs, and $R^{-2}$ is optimal; property A alone gives no power law (lamplighter).","two-sided IMS localisation with optimal R^-2 rate","XII.B, XII.C",40),
 ("K4","P",r"Every geometry-compatible frame field has $\ge 12$ of the 21 centre-octant two-cycles non-trivial in every level-1 supertile, so the connection is never pure gauge. Lean kernel-checks only encoded finite predicates; this geometric statement is not itself a kernel-checked Lean theorem.","forced curvature: >=12 of 21 centre-octant two-cycles non-trivial (Lean checks encoded finite predicates only; geometric statement not kernel-checked)","Phase VII-B P1",41),
 ("K5","C",r"$E_*>0$ $\Leftrightarrow$ some $T_k$ is not flat. All 1098 gauge classes of the 6561 proper rules have $E_*\ge 3.788$.","all 1098 gauge classes of the 6561 proper rules have E_* >= 3.788","X3",42),
 ("K6","P/C",r"No lower bound on $E_*$ follows from plaquette-class frequencies: there are two $\mathbb{Z}^3$ connections with the same $Q_8$ class on every plaquette and floors separated by $\ge 0.18$.","plaquette-class frequencies give no lower bound on E_*","X4, X5, XII.P63",43),
 ("K7","P",r"The non-spinor floors are functions of the plaquette class field; the X.5 separation lives in the spinor component.","non-spinor floors are functions of the plaquette class field","XI.H3",44),
 ("K8","P",r"Orbit Lemma: $\sigma_{dQ}=\rho_Q\circ\sigma_d$, $\rho_Q$ is a global gauge transformation, $T_1(dQ)\cong T_1(d)$, and $E_*(dQ)=E_*(d)$ on the conjugation stabiliser; outside it the equivalence can fail from level 2.","Orbit Lemma","XII.OL",45),
 ("K9","C",r"$E_*(1387)\in[9.1104981,\,9.3616608]$; $E_*(539311)\in[9.2083494,\,9.3817818]$; the maximiser over all $6^8$ rules is one of 1387, 539311, 539291.","certified E_* enclosures for 1387 and 539311; maximiser among three rules","XII.R20, XII.r24, XII.F4",46),
 ("K10","P+C",r"No function of level-one data determines $E_*$ (1387 against 539288).","no function of level-one data determines E_*","XII.T31",47),
 ("K11","P",r"For every $Q_8$ gauge section $s$ of a patch $K$: $\lambda_{\min}(P_KHP_K)\le B(s)=[\sum_e(2-2\,\mathrm{Re}\,d_e)+b(K)]/|K|$; the floor is bounded by the unique-games frustration energy of any section.","floor bounded by unique-games frustration energy of any gauge section","XII.ug.P151",48),
 ("K12","P",r"The Clifford transports lie in $Q_8$; on vectors (the adjoint) the link group is the Klein group $V_4$; in two dimensions the Pauli-frame connections are $\mathbb{Z}_4$-valued (Abelian).","Clifford transports lie in Q8; adjoint image V4; Z4-valued in 2D","CLIFFORD_Q8_PHASE2 Thms 2.2-2.3; X6",49),
 ("K13","P",r"No chirality: Wilson traces and plaquette classes are identical for a tiling and its mirror.","Wilson traces and plaquette classes are mirror-invariant","CLIFFORD_Q8_PHASE2 Thm 2.4",50),
 ("K14","P",r"Diamagnetic bound: $\lambda_{\min}(H_U)\ge\lambda_{\min}(H_1)$ on every patch, for every unitary connection (Kato's inequality; standard).","diamagnetic bound (Kato's inequality)","standard; prereg/G1_volume_scaling.json T1",51),
 ("K15","P",r"In infinite volume, independent ($\beta=0$) links, and every finite-$\beta$ Gibbs measure of a finite-group Wilson action, give floor 0 almost surely (finite energy plus Borel--Cantelli).","infinite-volume floor 0 a.s. for beta=0 and finite-beta finite-group Gibbs measures","Phase VII §8; prereg/G1_volume_scaling.json T3",52),
]
for kid,lab,tex,short,src,line in K:
    ca = {"P/C":"C","P+C":"C"}.get(lab,lab)
    c(kid,lab,"s2core",tex,short,f"{C_} §2 l.{line} (source: {src})",count_as=ca,
      unverified=(lab in ("P","P/C","P+C") and kid!="K4"),
      note=("combined label shown as written; counted as weakest component C" if ca!=lab else ""))

# ---------- Section 2: how the repositories fit (CORE.md §3) ----------
c("I-TSEITIN","P","s2fit",
  r"Tseitin parity formulas are unsatisfiable iff the total charge is odd ($\mathbf{1}_V\in\ker$ of the incidence over $\mathbb{F}_2$); this is the $\mathbb{Z}_2$ coboundary side of the core, in transposed form.",
  "Tseitin formulas unsat iff total charge odd; Z2 coboundary side of the core",
  f"{T} §2 l.63; {C_} §3 l.61", unverified=True)
c("I-ENERGY","P","s2fit",
  r"The continuous multilinear energy of a Tseitin instance has floor $E_{\min}\ge 1$.",
  "multilinear energy of a Tseitin instance has floor >= 1",
  f"{C_} §3 l.62", unverified=True)
c("I-ENERGY-INST","A","s2fit",
  r"Read as an instance of the core, that floor is an analogy only: it is the floor of a relaxation energy, not of a covariant Laplacian.",
  "Tseitin energy floor as an instance of the core is analogy only",
  f"{C_} §3 l.62")
c("I-XIII-SCOPE","P","s2fit",
  r"Scope statement: unique-games instances with $G=Q_8$ are the combinatorial side of the core; the external Unique Games Theorem is worst-case on finite instances and bounds no floor. (The external theorem itself is not checked here.)",
  "scope: external UG theorem is worst-case on finite instances and bounds no floor",
  f"{T} §2 l.64; {C_} §3 l.60", unverified=True)
c("I-UG-EXT","X","s2fit",
  r"Third-party claims (Unique Games Theorem / Min-UnCut hardness; ``Family 378: ETH is false'') are recorded as external and unchecked.",
  "external UG / 'ETH is false' claims recorded as external, unchecked",
  f"{C_} §3 l.69")
c("I-QIS320","E","s2fit",
  r"The Laplacian $\lambda_2$ of SAT clause graphs plateaus near $1.01$ as $N$ grows.",
  "lambda_2 of SAT clause graphs plateaus near 1.01",
  f"{C_} §3 l.64; {L} QIS-320", note="ledger QIS-320 label E; source_label 'certified' (ledger did not upgrade)")
c("I-QIS320-INST","A","s2fit",
  r"As an instance of the core this is an analogy only: a scalar (trivial-representation) graph Laplacian with no connection.",
  "QIS lambda_2 as an instance of the core is analogy only",
  f"{C_} §3 l.64; §5 l.87")
c("I-QIS299","F","s2fit",
  r"``Residual frustrated clauses carry a non-trivial 1-cycle'' (a would-be holonomy statement for a $\mathbb{Z}_2/\mathbb{R}$ cochain) is falsified.",
  "QIS-299 'frustrated clauses carry a non-trivial 1-cycle' is falsified",
  f"{C_} §3 l.65; {L} QIS-299")
c("I-GU-C4","C","s2fit",
  r"The 4D chair $C_4$ has face counts $(80,212,210,92,15)$, $\chi=1$; its boundary has $(80,208,192,64)$, $\chi=0$ (geometry only; no connection).",
  "4D chair C4 face counts, chi=1; boundary chi=0",
  f"{C_} §3 l.67; {L} GU-001")
c("I-GU-A","A","s2fit",
  r"Geometric Unity: the fibre of $\mathrm{Met}(X)$ as an internal space is a structural analogy only (no shared object).",
  "Geometric Unity: structural analogy only",
  f"{C_} §3 l.68")
c("I-WOLFRAM","A","s2fit",
  r"Hypergraph rewriting (Wolfram Physics Project) is substitution-like rewriting of graphs with no group-valued connection on a fixed substitution hull: analogy only.",
  "Wolfram hypergraph rewriting: analogy only",
  f"{C_} §3 l.70")
c("I-XIV-H1","F","s2fit",
  r"Phase XIV (dynamical $Q_8$ Wilson ensemble) prediction H1: the hot-series $\langle\lambda_{\min}\rangle(\beta)$ is non-increasing within 3\,SE --- falsified.",
  "Phase XIV H1 (hot-series floor non-increasing) falsified",
  f"{C_} §3 l.59; {T} §4 row 8 l.319; {L} CH14-XIV.H1")
c("I-XIV-H2","F","s2fit",
  r"Phase XIV prediction H2: $Y_3(1387)$ exceeds every sampled $\lambda_{\min}$ at every $\beta$ --- falsified.",
  "Phase XIV H2 falsified",
  f"{C_} §3 l.59; {T} §4 row 8 l.319; {L} CH14-XIV.H2")
c("I-XIV-H3","E","s2fit",
  r"Phase XIV H3 holds: the floor falls fastest where the inter-tile plaquette rises fastest (within one grid step).",
  "Phase XIV H3 holds",
  f"{C_} §3 l.59; {L} CH14-XIV.H3")
c("I-VI-017","F","s2fit",
  r"The earlier (Phase VI) claim that random i.i.d.\ $Q_8$ links are gapped (floor $\approx 14.4$) is withdrawn/falsified; G1 explains it as a pre-asymptotic plateau.",
  "Phase VI 'random Q8 links are gapped (14.4)' withdrawn/falsified",
  f"{T} §3.1 l.115; {L} CH-VI-017")

# ---------- 3.1 G1 ----------
c("G1-T1","P","g1",r"T1: the diamagnetic bound and compression give $\lambda_1(T_L)\le\lambda(T_L)\le\min$ over the eight child supertiles.",
  "T1: lambda_1(T_L) <= lambda(T_L) <= min over 8 children", f"{T} §3.1 l.90", unverified=True)
c("G1-T2","P","g1",r"T2: the children are i.i.d.\ copies of $T_{L-1}$, so $P(\lambda(T_L)>x)\le P(\lambda(T_{L-1})>x)^8$.",
  "T2: P(lambda(T_L)>x) <= P(lambda(T_{L-1})>x)^8", f"{T} §3.1 l.91", unverified=True)
c("G1-T3","P","g1",r"T3: for every $\beta\in[0,\infty)$ and every infinite-volume Gibbs measure of a finite-group Wilson action on the hull, $\inf\sigma(H_U)=0$ almost surely (standard argument; not claimed new).",
  "T3: inf spec H_U = 0 a.s. at every beta (finite groups)", f"{T} §3.1 l.92-94; {L} TOE-G1-T3", unverified=True,
  note="ledger evidence cites stale 'TOE_ATTEMPT.md s4.1' (now §3.1)")
c("G1-RARE","P-level estimate","g1",r"Rare-region scale: a trivial 1-star has probability $8^{-24}\approx 2\cdot10^{-22}$ at $\beta=0$, so the regions that drive the floor to 0 first appear at about $10^{22}$ tiles, far beyond $T_5$.",
  "rare regions first appear at ~1e22 tiles", f"{T} §3.1 l.95", count_as="non-standard",
  note="source label '[P-level estimate]' is not one of the six labels; kept verbatim, not counted as P; needs Joey's ruling")
c("G1-FLOORS","E","g1",r"$Q_8$ mean floors on $T_1\ldots T_5$ ($\beta=0$, 2780 samples): 18.511, 16.024, 15.036, 14.615, 14.367 ($\pm$0.027, 0.015, 0.009, 0.008, 0.014).",
  "Q8 mean floors T1..T5: 18.511 ... 14.367", f"{T} §3.1 l.98; results/g1_score.json")
c("G1-TRIVIAL","E","g1",r"The trivial-connection floor falls from 11.21 to 0.139 over $T_1\ldots T_5$.",
  "trivial floor 11.21 -> 0.139", f"{T} §3.1 l.99")
c("TOE-G1-T1","E","g1",r"Every $\beta=0$ sample obeys T1 (0 violations).",
  "every beta=0 sample obeys T1", f"{T} §3.1 l.100; {L} TOE-G1-T1 [C]",
  note="LABEL MISMATCH: TOE_ATTEMPT lists this under 'Results [E, simulated]', ledger says [C]; weaker [E] used (no upgrade); needs ledger reconciliation")
c("TOE-G1-T2","E","g1",r"T2 holds at every level: mean $\beta=0$ floor of $T_L\le E[\min$ of 8 i.i.d.\ level-$(L-1)$ floors$]+3$\,SE, $L=2..5$.",
  "T2 holds at every level (data check)", f"{T} §3.1 l.100; {L} TOE-G1-T2")
c("TOE-G1-H1","F","g1",r"H1 (preregistered): the ground state sits (weight $\ge\frac12$) on the weakest child in $\ge 2/3$ of samples. Outcome: fractions 0.345, 0.450, 0.650 ($L=3,4,5$).",
  "H1 weakest-child localisation", f"{T} §3.1 l.106; {L} TOE-G1-H1")
c("TOE-G1-H2","F","g1",r"H2 (preregistered): min-stable median law $\hat m$ = 0.0830-quantile of level $L-1$. Outcome: medians below the band at $L=3,4$, inside at $L=5$.",
  "H2 min-stable median law", f"{T} §3.1 l.107; {L} TOE-G1-H2")
c("TOE-G1-H3a","E","g1",r"H3a holds: $2I$ and $SU(2)$ floors agree within $3\sigma$ ($\Delta=+0.016,-0.006,+0.024$).",
  "H3a 2I and SU(2) agree", f"{T} §3.1 l.108; {L} TOE-G1-H3a")
c("TOE-G1-H3b","F","g1",r"H3b (preregistered): $Q_8$ significantly below $SU(2)$. Outcome: right sign ($-0.021,-0.014,-0.017$) but never beyond $3\sigma$.",
  "H3b Q8 significantly below SU(2)", f"{T} §3.1 l.109; {L} TOE-G1-H3b")
c("TOE-G1-H4","E","g1",r"H4 holds (weak test, recorded as such): medians (18.53 \ldots 14.39) lie above the certified $E_*(1387)\ge 9.1104981$.",
  "H4 medians above certified E_*(1387) (weak test)", f"{T} §3.1 l.110; {L} TOE-G1-H4")
c("SC-8","P","g1",r"Scorecard row 8 (programme-internal), settled negatively: in infinite volume the matter floor is 0 at every $\beta$ for finite groups (G1 T3), so it is not an infinite-volume order parameter of any finite-group Wilson ensemble.",
  "row 8: floor is not an infinite-volume order parameter ([P] negative)", f"{T} §3.1 l.116; §4 row 8 l.319", unverified=True,
  note="README.md says 'One scorecard row is [P]' but row 8 is '[P] negative' (discrepancies.md §2.7)")

# ---------- 3.2 G2 Part B ----------
c("G2B-DERIV","P-level","g2b",r"Derivation: $\lambda(T_L,\theta)=\lambda_1(T_L)+c_L\theta^2+O(\theta^3)$, with $c_L$ = dia $-$ para given exactly by second-order perturbation theory about the Dirichlet ground state.",
  "second-order expansion of lambda(T_L,theta)", f"{T} §3.2 l.129", count_as="non-standard",
  note="source label '[P-level]' kept verbatim; later proved as PROOF-A [P]")
c("G2B-CL","E","g2b",r"Floating-point $c_L$: FR30 $8.704, 11.324, 12.674, 13.046, 13.243, 13.318$ ($c_\infty\approx 13.364$); 1387 $9.850, 12.458, 13.685, 14.039, 14.196, 14.253$ ($c_\infty\approx 14.285$); $G_6/(\pi^2c_6)=0.9992$ for both.",
  "c_L table and geometric c_inf (FR30 13.364, 1387 14.285)", f"{T} §3.2 l.124,132-135; results/g2_partB.json")
c("TOE-G2-B0","C","g2b",r"B0 holds: Taylor check, finite-$\theta$ ratios 0.998--0.999; an independent finite-difference test agrees to $10^{-3}$.",
  "B0 Taylor check", f"{T} §3.2 l.124,139; {L} TOE-G2-B0")
c("TOE-G2-B1","E","g2b",r"B1 holds: geometric convergence, difference ratios FR30 0.528, 0.380; 1387 0.444, 0.359 ($\le 0.75$).",
  "B1 geometric convergence", f"{T} §3.2 l.140; {L} TOE-G2-B1")
c("TOE-G2-B2","E","g2b",r"B2 holds: $c_6>0$ and $c_\infty>0$ (13.36, 14.28).",
  "B2 c_6>0 and c_inf>0", f"{T} §3.2 l.141; {L} TOE-G2-B2")
c("TOE-G2-B3","E","g2b",r"B3 holds: $G_6/(\pi^2c_6)$ within 10\,\% of 1 (0.9992, 0.9992; from 0.17 at $L=1$ through 0.94, 0.987, 0.997). Uniformity of the $\theta^3$ remainder is not proved, so B3 remains [E].",
  "B3 scaling trajectory (remains [E])", f"{T} §3.2 l.142,153; {PR} §0 not-proved item 1; {L} TOE-G2-B3")
c("TOE-G2-B4","F","g2b",r"B4 (preregistered): the 20 lowest levels shift uniformly ($\pm20\,\%$ of $c_5$) at $L=5$. Outcome: entries 18 and 20 are 0.925 and 0.559 (FR30), 0.929 and 0.590 (1387).",
  "B4 uniform shift of 20 levels", f"{T} §3.2 l.143; {L} TOE-G2-B4")
c("G2B-LIMIT","E","g2b",r"Along $\theta=\kappa a$ the frame connection has a continuum limit.",
  "continuum limit along theta = kappa a", f"{T} §3.2 l.146; §7 l.371")
c("G2B-MASS","E","g2b",r"In that limit the frustration survives as a finite mass term, $\Lambda_{\rm phys}$ = (Dirichlet Laplacian of the chair region) $+\kappa^2c_\infty$, with $c_\infty\approx13.36$ (FR30), $14.28$ (1387) derived from the substitution, not fitted.",
  "frustration survives as mass term kappa^2 c_inf", f"{T} §3.2 l.147; §4 row 7 l.318; §7 l.372")
c("G2B-POSTHOC","E, post hoc","g2b",r"Post-hoc B4 diagnostic (not preregistered; does not change the frozen [F]): rerun with $k=28$ puts all 20 index-wise shifts in $[0.985,0.997]c_5$ (FR30), $[0.984,0.997]c_5$ (1387); the uniform-mass-shift prediction is plausible but not established.",
  "post-hoc B4 diagnostic: eigensolver artifact plausible, not established", f"{T} §3.2 l.159-164; src/posthoc_b4.py", count_as="E")

# ---------- PROOF.md ----------
c("TOE-PROOF-A","P","proof",r"Theorem A: $\lambda(T_L,\theta)=\lambda_1(T_L)+c_L\theta^2+O(\theta^3)$, with $c_L=\min_G\sum_e\varphi_L(a)\varphi_L(b)\,|w_e+G_b-G_a|^2$.",
  "Theorem A: second-order expansion and variational formula for c_L", f"{PR} §0 l.10, §2; {L} TOE-PROOF-A", unverified=True)
c("TOE-PROOF-B","P","proof",r"Theorem B: the twisted free densities $\mu_\ell$ increase; the corrected Dirichlet densities $\tilde\nu_\ell=\nu^0_\ell+48\cdot2^{-\ell}$ decrease; $\mu_\ell\le\nu^0_\ell$.",
  "Theorem B: monotone densities mu_l, nu~_l", f"{PR} §0 l.11, §3; {L} TOE-PROOF-B", unverified=True)
c("TOE-PROOF-C","P","proof",r"Theorem C: for every frame rule and every $\ell\le L$, with explicit $\varepsilon_{\ell,L}\to0$: $\mu_\ell(1-\varepsilon_{\ell,L})\le c_L\le\tilde\nu_\ell(1+\varepsilon_{\ell,L})$.",
  "Theorem C: two-sided bracket of c_L", f"{PR} §0 l.12, §4; {L} TOE-PROOF-C", unverified=True)
c("TOE-PROOF-D","P+C","proof",r"D: for every one of the $6^8=1\,679\,616$ frame rules, $\liminf_L c_L\ge\mu_1\ge 3527/1012>3.485$ (attained at rule 128462).",
  "D: liminf c_L >= 3527/1012 for all 6^8 rules", f"{PR} §0 l.13, §5; {L} TOE-PROOF-D [C]; results/proof_positivity.json", count_as="C", unverified=True,
  note="source label [P]+[C]; ledger records weakest component [C]; counted as C")
c("TOE-PROOF-E-FR30","C","proof",r"E (FR30): $13.232574\le\liminf c_L\le\limsup c_L\le 15.465590$ (level $\ell=6$).",
  "E FR30 bracket [13.232574, 15.465590]", f"{PR} §0 l.14, §5 l.184; {L} TOE-PROOF-E-FR30",
  note="ledger prints upper end 15.465589, PROOF.md prints 15.465590 (discrepancies.md §4); PROOF.md value kept")
c("TOE-PROOF-E-1387","C","proof",r"E (1387): $14.161980\le\liminf c_L\le\limsup c_L\le 16.390966$ (level $\ell=6$).",
  "E 1387 bracket [14.161980, 16.390966]", f"{PR} §0 l.14, §5 l.185; {L} TOE-PROOF-E-1387")
c("PROOF-E-TABLE","C","proof",r"Certified level densities $\mu_\ell\ge$, $\nu^0_\ell\le$ for FR30 and 1387, $\ell=1..6$ (Table~\ref{tab:munu}), as printed.",
  "certified mu_l / nu0_l table l=1..6 (10 cells flagged)", f"{PR} §5 l.173-182; results/proof_bounds.json",
  note="10 cells rounded to nearest, not outward (discrepancies.md §1); printed values kept and footnote-flagged")
c("TOE-PROOF-prim","C","proof",r"The frame substitution is primitive for 1\,666\,486 of the $6^8$ rules (FR30, 1387: $k=2$, $|H|=24$); it fails for 13\,130 rules, among them x539311 and x539291 ($|H|=48$, period-2 walk).",
  "primitivity holds for 1666486 rules, fails for 13130", f"{PR} §6 l.194-195; {L} TOE-PROOF-prim; src/proof_primitivity.py")
c("TOE-PROOF-F","P","proof",r"Theorem F: for every rule whose frame substitution is primitive, $c_L$ converges and $\lim c_L=\rho(d):=7\min$ over stationary closed tile-compatible fields $\xi$ of $E_\mu[\sum_k|w_k+\xi_k|^2]$ (using three cited standard theorems \cite{solomyak1997dynamics,wiener1939ergodic,hancheolsen2010kolmogorov}).",
  "Theorem F: c_L -> rho(d) corrector formula for primitive rules", f"{PR} §0 l.15, §6; {L} TOE-PROOF-F", unverified=True)
c("PROOF-L7","P","proof",r"Lemma 7 (sublinearity): for $\zeta\in\mathcal{C}_0$, $F_R(Y):=R^{-5}\sum_{q\in Q_R}|G_Y(q)-\langle G_Y\rangle_{Q_R}|^2\to0$, $\mu$-a.s.\ and in $L^1(\mu)$, where $Q_R=\{0,\ldots,R-1\}^3$ or any translate of it by $O(R)$.",
  "Lemma 7 (sublinearity of the integrated corrector)", f"{PR} §6 l.221-225", unverified=True)

# ---------- 3.2 G2 Part A ----------
c("TOE-G2-D1","P","g2a",r"D1 (weak coupling): $\beta\langle\lambda-\lambda_1\rangle\to C_{\rm pert}=3[\sum_eK^+_{ee}\varphi_0(a)\varphi_0(b)-\mathrm{tr}(K^+J)]$, by second-order perturbation theory with the Gaussian Wilson measure; $C_{\rm pert}=11.4856$ ($T_2$), $13.6306$ ($T_3$). The derivation is at the level of formal perturbation theory.",
  "D1: weak-coupling limit C_pert (formal perturbation theory)", f"{T} §3.2 l.175-177,203; {L} TOE-G2-D1; src/pert.py", unverified=True,
  note="ledger [P]; TOE text says derivation is 'at the level of formal perturbation theory' -- referee may want [X]/[P, unverified]")
c("TOE-G2-W1","E","g2a",r"W1 holds: $R_{SU2}(64)\in[0.85,1.15]$, $R_{SU2}(32)\in[0.75,1.25]$ (1.002/1.025 on $T_2$; 1.010/1.017 on $T_3$).",
  "W1 SU(2) approaches C_pert/beta", f"{T} §3.2 l.195; {L} TOE-G2-W1")
c("TOE-G2-W2","E","g2a",r"W2 holds: $|R_{SU2}-1|$ non-increasing over $\beta=8\ldots64$.",
  "W2 monotone approach", f"{T} §3.2 l.196; {L} TOE-G2-W2")
c("TOE-G2-W3a","E","g2a",r"W3a holds: $2I=SU(2)$ at $\beta\le4$.",
  "W3a 2I tracks SU(2) at beta<=4", f"{T} §3.2 l.197; {L} TOE-G2-W3a")
c("TOE-G2-W3b","E","g2a",r"W3b holds: $2I$ frozen ($R_{2I}<R_{SU2}/2$) at $\beta=32,64$.",
  "W3b 2I frozen at beta=32,64", f"{T} §3.2 l.198; {L} TOE-G2-W3b")
c("TOE-G2-W3c","F","g2a",r"W3c (preregistered): $Q_8=SU(2)$ at $\beta\le1$ and frozen at $\beta\ge4$. Outcome: frozen from $\beta=4$ as predicted, but already different at $\beta=0.5,1$ ($T_3$: 13.862 vs 13.950; 12.267 vs 12.666).",
  "W3c Q8 tracks SU(2) at beta<=1", f"{T} §3.2 l.199; {L} TOE-G2-W3c")
c("TOE-G2-W4","E","g2a",r"W4 holds: $2I$ within 25\,\% of $SU(2)$ at $\beta=8$ (ratios 0.85, 0.81).",
  "W4 2I within 25% of SU(2) at beta=8", f"{T} §3.2 l.200; {L} TOE-G2-W4")
c("G2A-SELFENERGY","E","g2a",r"In the dynamical $SU(2)$ theory the gauge-induced floor shift approaches $C_{\rm pert}/\beta$ monotonically and agrees with it to 1\,\% at $\beta=64$ on both levels (the floor is a mass renormalisation).",
  "floor shift = perturbative self-energy to 1% at beta=64", f"{T} §3.2 l.203-205; §7 l.369")

# ---------- 3.3 G3 ----------
c("TOE-G3-R0","P","g3",r"R0: in temporal gauge the weight factorises as $M^{1/2}KM^{1/2}$ with positive-definite kernel $K(U,U')=\prod_ef(U_eU_e'^{-1})$, $f(g)=e^{\beta\,\mathrm{Re}\,g}$; the transfer matrix is self-adjoint and positive on any spatial 2-complex, so $H=-\ln T$ generates unitary $e^{-iHt}$ on the gauge-invariant space (L\"uscher 1977; Osterwalder--Seiler 1978; not chair-specific).",
  "R0 positive self-adjoint transfer matrix (standard)", f"{T} §3.3 l.217-220; {L} TOE-G3-R0", unverified=True)
c("TOE-G3-R1","E","g3",r"R1 holds: $C(\tau)\ge0$ and log-convex in every run, within $3\sigma$.",
  "R1 positive log-convex correlators", f"{T} §3.3 l.231; {L} TOE-G3-R1")
c("TOE-G3-R2","E","g3",r"R2 holds: $r(1)/u^2$ = 0.981, 1.011, 1.018 ($\beta=0.25$); 0.996, 1.073, 0.995 ($\beta=0.5$) for $2I$, $Q_8$, $SU(2)$.",
  "R2 r(1)/u^2 within band", f"{T} §3.3 l.232; {L} TOE-G3-R2")
c("TOE-G3-R3a","E","g3",r"R3a holds: $Q_8$ above $SU(2)$ at $\beta=1$ ($r(1)=0.1184\pm0.0008$ vs $0.0534\pm0.0002$).",
  "R3a Q8 above SU(2) at beta=1", f"{T} §3.3 l.233; {L} TOE-G3-R3a")
c("TOE-G3-R3b","E","g3",r"R3b holds: $2I=SU(2)$ within $3\sigma$ at every $\beta$.",
  "R3b 2I = SU(2)", f"{T} §3.3 l.234; {L} TOE-G3-R3b")
c("TOE-G3-R3c","E","g3",r"R3c holds: $m_{\rm eff}$ within $\times1.5$ of $-2\ln u$ at $\beta=1$ ($Q_8$ 2.13 vs 2.70; $2I$ 2.92 vs 2.85; $SU(2)$ 2.93 vs 2.85).",
  "R3c m_eff vs -2 ln u", f"{T} §3.3 l.235; {L} TOE-G3-R3c")
c("G3-SPECTRUM","E","g3",r"The strong-coupling spectrum is the one derived, including the chair-specific mass $-2\ln u_G$ from two-link plaquettes.",
  "strong-coupling spectrum matches derivation", f"{T} §3.3 l.238; §7 l.379")
c("SC-6","P","g3",r"Scorecard row 6: quantum mechanics with unitary time evolution holds at the lattice level only (standard construction).",
  "row 6: QM with unitary evolution at lattice level", f"{T} §4 row 6 l.317; §4 l.321", unverified=True)

# ---------- 3.4 G4 ----------
c("TOE-G4-O1","P","g4",r"The core has no chirality: $H_U$ is second order (no Dirac operator; mirror theorem); the hull is 3-dimensional (no $\gamma_5$ as Euclidean spacetime); on any finite patch a closed loop of $U(1)$ twists has zero net spectral flow (finite-volume content of Nielsen--Ninomiya); a domain wall or overlap would insert chirality, not derive it.",
  "G4 obstruction: no chirality in the core", f"{T} §3.4 l.245-255; {L} TOE-G4-O1", unverified=True,
  note="ledger evidence cites stale 'TOE_ATTEMPT.md s4.4' (now §3.4)")
c("TOE-G4-O2","P","g4",r"An $SU(2)$ theory with a single Weyl doublet is inconsistent (Witten 1982); any chiral version of the $SU(2)$ $\theta$-family needs an even number of doublets.",
  "Witten anomaly: even number of doublets needed", f"{T} §3.4 l.256; {L} TOE-G4-O2", unverified=True)
c("G4-INFVOL","X","g4",r"The infinite-volume statement for the hull (no single Weyl fermion) is not covered by the 1981 Nielsen--Ninomiya proofs, which assume translation invariance, and is not proved.",
  "infinite-volume Nielsen-Ninomiya for the hull: open", f"{T} §3.4 l.251,258")

# ---------- 3.5 G5 ----------
c("G5-S1","P","g5",r"S1: an exact axis symmetry of the rule, $\mathrm{conj}_Q(d)=d$, makes the shadow floors constant on the orbits of the symmetry group on the axes.",
  "S1 axis symmetry -> constant shadow floors on orbits", f"{T} §3.5 l.267", unverified=True)
c("TOE-G5-S3","P","g5",r"S3: the shadows are three different $Q_8$ characters; a symmetry permuting them acts as an outer automorphism of the gauge group, whereas generations carry identical gauge charges.",
  "S3 shadows are different Q8 characters", f"{T} §3.5 l.268; {L} TOE-G5-S3", unverified=True)
c("G5-S4","P","g5",r"S4: the only non-Abelian sector, the spinor, has multiplicity 2, and the Chair44 index is $2\chi=2$.",
  "S4 spinor multiplicity 2, index 2chi=2", f"{T} §3.5 l.269", unverified=True)
c("G5-COUNT","C","g5",r"Structural count among the 6561 proper rules: 6456 have no axis symmetry, 24 a symmetry group of order 2, 80 of order 3, and exactly one (rule 63) the full $S_3$.",
  "6456/24/80/1 symmetry count (rule 63 unique S3)", f"{T} §3.5 l.271-275; src/rule_symmetry.py")
c("TOE-G5.1","C","g5",r"G5.1 holds: rule 63 ($S_3$), $\lambda_1=\lambda_2=\lambda_3$ on $T_2\ldots T_5$ (7.868057, 5.345482, 4.678361, 4.280895).",
  "G5.1 rule 63 threefold degenerate", f"{T} §3.5 l.281; {L} TOE-G5.1")
c("TOE-G5.2","C","g5",r"G5.2 holds: rule 64 ($C_3$), the same (10.838889, 8.860622, 7.680477, 6.323312).",
  "G5.2 rule 64 threefold degenerate", f"{T} §3.5 l.282; {L} TOE-G5.2")
c("TOE-G5.3","C","g5",r"G5.3 holds: FR30 $\lambda_x=\lambda_z\ne\lambda_y$ (e.g.\ $T_5$: 7.700134, 5.386980, 7.700134).",
  "G5.3 FR30 lambda_x = lambda_z != lambda_y", f"{T} §3.5 l.283; {L} TOE-G5.3")
c("TOE-G5.4","C","g5",r"G5.4 holds: 1387, x539311, x539291 have three distinct floors (minimum pair gap 0.01486, 1387, $T_4$).",
  "G5.4 three distinct floors for frontier rules", f"{T} §3.5 l.284; {L} TOE-G5.4")
c("TOE-G5.5","C","g5",r"G5.5 holds: conjugation by $W_Q$ permutes $\chi_k\to\chi_{Q(k)}$ for all six $Q$.",
  "G5.5 conjugation permutes shadows", f"{T} §3.5 l.285; {L} TOE-G5.5")
c("TOE-G5-none","P","g5",r"No mechanism in the core produces three generations.",
  "no mechanism for three generations", f"{T} §3.5 l.288; {L} TOE-G5-none", unverified=True,
  note="ledger evidence cites stale 'TOE_ATTEMPT.md s4.5' (now §3.5)")
c("G5-R63","A","g5",r"The degenerate shadow triplet of rule 63 is related by an $S_3$ that permutes gauge charges; it is at most an analogue of a flavour or colour triplet, not three generations.",
  "rule-63 triplet is at most a flavour/colour analogue", f"{T} §3.5 l.289")

# ---------- 3.6 G6 ----------
c("TOE-G6-O1","P","g6",r"The substitution geometry is flat and rigid: every interior lattice edge lies in exactly four unit cubes, so every Regge deficit angle is $2\pi-4\cdot\frac{\pi}{2}=0$ and the Regge action vanishes at every level; the substitution is an exact similarity by a factor 2.",
  "chair complex is flat and rigid (Regge deficits 0)", f"{T} §3.6 l.297-300; {L} TOE-G6-O1", unverified=True,
  note="ledger evidence cites stale 'TOE_ATTEMPT.md s4.6' (now §3.6)")
c("TOE-G6-O2","P","g6",r"Making the geometry dynamical (Regge calculus with variable edge lengths, or causal dynamical triangulations) leaves the substitution class and destroys the legal-patch structure used by K2--K10.",
  "dynamical geometry leaves the substitution class", f"{T} §3.6 l.301; {L} TOE-G6-O2", unverified=True,
  note="TOE_ATTEMPT item 2 carries no explicit inline label; label [P] taken from ledger TOE-G6-O2 (section-level 'each statement' rule only in §3.4)")

# ---------- Figures ----------
c("FIG5-ESTAR","C","fig",r"$E_*(\mathrm{FR30})\in[7.954292,\,8.7642270381]$ as printed in the ledger (not in PROOF.md).",
  "E_*(FR30) enclosure [7.954292, 8.7642270381] (truncated upper end flagged)",
  f"{L} CH9-N3-enclosure (l.624), CH8-B1-upper-bound (l.474); figures/proof-brackets/README.md Fig.5",
  note="upper end truncated; outward value 8.7642270382 (discrepancies.md §1); printed value kept")

# =====================================================================
# v0.1 revisions (2026-11-01, Paper Writer), responding to
# referee-reports/toe-preprint-skeleton.md and novelty/theorem-F-novelty.md.
# The source label (field 'label') is NEVER changed: it is what the source says.
# 'paper' is the label printed in the paper. Rule: paper label may be weaker than
# the source label, never stronger. Every difference gets a row in Appendix C.
# =====================================================================
LABEL_CHANGES = {
 # id: (paper label, reason, pending-author-ruling marker text or "")
 "K6": ("C", "compound source label [P]/[C]; printed as its weakest component", ""),
 "K10": ("C", "compound source label [P]+[C]; weakest component; ledger CH12-XII.T31 is [C]", ""),
 "TOE-PROOF-D": ("C", "compound source label [P]+[C]; weakest component; ledger TOE-PROOF-D is [C]", ""),
 "G1-RARE": ("X", "non-standard source label 'P-level estimate'; a heuristic order-of-magnitude estimate with no run near 1e22 tiles, so no numerical evidence: [X]", "label pending author ruling on 'P-level estimate'"),
 "G2B-DERIV": ("E", "non-standard source label 'P-level'; formal second-order expansion whose only support at this point is the floating-point B0 check; the proved statement is TOE-PROOF-A", "label pending author ruling on 'P-level'"),
 "G2B-POSTHOC": ("E", "compound source label 'E, post hoc'; standard label [E], the qualifier 'post hoc, not preregistered' is kept in the statement", ""),
 "TOE-G2-B0": ("E", "floating-point Taylor/finite-difference check without error control (referee §4)", ""),
 "TOE-G5.1": ("E", "floating-point eigenvalues, equality to 1e-13 without a rigorous error bound (TOE_ATTEMPT l.277; referee §4)", ""),
 "TOE-G5.2": ("E", "floating-point eigenvalues, equality to 1e-13 without a rigorous error bound (TOE_ATTEMPT l.277; referee §4)", ""),
 "TOE-G5.3": ("E", "floating-point eigenvalues, equality to 1e-13 without a rigorous error bound (TOE_ATTEMPT l.277; referee §4)", ""),
 "TOE-G5.4": ("E", "floating-point eigenvalues; a minimum gap of 0.01486 without a rigorous error bound (TOE_ATTEMPT l.277; referee §4)", ""),
 "G2B-LIMIT": ("X", "existence of a continuum limit is not established by six levels; the frozen prereg itself labels the homogenisation step D3 '[X, derived]' (prereg/G2_scaling.json); uniformity of the theta^3 remainder is open (PROOF.md §0)", ""),
 "G2B-MASS": ("X", "identifying the limit operator as Dirichlet Laplacian + kappa^2 c_inf rests on D3 [X] and on an extrapolated c_inf; the computed c_L values stay [E] (G2B-CL)", ""),
 "TOE-G2-D1": ("E", "formal perturbation theory (TOE_ATTEMPT l.203); the asymptotic expansion is not proved; what supports the limit is the numerical agreement W1/W2 [E]", ""),
 "FIG5-ESTAR": ("E", "source category mapped to [C] under a Phase IX mapping the author has not ratified (discrepancies.md §2.2; ledger CH9-N3); printed [E] until that mapping is ratified. Interval printed outward", ""),
}
PENDING = {  # same label as source, but rendered with an explicit pending marker
}

# Ledger ids (toe/ledger.json). Identity maps K12..G5-R63 filled from the 2026-11-06 owner ledger sync (Cookies toe-unification 7e6a508); paper id = ledger id.
LEDGER_IDS = {"K1":"CH10-X1-flatness","K2":"CH12-XII.A","K3":"CH12-XII.B","K4":"CH7b-P1-forced-curvature",
 "K5":"CH10-X3-positivity","K6":"CH10-X4-no-go","K7":"CH11-XI.H3","K8":"CH12-XII.OL","K9":"CH12-XII.R20",
 "K10":"CH12-XII.T31","K11":"CH12-XII.ug.P151","S1-QIS-PNP":"QIS-322","S1-QIS-PLANNER":"QIS-182",
 "I-QIS320":"QIS-320","I-QIS299":"QIS-299","I-GU-C4":"GU-001","I-XIV-H1":"CH14-XIV.H1","I-XIV-H2":"CH14-XIV.H2",
 "I-XIV-H3":"CH14-XIV.H3","I-VI-017":"CH-VI-017","G1-T3":"TOE-G1-T3","FIG5-ESTAR":"CH9-N3-enclosure",
 "K12":"K12","K13":"K13","K14":"K14","K15":"K15",
 "I-TSEITIN":"I-TSEITIN","I-ENERGY":"I-ENERGY","I-ENERGY-INST":"I-ENERGY-INST",
 "I-XIII-SCOPE":"I-XIII-SCOPE","I-UG-EXT":"I-UG-EXT","I-QIS320-INST":"I-QIS320-INST",
 "I-GU-A":"I-GU-A","I-WOLFRAM":"I-WOLFRAM",
 "G1-T1":"G1-T1","G1-T2":"G1-T2","G1-RARE":"G1-RARE","G1-FLOORS":"G1-FLOORS","G1-TRIVIAL":"G1-TRIVIAL",
 "SC-8":"SC-8","G2B-DERIV":"G2B-DERIV","G2B-CL":"G2B-CL","G2B-LIMIT":"G2B-LIMIT",
 "G2B-MASS":"G2B-MASS","G2B-POSTHOC":"G2B-POSTHOC","PROOF-E-TABLE":"PROOF-E-TABLE",
 "PROOF-L7":"PROOF-L7","G2A-SELFENERGY":"G2A-SELFENERGY","G3-SPECTRUM":"G3-SPECTRUM",
 "SC-6":"SC-6","G4-INFVOL":"G4-INFVOL","G5-S1":"G5-S1","G5-S4":"G5-S4",
 "G5-COUNT":"G5-COUNT","G5-R63":"G5-R63"}

TEX_REVISIONS = {
 "G2B-CL": r"Floating-point $c_L$: FR30 $8.704, 11.324, 12.674, 13.046, 13.243, 13.318$; 1387 $9.850, 12.458, 13.685, 14.039, 14.196, 14.253$; $G_6/(\pi^2c_6)=0.9992$ for both. The frozen B2 geometric extrapolation from $(c_4,c_5,c_6)$ gives $c_\infty\approx13.364$ (FR30), $14.285$ (1387); from $(c_3,c_4,c_5)$ the same formula gives $13.463$ and $14.322$ (four-decimal inputs), so the extrapolated value moves by $0.10$ and $0.04$ with the fitting range. The geometric model $c_L=c_\infty-Aq^L$ has three parameters and is fitted to three points exactly, so no goodness-of-fit statistic exists; the range sensitivity is the only check. Both lie inside the certified brackets of Corollary E.",
 "G2B-LIMIT": r"Conjecture: along $\theta=\kappa a$ the frame connection has a continuum limit (the computed $G_L$, $L\le6$, are consistent with this; existence is not shown).",
 "G2B-MASS": r"Conjecture: in that limit the frustration survives only as a finite mass term, $\Lambda_{\rm phys}$ = (Dirichlet Laplacian of the chair region) $+\kappa^2c_\infty$, with $c_\infty$ the limit of the derived (not fitted) coefficients $c_L$.",
 "G2B-POSTHOC": r"Post-hoc B4 diagnostic (not preregistered; does not change the frozen [F]): rerun with $k=28$ puts all 20 index-wise shifts in $[0.985,0.997]c_5$ (FR30), $[0.984,0.997]c_5$ (1387); the uniform-mass-shift prediction is plausible but not established.",
 "TOE-PROOF-E-FR30": r"E (FR30): $13.232574\le\liminf c_L\le\limsup c_L\le 15.465590$ (level $\ell=6$). The two numbers are certified computations; that they bound $\liminf c_L$ and $\limsup c_L$ (and, via Theorem F, $\rho(\mathrm{FR30})$) is conditional on Theorems B, C and F, which are hand proofs.",
 "TOE-PROOF-E-1387": r"E (1387): $14.161980\le\liminf c_L\le\limsup c_L\le 16.390966$ (level $\ell=6$). Conditional on Theorems B, C and F as for FR30.",
 "PROOF-E-TABLE": r"Certified level densities $\mu_\ell\ge$, $\nu^0_\ell\le$ for FR30 and 1387, $\ell=1..6$, printed in Table~\ref{tab:munu} rounded outward from the stored full-precision bounds.",
 "TOE-PROOF-F": r"Theorem F: for every rule whose frame substitution is primitive, $c_L$ converges and $\lim c_L=\rho(d):=7\min$ over stationary closed tile-compatible fields $\xi$ of $E_\mu[\sum_k|w_k+\xi_k|^2]$. This is an application of standard ergodic homogenisation of discrete operators with stationary coefficients (Section~\ref{sec:relwork}), using unique ergodicity of the hull \cite{solomyak1997dynamics,solomyak1999corrections}, a multiparameter ergodic theorem \cite{wiener1939ergodic} and Kolmogorov--Riesz compactness \cite{hancheolsen2010kolmogorov}. Unique ergodicity of this hull and the cube-versus-ball form of the ergodic input remain unverified (Section~\ref{sec:g2}); they are not treated as newly checked [P].",
 "TOE-G2-B0": r"B0 holds (a check of the code, not physics): finite-$\theta$ Taylor ratios 0.998--0.999; an independent finite-difference test agrees to $10^{-3}$ (floating point, no error control).",
 "TOE-G5.1": r"G5.1 holds: rule 63 ($S_3$), $\lambda_1=\lambda_2=\lambda_3$ on $T_2\ldots T_5$ (7.868057, 5.345482, 4.678361, 4.280895), equal to $10^{-13}$ in floating point.",
 "TOE-G5.2": r"G5.2 holds: rule 64 ($C_3$), the same (10.838889, 8.860622, 7.680477, 6.323312), equal to $10^{-13}$ in floating point.",
 "TOE-G5.3": r"G5.3 holds: FR30 $\lambda_x=\lambda_z\ne\lambda_y$ (e.g.\ $T_5$: 7.700134, 5.386980, 7.700134), floating point.",
 "TOE-G5.4": r"G5.4 holds: 1387, x539311, x539291 have three distinct floors (minimum pair gap 0.01486, 1387, $T_4$), floating point.",
 "FIG5-ESTAR": r"$E_*(\mathrm{FR30})\in[7.954291,\,8.7642270382]$, rounded outward from the two lower-end certificates and the exact rational upper bound (ledger only, not in PROOF.md).",
}
SHORT_REVISIONS = {
 "FIG5-ESTAR": r"E_*(FR30) enclosure [7.954291, 8.7642270382] (outward)",
}
NOTE_REVISIONS = {
 "PROOF-E-TABLE": "v0.0 printed PROOF.md's values; 10 cells were nearest-rounded (discrepancies.md §1). v0.1 prints outward values from results/proof_bounds.json; PROOF.md values are given in table footnotes",
 "FIG5-ESTAR": "v0.0/v0.1 CSV short text printed the ledger interval [7.954292, 8.7642270381] (truncated upper). v0.2 paper label [E] until Phase IX mapping is ratified, and short text [7.954291, 8.7642270382], matching the outward paper statement. Owner first pass 2026-11-06 re-checked the outward arithmetic [C] and did not re-derive the certificates from source files",
 "TOE-PROOF-E-FR30": "ledger prints upper end 15.465589, PROOF.md 15.465590; stored value 15.465588903524477, so both are outward-safe. PROOF.md value kept",
 "G2B-DERIV": "non-standard source label 'P-level'; printed [E] pending ruling; the proved version is TOE-PROOF-A",
 "G1-RARE": "non-standard source label 'P-level estimate'; printed [X] pending ruling",
 "K10": "", "K6": "", "TOE-PROOF-D": "", "G2B-POSTHOC": "",
 "TOE-G2-D1": "ledger [P]; TOE text: 'at the level of formal perturbation theory'; printed [E] (Appendix C)",
}
for x in CLAIMS:
    i = x['id']
    if i in LABEL_CHANGES:
        x['paper'], x['reason'], x['pending'] = LABEL_CHANGES[i]
    else:
        x['paper'], x['reason'], x['pending'] = x['label'], "", PENDING.get(i, "")
    assert x['paper'] in "PCEXAF" and len(x['paper']) == 1, i
    x['ledger'] = LEDGER_IDS.get(i, i if i.startswith("TOE-") else "")
    if i in TEX_REVISIONS: x['tex'] = TEX_REVISIONS[i]
    if i in SHORT_REVISIONS: x['short'] = SHORT_REVISIONS[i]
    if i in NOTE_REVISIONS: x['note'] = NOTE_REVISIONS[i]

# no-upgrade check: strength order P > C > E > X > A, F separate (F never changes)
_RANK = dict(P=5, C=4, E=3, X=2, A=1)
for x in CLAIMS:
    src = [s for s in x['label'].replace('+','/').replace(',', '/').split('/') if s.strip() in _RANK or s.strip()=='F']
    if x['label'] == 'F': assert x['paper'] == 'F'
    elif x['paper'] in _RANK:
        weakest = min((_RANK.get(s.strip()[0], 0) for s in x['label'].replace('+','/').replace(',','/').split('/') if s.strip()), default=0)
        assert _RANK[x['paper']] <= max(weakest, _RANK.get(x['label'][0], 0)), (x['id'], x['label'], x['paper'])
# The 'unverified' tag marks a hand proof. TOE-G2-D1 is no longer printed as a proof, so it
# drops the tag. K6, K10, TOE-PROOF-D keep it: their [P] component is still a hand proof.
for x in CLAIMS:
    if x['id'] == 'TOE-G2-D1':
        x['unverified'] = False
