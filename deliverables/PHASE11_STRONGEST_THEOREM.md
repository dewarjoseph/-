# The strongest theorem of Phase XI (one page)

**Setting.**
- G = (V, E) is a countable graph, multi-edges allowed, with every degree ≤ d.
- U assigns a unitary U(v→w) ∈ U(n) to each oriented edge, with U(w→v) = U(v→w)⁻¹. Any rank n, any structure group.
- H_U = D_U†D_U = Deg − A_U and E_\*(U) = inf σ(H_U).
- An *environment* of radius R is a rooted ball with its degrees and its connection, up to rooted isomorphism and gauge.
- D_R(U) is the infimum, over the environments that occur, of the least eigenvalue of the Dirichlet compression.

## Theorem (support-sensitive spectral-frustration principle)

**(1) Support.** D_R(U) ↓ E_\*(U) as R → ∞.
- E_\* depends only on the set of environments that occur, and is order-reversing in that set: more legal environments, lower or equal floor.
- It does not depend on frequencies, invariant measures or correlations.
- No hypothesis beyond bounded degree is needed. No rate holds in that generality.

**(2) Two-sided local certificates, uniformly over all connections.** For any partition of unity Σχ_j² = 1 whose pieces lie in balls of radius R,

  Λ(χ) ≤ E_\*(U) ≤ D_R(U),  D_R(U) − Λ(χ) ≤ ε(χ) := sup_v Σ_{e∋v}(1/c_e − 1),  c_e = Σ_j χ_j(v)χ_j(w).

Here Λ(χ) is the minimum, over the pieces, of the least eigenvalue of Deg − Ã_U, with every link divided by c_e. This is an exact identity H_U = Σ_j χ_j(Deg − Ã_U)χ_j.
- Uniform convergence (inf_χ ε → 0) holds **iff G has property A**.
- If G is uniformly doubling with constant C_D, the error is **≤ 16 d C_D²/R²**.
- If G has a proper realisation c: V → ℝ^D with S_c = sup_v Σ_{w∼v}|c(v) − c(w)|² and h = max edge length, the error is **≤ K_D S_c/ρ²** with K_D = (j_D²/2D)/(1 − j_D²h²/(2Dρ²)). Here j_D² is the first Dirichlet eigenvalue of the unit D-ball.
- For the chair tiling, D = 3, S_c = 4734/49, h = 15/7.

**(3) Sharpness.**
- R⁻² cannot be improved: on ℤ^D with trivial links, D_R − E_\* ≥ 2D/(R + 1)².
- Bounded degree alone does not give R⁻²: on the lamplighter ℤ₂ ≀ ℤ^k, D_R − E_\* ≥ c_k R^{−2/k}.

**(4) Quantitative frustration bound and its converse.** Suppose every ball of radius r contains a based loop whose holonomy has all eigenvalue arguments of modulus ≥ θ₀ > 0. This is automatic for the spinor representation of any finite subgroup of SU(2) once every r-ball is non-flat; θ₀ = π/2 for Q₈. Then

  **E_\*(U) ≥ 2 sin²(θ₀/2) / ((2r + 1)·max_v|B_r(v)|).**

- Conversely, a flat ball B_R gives E_\* ≤ λ^D_trivial(B_R).
- On graphs where these Dirichlet values tend to 0 (ℤ^D, amenable Cayley graphs), E_\* > 0 ⟺ the flatness radius is finite.

**(5) Obstructions.**
- (a) No lower-semicontinuous function of environment frequencies is a non-trivial lower bound on E_\*.
- (b) For every R, connections with identical radius-R languages can have different E_\*.
- (c) The plaquette conjugacy-class field does not determine E_\*. For a finite group, every non-spinor representation's floor is a function of it; the failure is confined to the non-Abelian irreducible component.
- (d) Neumann (free-boundary) localisation does not converge to E_\*. On the π-flux ladder it converges to 2 − √2 < 3 − √5 = E_\*.

## Hypotheses that matter, and where they enter

| hypothesis | needed for | fails without it |
|---|---|---|
| bounded degree | (1)–(4) | H_U unbounded |
| complete legal-environment enumeration | any certificate built on (2) | a visible-only enumeration gave a **false** certificate: ≥ 0.522 claimed, true floor ≤ 0.408 (ladder) |
| property A, or doubling, or a Euclidean realisation | uniform rate in (2) | lamplighters: R^{−2/k}; non-A graphs: no uniform IMS certificate |
| angle gap (fixed-point-free holonomy) | (4) | ℤ², diag(1, π-flux): every ball non-flat, E_\* = 0 |
| minimality (or components permuted by symmetries of H) | E_\* constant on a hull | a → aab, b → bb: E_\* ≤ 0.408 on the fixed point, 3 − √5 on b^∞ |

## What it does not establish

- It does not compute E_\* for any Chair44 rule. It brackets it, with every bound recomputed independently.
  - Class 1387: [8.7999990, 9.3679502].
  - FR30: [7.9542913, 8.7642271].
- It does not decide the extremal rule. What is certified instead (by (2) plus exact Rayleigh quotients, over all 6⁸ frame rules):
  - the maximiser lies in the six-rule orbit of 1387 under right multiplication of the child frames by the chair's point group: {1387, 1389, 1391, 539311, 539291, 539288};
  - the six intervals all overlap;
  - by sampled probes, no IMS certificate at R ≤ 22 separates the co-leaders 1387 and 539311 (Λ_R ≤ 9.17 and ≤ 9.19, against upper bounds 9.37 and 9.39).
- Bound (4) is valid but weak on Chair44: it is far below the certified floors. Curvature data certify positivity, not extremality.
- Most of (1)–(3) is established mathematics: the variational principle, IMS, property A and isoperimetry, assembled here for connection Laplacians.
  - Not found in the literature: the discrete form of (4) with explicit constants, the representation-theoretic confinement in (5c), and the explicit counterexamples in (5b) and (5d).
- No physical law, quantum dynamics or particle spectrum follows from a spectral floor.
