# The strongest results of Phase XII (one page)

**Setting.**
- (G) G = (V, E) is a countable, locally finite multigraph without loops, with every degree ≤ d.
- (U) Each oriented edge carries U(v→w) ∈ U(n), with U(w→v) = U(v→w)⁻¹.
- (H) H_U = D_U†D_U = Deg − A_U on ℓ²(V; ℂⁿ), bounded, with domain all of ℓ², and E_\*(U) := inf σ(H_U) = inf over finitely supported ψ ≠ 0 of q_U(ψ)/‖ψ‖².
- For Chair44: G is the panel multigraph of a chair tiling, U(a→b) = (σ·M_aᵀe_k)(σ·M_bᵀe_k) ∈ Q₈, Deg ≡ 24, and E_\*(r) = inf over the hull of rule r.

## Theorem 1 (support-sensitive two-sided principle; corrected from Phase XI)

**(1a)** E_\* = inf{λ_min(P_K H_U P_K) : K a finite legal patch} = lim_R D_R, with D_R ↓.
- E_\* is a function of the set of legal environments, and order-reversing in it.
- It does not depend on frequencies.
- Nothing beyond (G), (U), (H) is assumed. Neither (G) nor property A gives a rate.

**(1b)** For every partition of unity Σ_jχ_j² = 1 with finite pieces K_j and c_e = Σχ_j(v)χ_j(w) > 0, the identity q_U = Σ_j⟨χ_jψ, (Deg − Ã_U)χ_jψ⟩ holds exactly. Hence

  inf_j λ_min(P_{K_j}(Deg − Ã_U)P_{K_j}) ≤ E_\* ≤ D_R,

and the lower side is ≥ inf_j λ^D(K_j) − ε(χ), with ε(χ) = sup_vΣ_{e∋v}(1/c_e − 1).

**(1c) Rates.**
- ε ≤ 16dC_D²/R² on uniformly doubling graphs, for R ≥ 4C_D.
- ε ≤ K_D(ρ)S_c/ρ² for a proper realisation in ℝ^D. Here the pieces are Euclidean balls of radius ρ > j_D h/√(2D), and K_D(ρ) = (j_D²/2D)/(1 − j_D²h²/(2Dρ²)).
- R⁻² is optimal (ℤ^D). Property A alone gives no power: the lamplighter ℤ₂ ≀ ℤ^k, k ≥ 2, has rate ≥ c_kR^{−2/k}.

**(1d) Boundary conditions and coverage.**
- Neumann windows are not compressions. On the π-flux ladder they converge to 2 − √2 < 3 − √5 = E_\*.
- A lower bound computed over a strict subset of the legal environments can be false (ladder: 0.49054 claimed, ≤ 0.40791 true).

## Theorem 2 (Orbit Lemma; new) [P, with every finite step checked exhaustively]

For a frame rule d with child factors h_c and Q in the chair's point group S₃:
- let d·Q have factors h_cQ;
- let ρ_Q(M, T) = (MQ, T);
- let conj_Q be the S₃-conjugation of rules.

Then:
- **(a)** σ_{dQ} = ρ_Q∘σ_d, and ρ_Q preserves every tile's cube set.
- **(b)** ρ_Q is a global gauge transformation of every patch: U^{ρ_Q} = W_Q U W_Q†, with W_Q = x/|x| for an explicit integer quaternion x.
- **(c)** T₁(dQ) ≅ T₁(d) (unitarily), and the shadows are permuted, χ_k ↦ χ_{Q(k)}.
- **(d)** If conj_Q(d) = d, then T_L(dQ) ≅ T_L(d) for all L, and **E_\*(dQ) = E_\*(d)**.
- **(e)** Otherwise σ_dρ_Q ≠ ρ_Qσ_d, and the equivalence fails from level 2 on.

The same holds verbatim for the cube family with the θ-connections, for proper Q and all θ. Improper Q map θ to −θ, so for them it holds only at the Pauli point θ = π/2.

## Certified corollaries [C]

1. **E_\*(1387) ≥ 9.1104981** (radius 20, 24 571 legal balls). E_\*(1387) ∈ [9.1104981, 9.3679502].
2. **The maximiser of E_\* over all 6⁸ = 1 679 616 Chair44 frame rules is one of 1387, 539311, 1389, 539291.** Every other rule has an exact rational upper bound below a certified lower bound of 1387.
3. **The six-member S₃ orbit at the top of the frontier is not a symmetry of the operator.** E_\*(539288) ≤ 9.0982535 < 9.1104981 ≤ E_\*(1387), with 539288 = 4753·(0 2 1), although T₁ of the two rules are unitarily equivalent.
   - So **no function of level-one data determines E_\*** (Theorem 3.1 of the report).
4. E_\*(539315) = E_\*(FR30): 1386 is fixed by conj_{(x y)}, an instance of (d).
5. **The lemma's moves are complete at level 3.** Inside right orbits, the exact level-3 spectral coincidences are precisely the closure of conjugation and the stabiliser clause. There are 1612 tied pairs among 1 401 660, with 0 unexplained and 0 related-but-split. Beyond level 3 this completeness is a conjecture.

## What this does not establish

- **No global optimum.** 1387 is the best-resolved frontier member. 539311 has a higher upper bound (9.3885938), and, by sampled probes, no IMS certificate at the probed radii up to 22 separates them.
- **No quantitative law for the splitting** inside an orbit. The conjugation defect was preregistered as such a law and **failed** (Spearman −0.06).
- **No sharp curvature bound.** The support-sensitive transport bound is valid (1.69926 for the orbit of 1387) but captures under a fifth of the floor. Lengths, overlaps, eigenangles and plaquette classes cannot be sharp: the ℤ³ pair has identical inputs and floors separated by 0.18165.
- **No proof-assistant formalization.** Lean was unavailable; the finite core is checked by exact computation.
- **No physical law, observable or particle spectrum.**
