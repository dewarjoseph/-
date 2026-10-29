# Phase XIII — "The Exponential Time Hypothesis is False" (openai/math, Family 378): an independent reconstruction and a concrete audit

**Repository state.**
- Branch `claude/fervent-fermi-e2wi4y`. New in this phase: `audit/phase13_eth.py`, `audit/phase13_eth_costs.py`, their results `audit/results/phase13_eth*.json`, `tests/test_phase13.py` and this report.
- Source examined: the public repository `openai/math` at head 7ef5c0c (26 October 2026), read as data.
  - `preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/` (`main_full_version.tex`, 4 829 lines, and three quantitative appendices);
  - `lean/docs/378.md`, `lean/ComparatorChallenges/SubexponentialSAT.lean`, and the 3 977 solution files under `lean/OAI/Algorithms/SubexponentialSAT/`.
- **No code from that repository was executed**, and no other prototype was used. The reconstruction was written from the paper's text alone.
- The starting point was a transcript of an earlier session with another assistant (Gemini), which described the release and the user's local repositories. Its statements were treated as claims to check, not as findings (§5).

**Labels** (as in Phases X–XII): [P] proved; [C] computer-checked, exactly; [E] floating-point evidence; [X] conjecture or extrapolation; [F] falsified. "Claimed" marks a statement of the release that was not checked here.

---

## 0. Answer

**1. What the release claims** (read from the source; claimed, not refereed).
- *Theorem 1.1.* For each fixed k ≥ 2, a deterministic algorithm computes #F for a k-CNF on n ≥ 20 variables and m clauses in (n+m)^{O_k(1)}·2^{O_k(n log log n/√log n)} bit operations and polynomial space, and in 2^{O_{k,D}(n/√log n)} when m ≤ Dn. Taking k = 3 refutes ETH.
- *The Lean comparator statement* (`exact_count_and_sat`) proves the weaker exponent n(log log n)²/√log n with existential constants C, A, d, e, for a fixed primitive machine, with polynomial visited space. Permitted axioms: propext, Quot.sound, Classical.choice.
- Lean was not run here: the environment cannot reach the toolchain (Phase XII §9.1). None of the solution files contains `sorry`, which says nothing about whether they compile.

**2. The core construction is correct where it can be checked, and it reproduces exact counts** [C] (§3).
- An independent implementation of Sections 3–4, in exact arithmetic over ℚ (and over GF(2⁶¹ − 1) for speed), checks:
  - the swap eigenbasis, the parity interpolant f_I, M₀ = V₀f_I(W₀), the measurement matrix C^B and the rows P_u(T);
  - Lemmas 4.1, 4.2, 4.3 and 4.6 on every label, for seven parameter sets with D up to 1 024;
  - Remark 4.4 verbatim;
  - Definition 3.1 on three formula layouts.
- **The full counting routine returns the brute-force count on all 8 test formulas.** The routine is: separation by measurements (Lemma 3.2), Boolean differences (Lemma 3.3), and Hermite interpolation from the Taylor jets at t = 1, …, Q. Two of the formulas are computed exactly over ℚ; two are in the truncated regime q < n.
- **The checks can fail.** Removing one essential measurement row breaks the design condition and changes the separated sum, in 5 of 5 instances.
- This is evidence that the construction is described correctly. It is not a check of the theorem: correctness at small sizes says nothing about the asymptotic cost.

**3. The algorithm is exhaustive search for every input that could ever be written down** [C, computed from the paper's own definitions] (§4).
- **The paper's explicit parameter schedule** (Lemma 4.8, used in Section 5) passes its own integer guards only from ⌈log₂ n⌉ = 10 909 384 704. Below that, the algorithm "checks the original equations directly on all 2ⁿ assignments". So it is exhaustive search for every n < 2^(1.09·10¹⁰), a number with more than 3·10⁹ decimal digits.
- **The Lean machine's main branch** requires `GoodInput n := 32 ≤ log₂(log₂ n)`, i.e. n ≥ 2^(2³²). Every smaller input goes to the finite fallback machine.
- **Even with the parameters chosen freely** within the construction lemma's hypotheses (Lemma 4.5, bounded-occurrence 3-CNF), the paper's cost bound (Proposition 3.4) falls below 2ⁿ only for n ≥ 2^15 426 ≈ 10^4644 (degree d = n), or n ≥ 2^159 380 ≈ 10^47 978 (d = 3n). This is confirmed exhaustively for r ≤ 64. At the optimum the bound is 2^{0.99992n}.
- **None of this contradicts the theorem**, which is asymptotic. It means the refutation of ETH, if correct, has no bearing on solving any SAT instance in practice, and gives no algorithm faster than brute force at any size below these thresholds.

**4. Gemini's account, audited** (§5). Most of its description of the paper and the Lean files is accurate. Specific errors:
- 1 258 Lean files: the true count is 3 977.
- An "exp(O(n(log log n)³/log n))" bound: no such bound appears in the paper.
- "Corollary 1.3": the circuit bound is Corollary 1.4.
- "Appendix A": the tensor contraction is Appendix D.
- The measurement count O(n log log n/√log n): the paper's is 2τn = Θ(n(log log n)²/(log n)^{3/2}).
- **Its descriptions of the user's local repositories are partly checkable.** Pillar 10 and its 14 533-line, zero-`sorry` Lean file are in this repository, as described. `p_vs_np_repo` is not on GitHub, and the GitHub copy of `QIS` (last pushed 21 August 2026) contains none of the other files cited.

**5. Relation to Chair44 and to the user's p_vs_np programme** (§6).
- The release bounds no spectral floor and changes no statement of Phases X–XII.
- It does not touch restricted-model lower bounds (resolution, OBDDs, bounded-depth circuits), which concern proof systems and models, not algorithms in general.
- Its circuit corollary (C_L(n) > c·n√log n for some L ∈ E^NP) is a real but modest superlinear bound.

**No physical claim is made.**

---

## 1. What the paper does, in the paper's terms

- **Sections 2–4** count the solutions of a bounded-occurrence 3-CNF; Section 5 reduces general #k-SAT to that setting by sparsification and sparse 𝔽₂ equations.
- **The count is a sum of products of clause polynomials**: #F = Σ_x Π_e Φ_e(x), of degree d ≤ 3n.
- **Each input X_v of clause e is replaced** by a linear form ⟨P_{e,v}(T), X⟩, polynomial of degree ≤ R in a parameter T. This gives a polynomial H(T), with H(0) = #F and deg H ≤ dR.
- **The (r, τ, D)-design at each t = 1, …, Q.**
  - The variables are split into r groups of size ≤ 2n/r.
  - Each clause depends on the other groups only through ≤ 2τn integer measurements y_h = C_h x_h, each with row sum ≤ D.
  - Fixing the measurement tuple factorises the sum over groups (Lemma 3.2), with cost (2D+1)^{2τn}·2^{2n/r}.
- **Recovery of H(0).** The Taylor jets of H at t = 1, …, Q, to order q = ⌊dR/Q⌋, determine H by Hermite interpolation. Each jet is obtained by inclusion–exclusion over pairs U ⊆ E ⊆ [n] with |E| ≤ q (Lemma 3.3); there are C_q = Σ_{j≤q} 2^j·C(n, j) such pairs.
- **The forms (Section 4).**
  - Auxiliary labels: 𝓑 = ([r]^Q)², with D = r^{2Q}.
  - The swaps Π_s exchange the two sequences at position s. M₀ = V₀f_I(W₀), where f_I interpolates (−1)^j on an interval I of R values around the binomial mean.
  - C^B is formed by the swap eigenvectors with j ∉ I.
  - P_u(T) = δ_u(I − M₀) + Σ_y M₀[u,y]·∏_{s∈E_{u,y}}(1 − T/s)·δ_y.
  - The formula's incidences are placed in copies of 𝓑.
- **The three costs.** The exponent is n[(R/Q)log(2Q/R) + τ log(2D+1) + 1/r]. The parameter choice r ~ √log n/(log log n)², Q ~ log n/log log n, R ~ √log n, τ = 1/(r⌈log₂ n⌉) makes it O(n(log log n)²/√log n).
- Appendix D sharpens the exponent by recursive tensor contraction. That algorithm is not analysed here.

---

## 2. The reconstruction (`audit/phase13_eth.py`)

- **Written from the paper's statements only.**
- **M₀ is formed in two independent ways.**
  - By the expansion f_I(W₀) = Σ_S g(|S|)Π_S, whose coefficients are the Krawtchouk transform of f_I on {0, …, Q} (the Π_s are commuting involutions).
  - By direct matrix products, for D ≤ 81.
  - Both agree entry by entry. The coefficients g(k) vanish for k ≥ R, which is Lemma 4.2's mechanism.
- **The counting routine is the paper's** (Lemma 3.2 with representatives x̄_h, Lemma 3.3, Proposition 3.4, Hermite interpolation). It differs in one inessential point: it iterates over the measurement tuples that occur (tuples with an empty fibre contribute zero), not over all of {−D, …, D}^c. That enumeration would be impossible even here: c = 20 rows at D = 64 gives 129²⁰ ≈ 10⁴² tuples.
- **Field.** GF(p), p = 2⁶¹ − 1, runs are images of the rational computation: every denominator divides (R−1)!·Q! or the Hermite determinant, and 0 ≤ #F < p.

---

## 3. Verification battery (`phase13_eth.json`)

**The auxiliary construction** [C]. For every parameter set:
- f_I(j) = (−1)^j on I, and g(k) = 0 for k ≥ R;
- Lemma 4.2: every nonzero M₀[u, y] has |E_{u,y}| ≤ R − 1;
- M₀ψ = (−1)^j f_I(j)ψ on the whole basis, and M₀ψ = ψ for j ∈ I (Lemma 4.1);
- c_B equals the exact count Σ_{j∉I} C(Q, j)·(r(r−1)/2)^j·(r(r+1)/2)^{Q−j};
- Lemma 4.3: P_u(0) = δ_u, deg ≤ R − 1, and outside the assigned group P_u(t) equals the row of I − M₀, which lies in the span of C^B;
- Lemma 4.6: (R−1)!·Q!·P_u is integral.

| r | Q | R | D | c_B | M₀ also by matrix products |
|---|---|---|---|---|---|
| 2 | 2 | 2 | 16 | 1 | yes |
| 2 | 3 | 2 | 64 | 10 | yes |
| 2 | 4 | 2 | 256 | 67 | — |
| 2 | 4 | 3 | 256 | 13 | — |
| 3 | 2 | 1 | 81 | 45 | yes |
| 3 | 3 | 2 | 729 | 189 | — |
| 2 | 5 | 3 | 1024 | 106 | — |

**Remark 4.4** [C]. With r = 2, Q = R = 2 and I = {0, 1}, the row of u = (00, 11) is ζ₀ − (T/2)ζ₁ − Tζ₂, and M₀ restricted to its orbit is Π₁ + Π₂ − Π₁Π₂, as printed.

**Definition 3.1 on actual formulas** [C]. Three random bounded-occurrence 3-CNFs (n = 6, 7, 6), with (r, Q, R) = (2, 3, 2), (2, 4, 2), (3, 3, 2). In each:
- P_{f,v}(0) = δ_v and deg ≤ R − 1;
- every row sum is ≤ D (observed maximum 2);
- the kernel condition holds for every incidence, point and foreign group (exact rank tests over ℚ).

**The count** [C]:

| r | Q | R | n | clauses | d | q | J | pairs (U ⊆ E) | algorithm | brute force | field |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 2 | 3 | 2 | 4 | 2 | 6 | 4 | 5 | 243 | 12 | 12 | ℚ |
| 2 | 3 | 2 | 5 | 3 | 9 | 6 | 7 | 729 | 21 | 21 | GF(p) |
| 2 | 4 | 2 | 6 | 3 | 9 | **4** | 5 | 1 892 | 40 | 40 | GF(p) |
| 2 | 3 | 2 | 5 | 4 | 12 | 8 | 9 | 729 | 18 | 18 | GF(p) |
| 3 | 3 | 2 | 5 | 3 | 9 | 6 | 7 | 729 | 20 | 20 | GF(p) |
| 2 | 4 | 3 | 5 | 3 | 9 | 6 | 7 | 972 | 22 | 22 | GF(p) |
| 2 | 5 | 2 | 7 | 3 | 9 | **3** | 4 | 1 895 | 80 | 80 | GF(p) |
| 2 | 4 | 2 | 6 | 4 | 12 | 6 | 7 | 2 916 | 34 | 34 | ℚ |

- In every case the Taylor jets computed by the routine equal the jets of H obtained by direct summation over all 2ⁿ assignments, and deg H ≤ d_H.
- In the two bold cases q < n, so the inclusion–exclusion is genuinely truncated.

**Adversarial checks** [C], five instances. In each, the intact design gives the correct separated sum. Removing all measurement rows at t = 1, or a single essential row, makes the kernel condition fail for a clause incidence and changes the sum. Two pitfalls showed up while building this check:
- Removing one *arbitrary* row is often harmless (the row is redundant).
- Kernel failures on dummy factors are harmless too, because those factors are constant.
So the recorded check removes one row that breaks the condition for a real clause.

---

## 4. Where could the algorithm beat 2ⁿ? (`phase13_eth_costs.py` → `phase13_eth_costs.json`)

**4.1 The paper's explicit schedule** [C, integer arithmetic].
- *The schedule.* λ = ⌈log₂ n⌉, ν = ⌈log₂ λ⌉, r = ⌊√λ/ν²⌋, Q = ⌊λ/(128ν)⌋, R = (β+3)⌈√λ⌉.
- *The guards.* Section 5 checks r ≥ 2, Q > R, R ≥ 32 and 6R ≤ Q, then the balance and tail conditions. If any check fails it "checks the original equations directly on all 2ⁿ assignments".
- *Binding constraint.* The guard 6R ≤ Q binds. Within a block of constant ν the guards are monotone in λ, so the threshold is found by bisection, and the 2 000 values below it are checked one by one.

| β | least λ = ⌈log₂ n⌉ passing | ν | r | Q | R | log₂ D |
|---|---|---|---|---|---|---|
| 1 | **10 909 384 704** | 34 | 90 | 2 506 752 | 417 792 | 3.25·10⁷ |
| 2 | 17 045 913 600 | 34 | 112 | 3 916 800 | 652 800 | 5.33·10⁷ |
| 3 | 26 011 238 400 | 35 | 131 | 5 806 080 | 967 680 | 8.17·10⁷ |

- At the threshold the remaining checks hold. The balance condition holds because log₂ D ≤ λ/128. The tail condition holds because Hoeffding gives 2^{−12 556} against the required 2^{−80}.
- *The bound at β = 1.*
  - With d = n, Proposition 3.4's bound there is 2^{0.839n}: Taylor 0.817, groups 0.022, measurements 7·10⁻⁵.
  - With d = 3n, the Taylor term alone is 1.5, worse than brute force. The bound falls below 2ⁿ only by λ ≈ 6.2·10¹⁰ (scanned in steps of 2^{1/8}).
- **So for every n below 2^(1.09·10¹⁰), the specified algorithm is exhaustive search.**

**4.2 The Lean formalization** [C, from the definitions].
- In `SubexpPackingParameters.lean`, `s n = Nat.log2 (Nat.log2 n)` and `GoodInput n := 32 ≤ s n`.
- The main-branch guard `Ready` implies `GoodInput` (`ready_goodInput`). Unready inputs go to a finite fallback machine, with an existential cutoff (`exists_fallback_cutoff`).
- GoodInput holds exactly from n = 2^(2³²), about 10^(1.29·10⁹). The remaining checks in `Ready` (a prime search, dimension and tail guards) can only raise this.
- The Lean schedule differs from the paper's (it uses a prime p, Q = p⁴ − 1 and h = 4). I did not trace its parameters further.

**4.3 Free parameters, within the construction's own hypotheses** [C for the search; the Taylor term uses its n → ∞ form].
- *Setup.* For every r ∈ [3, 64], every Q, every R < Q and the interval of Lemma 4.8, take the least τ allowed by the tail condition (τ = r·b·Pr[W ∉ I], with b = w = 3). Lemma 4.5's balance hypothesis forces n ≥ 4D² = 4r^{4Q}.
- *Rate.* The rate of Proposition 3.4's bound is (α + H₂(α)) + 2τ log₂(2D+1) + 2/r, with α = (d/n)·R/Q.
- *Method.* Exponential and binary search in Q, then an exhaustive scan of every (r, Q) that could improve the optimum. None does.

| d | best r, Q, R | rate | least n with bound < 2ⁿ |
|---|---|---|---|
| n | 15, 987, 174 | 0.99992 | 2^15 426 ≈ 10^4644 |
| 3n | 17, 9 748, 591 | 0.999987 | 2^159 380 ≈ 10^47 978 |

- The exponent n(1 − rate) saved at these optima is about 10^4640 bits: an astronomical saving, but only for an astronomical n.
- The threshold grows with r above the optimum (for d = 3n it is 2^186 075 at r = 58).
- *Reading.*
  - The obstruction is structural. The Taylor term needs R ≪ Q. The tail term then needs R ≳ 5√Q, hence Q in the hundreds or thousands. Then D = r^{2Q} is enormous, and the construction needs n ≥ 4D².
  - This is a statement about the paper's bound under the paper's hypotheses, not a lower bound for every implementation. The algorithm as specified does enumerate all (2D+1)^c measurement tuples, and its Taylor loop has C_q pairs, so the bound is not loose by much.
  - The sharper Appendix D algorithm is not analysed here.

---

## 5. Gemini's account, claim by claim

| claim (Gemini transcript) | status | evidence |
|---|---|---|
| announcement on 26 Oct 2026; a "trio" of results; review shepherds Williams, Impagliazzo, Paturi | **not checked** (external news) | the repository has the ETH paper (25 Oct), Kakeya papers (23–24 Sep) and others; commit 7ef5c0c is dated 26 Oct |
| deterministic exact counting, polynomial space, fixed width, time exp(n/(log n)^{1/2+o(1)}) | **correct** | Theorem 1.1; ρ(n) at lines 87–92 |
| "does not prove P = NP" | **correct** | line 149 |
| Family 378; commit 7ef5c0cc5; file list | **correct** | `lean/docs/378.md`; `git log` |
| "Lean 4 formalization (1 258 files)" | **wrong** | 3 977 solution files (710 320 lines) plus the challenge file |
| `Final.lean` with `compiled_exact_count_and_sat`, `exact_count_and_sat`, `exact_count_eth`, `sat_polynomial_space`; `ExecutionNativeFinal.lean`; `BinomialMatrix`, `BinomialInterpolation`, `MatrixSupport`, `Annihilation` | **correct** | `find`, `grep` |
| `runtimeScale n = n (log log (n+16))² / √log (n+16)` | **correct** | comparator file, lines 132–134 |
| the construction (𝓑, Π_s, V₀, W₀, f_I, M₀, C^B, P_u, φ_{u,y}, Lemmas 4.1–4.3, Remark 4.4) | **correct**, and **reproduced** [C] | §3 |
| parameter orders r, Q, R, τ, D ≤ (2n)^{1/128} | **correct** (garbled in places; one passage reads R = Θ(log n) where the paper has Θ(√log n)) | eq. (overview-parameter-bounds) |
| "cross-group interactions factor through 2τn = O(n/(√log n/log log n)) measurements" | **wrong** | 2τn = 2n/(r⌈log₂ n⌉) = Θ(n(log log n)²/(log n)^{3/2}) |
| tensor contraction in "Appendix A" gives n log log n/√log n, and n/√log n at bounded density | **bounds correct, appendix wrong** | it is Appendix D (`quantitative-reduction.tex`, Theorem D.1) |
| "improved exp(O_k(n(log log n)³/log n)) … tensor contraction bound" | **wrong** | no such bound appears in the paper |
| "Corollary 1.3: C_L(n) > c n √log n, L ∈ E^NP" | **statement correct, number wrong** | Corollary 1.4 (the counter is shared within §1) |
| Beigel–Tarui polynomial; 𝒜_ℓ = ℚ[V]/(V^ℓ) in Section 5 | **correct** | lines 1592, 2902, 2945 |
| a Python prototype with "8 test suites pass" | **not checked** (local, not available) | not used here |
| Pillar 10 manuscript and `PvsNPCliffordCertificates.lean`, 14 533 zero-sorry lines | **correct** (found later in *this* repository) | `deliverables/pillar10_p_vs_np_clifford_complexity.tex`; `certificates/PvsNPCliffordCertificates.lean`: 14 533 lines, 440 `#print axioms`, 508 theorems, no `sorry` (the abstract says 14 527 lines). Not compiled here |
| the user's `p_vs_np_repo` phases 1–3; `QIS` `CLAIMS_LEDGER.md`, `NEE_CLOSED_LOOP.md`, `SLRCompare.lean` | **not checked** | `p_vs_np_repo` is not on GitHub; the GitHub `QIS` (head 952985c, 21 Aug 2026) has none of these files |

---

## 6. What this means, and what it does not

- **For the extremal Chair44 problem (Phases X–XII): nothing changes.**
  - The release concerns counting Boolean solutions. It bounds no spectral floor.
  - Phase XII §15 already showed that the Unique Games Theorem from the same release does not apply.
  - The Chair44 certificates are finitely many local eigenvalue problems, not instances of SAT.
- **For a research programme on P vs NP.**
  - The refutation of ETH, if correct, removes 2^{Ω(n)} as a hypothesis for *general* algorithms. Every conditional lower bound derived from ETH or SETH loses its premise.
  - It leaves untouched the unconditional lower bounds for restricted models (resolution, regular resolution, OBDDs, bounded-depth circuits, communication protocols). Those concern proof systems and computational models, not algorithms in general. The algorithm itself is algebraic, interpolating through values outside {0, 1}, and is not a proof in those systems.
  - Its circuit consequence, C_L(n) > c·n√log n for some L ∈ E^NP (via Williams' algorithmic method), is unconditional but small: superlinear by a √log n factor.
- **For practice: nothing.**
  - For every input size below 2^(1.09·10¹⁰) (paper) or 2^(2³²) (Lean), the specified algorithm is exhaustive search.
  - Even ideal parameters within the construction's own hypotheses beat 2ⁿ only beyond 10^4644.
  - Existing SAT solvers, local search, and the continuous relaxations studied in the user's earlier work are unaffected.

---

## 7. The five statements

1. **Strongest result proved or checked here** [C]. An independent, exact reconstruction of the paper's construction and counting routine agrees with the paper's lemmas on every label of seven parameter sets. It returns the brute-force count on eight formulas, including the truncated regime q < n. A broken design is detected.
2. **Strongest new quantitative result** [C].
   - The paper's explicit schedule activates only for ⌈log₂ n⌉ ≥ 10 909 384 704.
   - The Lean main branch activates only for n ≥ 2^(2³²).
   - Within the construction's hypotheses, Proposition 3.4's bound beats 2ⁿ only for n ≥ 2^15 426 (d = n) or 2^159 380 (d = 3n), confirmed for all r ≤ 64.
3. **Most important negative result.** The refutation of ETH, if correct, is purely asymptotic. The specified algorithm, in the paper's schedule and in the Lean machine, *is* exhaustive search on every input that could be stored in the observable universe (any such n is below 2^(2³²)). With freely chosen parameters, the paper's own bound beats 2ⁿ only beyond 10^4644.
4. **Open.** Whether the sharper tensor-contraction algorithm (Appendix D) has a usable regime. Whether the Lean proof compiles: it was not run here.
5. **Next step.**
   - Run the comparator (Lean, with the repository's toolchain) on a machine that can reach it.
   - Extend §4 to Appendix D's parameters.
   - If the user's local `p_vs_np_repo` and `QIS` are pushed, check the Gemini-reported statements about them against the files.

---

## Reproduction

| step | command | output | time |
|---|---|---|---|
| verification battery | `python -u -I audit/phase13_eth.py` | `phase13_eth.json` | ≈ 1 min |
| cost analysis | `python -u -I audit/phase13_eth_costs.py` | `phase13_eth_costs.json` | ≈ 10 min |
| tests | `python -m pytest -q tests/test_phase13.py` | — | 6 s |

Requires the `openai/math` clone only for the claims of §5 (file counts and line references). The scripts themselves use only the paper's definitions, restated in their docstrings.
