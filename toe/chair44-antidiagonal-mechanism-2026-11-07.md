# Chair44 anti-diagonal: finite-box structure-factor mechanism

Internal unification-programme leftover · 7 Nov 2026 (PST). No new scored run or Lean implementation.

## Phase summary

- **[P, elementary]** The DFT separates integer-position amplitudes from orientation-dependent centroid phases. This explains why the anti-diagonal is a distinguished place to inspect interference, but does not prove why the computed excess concentrates there.
- **[C on patch]** The high-denominator D1 plateau drops by 0.05494734 between the stored L=32 and L=64 box analyses; the separate same-q median ratio is 0.06362730. The line is not uniformly fading: its central dyadic peak at (1/2,1/2,0) is strong, I64=0.9034208899704588, and essentially unchanged.
- **Important correction [P]:** the integer FFT *indices* wrap, but the physical D1 structure factor is **not generally unit-periodic in q**. Its noninteger centroid offsets prevent identifying (1,0) or (0,1) with Gamma at equal intensity. The slower end tails can be leakage near strong integer reciprocal peaks; calling them “just Gamma wraparound” is not justified.
- **[X]** The fade interpretation, its mechanism, and the competition between weak high-denominator peaks and a continuous sheet/rod remain unresolved. CH-V-020 stays [X]; decorations remain [A]. Nothing here upgrades Theorem F, TOE-PROOF-F, CH-VA-019, [S], or unique ergodicity, or falsifies remainder (M).
- **[C on patch]** Mean D1 points per box are exactly 262144/56 at L=32 and 262144/7 at L=64 (ratio 8). Mid-line same-q median ratio (10 pixels with torus distance d0 to the origin in (0.2, 0.6)) is 0.057373318522754325; the wraparound pair ratio is 0.7811193565051474; the den-L plateau ratio is 0.05494734033155176; the off-diagonal den-L floor ratio is 0.014127358437406604 (near 1/64); median streak/floor contrast rises from about 106.36 to about 413.67.
- **[X]** Mid-line fade near 1/16 is compatible with the hop's M ~ L rod/line reference under I = |F/N|^2, which is a different ruler from the scripts' sheet/rod-like ~ 1/2 bar. The slow ends are a separate near-corner mechanism: every den-32 line pixel is the same distance √2/32 from the nearest den-≤16 point on the line, so that distance does not explain the ratio table. No hull rod, fade law, or CH-V-020 upgrade follows.
- **[F]** On-grid Dirichlet/sinc leakage of dyadic DFT-bin peaks, including (1/2,1/2,0) and Γ, is not the source of the inter-peak den-L intensity: a cube-window kernel is identically 0 at every other DFT bin, while the observed L=64 den-L anti-diagonal median is 2.3131609108000826e-07.
- **[C on patch]** Immediate anti-diagonal neighbors of (1/2,1/2,0) at L=64 have I = 2.309710531541855e-07, darker than the axis-neighbor median 6.039869209481548e-07 and the main-diagonal-neighbor median 8.846444894797149e-07, and essentially equal to the mid-ridge rather than a decaying tail of that peak.
- **[C on patch, QC stored sums, not rerun here]** The stored decoration comparison records matching den-L medians on the three ⟨110⟩ lines perpendicular to the chair [111] axis, and that integer centers or a uniform shift do not carry the streak. Each of those lines is hot in only three of seven occupied octants. Two other lines in q_x+q_y+q_z ∈ Z are bright after averaging, mostly from the (0,0,0) box — not a filled sheet in every octant. Fade reading and CH-V-020 stay [X].
- **[P, elementary] / [F] as a same-type companion / [X] brightness:** From cen = T + (13/14)G(1,1,1), the extra line (t,t,1−2t) is not predicted as a same-type companion of the three ⟨110⟩ lines (only 2 of 8 orientation classes have a t-independent phase, versus 4 of 8 on each ⟨110⟩ line). The extra line (t,1/2,1/2−t) is predicted as a parallel companion of (t,0,1−t) by the same s_x=s_z criterion. Equal intensity is not predicted [X].
- **[C on patch, QC stored controls, not rerun]** Official q_z=0 planes meet both extra lines only at the stable D1 peak (1/2,1/2,0) (I64=0.9034208899704588), so they cannot recertify either off-plane ridge. On a regenerated FR30 decoration, integer centers and a uniform shift drop both extra lines to the same isotropic floor ~7.1304928631e-10 as the ⟨110⟩ lines; shuffling (seed 1) leaves a brighter near-isotropic background fading at 0.10383090888712813 and 0.1160913692924512. The residual elevation is pairing-dependent, which does not upgrade (t,t,1−2t) to a same-type companion or change the fade reading. Fade reading and CH-V-020 stay [X].
- **[C on patch, QC independent check of §9]** QC opened the intermediate note sha256 `4db997ff8f31927887a07898878251c961bd4e1a3c128c9da23f629cfed39c88` against [S15] and recorded no numeric correction to that transcription [S17]. They independently enumerated the eight orientation classes and recovered the same freeze counts. The stored [S15] seven-box L=64 medians of (t,1/2,1/2−t) and (t,0,1−t) are 3.5356498231057164e-07 and 2.3131609108003926e-07; their ratio is 1.5284928111128775, so the medians are unequal [C on patch]. That is consistent with equal intensity remaining unpredicted [X]. Same-type companion stays [F]; parallel companion stays [P, elementary]; fade reading, CH-V-020, and sheet/hull stay [X]. Cyclic midpoint parallels were not summed.

## 1. Definition actually used

The streak script [S1, lines 84–139] builds `supertile(FR30,6)` from [S6], then takes D1 tile centroids with b=1. For each nonempty cubic box B,

    F_B(q) = (1/N_B) sum_{r in B} exp(2 pi i q·(r-lo_B)),
    I_L(q) = (1/M_L) sum_B |F_B(q)|².

L=64 uses seven occupied octants with origins 64(i,j,k), excluding (1,1,1); L=32 uses their 56 sub-boxes. Shifting each box only changes its overall Fourier phase, not its intensity. This is an **average of box intensities**, not the coherent transform of the entire large chair-with-a-hole. Box weights are equal, not N_B-weighted. D1 has 37449–37450 sites per 64-box and 4681–4682 per 32-box [S2].

The planes store q=(jx/L,jy/L,0), with array axes [jx,jy]. The mask is `(jx+jy)%L==0`, excluding (0,0), hence qx+qy=1 in the displayed half-open unit square. `den=L/gcd(jx,jy,L)` reduces on this mask to L/gcd(jx,L); den=L selects odd jx for these power-of-two L. These are grid/mask facts, not assertions of physical reciprocal periodicity.

## 2. Chair geometry and the phase that encodes orientation

[Sources S1, S6.] UCUBES contains doubled cube centres (2u+1), u in {0,1}³ except (1,1,1). In physical units, each coordinate of the full eight-cube centre sum is 8; removing the upper cube centre subtracts 3/2, so the seven-cube centroid is (13/14)(1,1,1). This arithmetic was independently checked with exact rational sums, without running the geometry generator.

For a pose (G,T), G is a signed permutation and T is integral. Thus, with s=G(1,1,1) in {−1,+1}³,

    r = T + (13/14)s = n − s/14,    n=T+s in Z³.

The fractional coordinate is 13/14 when s_a=+1, and 1/14 when s_a=−1. These are two classes **per coordinate**, allowing eight offset vectors, not just two 3D species. FR30 specifies child permutations and sign flips; `supertile` iterates G'=Gh and T'=2T+Gt. No extra cubic symmetry of the resulting diffraction is assumed.

Exactly, for a finite box (with integer box shift absorbed into n),

    F_B(q) = sum_s exp(−2 pi i q·s/14) A_{B,s}(q),
    A_{B,s}(q) = (1/N_B) sum_{k:s_k=s} exp(2 pi i q·n_k).

Each A_s is unit-periodic; their phase-weighted sum need not be. On q=(t,1−t,0), the orientation factor is

    exp(−2 pi i [s_y+t(s_x−s_y)]/14).

For s_x=s_y it is independent of t; for s_x=−s_y its phase depends on (2t−1)s_x. Thus orientation-class cross terms really can reinforce or cancel differently along this line **[P identity]**. That this interference causes the measured high-denominator streak, or its fade rate, is **[X]**: the landed planes do not separate the A_s or their cross terms. This is a point-decoration phase, not an assumed physical atomic form factor.

## 3. Ends, Gamma, and the central dyadic peak

For b=1, F_B(0)=1 and I_L(0)=1, confirmed in both landed D1 planes [S3]. But q→q+m multiplies each centroid term by exp(2 pi i m·r), which is not a common phase for arbitrary integer m. In particular, for m=e_y the factors are exp(−2 pi i s_y/14), not all 1. Therefore the plotted corners are Gamma images only for the integer *base-grid channels*, not exact aliases of the D1 physical intensity. The grid excludes q=1 itself.

The samples (1/L,1−1/L,0) and its transpose are nearest to the corners on this displayed line. They are nearest to Gamma **in the quotient-coordinate picture**, but physically near e_y or e_x. The elementary endpoint bound in §6 proves these integer peaks are strong even without an orientation-balance assumption. Leakage from them is a plausible end-tail mechanism [X]; the two planes alone cannot establish it as the sole explanation.

**[C on patch]** Read directly from [S3]; all q below have qz=0. Numbers are stored floating-point values (display approximations, not certified numerical bounds):

| qx,qy | I32 | I64 at the same q | I64/I32 |
|---|---:|---:|---:|
| 1/32,31/32 | 1.80166513085e−5 | 1.40731550765e−5 | 0.7811193565 |
| 31/32,1/32 | 1.80166513085e−5 | 1.40731550765e−5 | 0.7811193565 |
| 15/32,17/32 | 4.18052876092e−6 | 2.39522397862e−7 | 0.0572947614 |
| 17/32,15/32 | 4.18052876092e−6 | 2.39522397862e−7 | 0.0572947614 |
| 13/32,19/32 | 4.17614845322e−6 | 2.35049309348e−7 | 0.0562837533 |
| 1/2,1/2 | 0.903424825957 | 0.903420889970 | 0.9999956433 |
| 1/2,0 | 0.534647526235 | 0.534647494600 | 0.9999999408 |
| 0,1/2 | 0.534647526235 | 0.534647494600 | 0.9999999408 |
| 1/4,0 | 3.87459701625e−4 | 3.87453352252e−4 | 0.9999836128 |
| 1/4,3/4 | 7.20988318714e−3 | 7.20594308600e−3 | 0.9994535139 |
| 3/4,1/4 | 7.20988318714e−3 | 7.20594308600e−3 | 0.9994535139 |
| 1/8,7/8 | 2.32647715988e−3 | 2.32253544624e−3 | 0.9983057157 |
| 7/8,1/8 | 2.32647715988e−3 | 2.32253544624e−3 | 0.9983057157 |
| 3/8,5/8 | 1.05014168528e−5 | 6.56018484330e−6 | 0.6246952135 |
| 5/8,3/8 | 1.05014168528e−5 | 6.56018484330e−6 | 0.6246952135 |

At the nearest L64 end sample (1/64,63/64,0), [S2/S3] gives I64=1.1154861061185147e−6. That is a different q from (1/32,31/32,0), so it must not replace the same-q tail comparison.

**Selection-rule caution:** (1/2,1/2,0) is not weak: it is the maximum off-origin D1 pixel in this plane. There is no weak-centre extinction to explain. The README's (0,1/2,1/2) example is a different listed coordinate, not evidence requiring us to infer this plane value by cubic symmetry. The stored L=64 intensity 0.9034208899704588 occurs only at (1/2,1/2,0), so a same-strength comparison with (0,1/2,1/2) cannot be made from these q_z=0 planes. Same denominator also does not decide stability: (1/8,7/8,0) and (3/8,5/8,0) are both den-8, but only the second fades (ratio 0.6246952135 versus 0.9983057157). Strong dyadic pixels must be separated from the fading in-between plateau.

## 4. Two distinct D1 summaries and the reference ruler

Recomputed medians/percentiles from [S3] agree with [S2]:

1. **Changing q sets:** den-32 line pixels at L32 (n=16) have median 4.209777756016015e−6; den-64 line pixels at L64 (n=32) have median 2.3131609108000826e−7. Their ratio is 0.05494734033155176.
2. **Fixed q set:** the same 16 den-32 line pixels have median I64=2.6803385119686617e−7 and median I32=4.209777756016015e−6. The **median of their individual ratios** is 0.06362729841650083; p10=0.05580883569670223, p90=0.5255304654777284. This is neither summary 1 nor a definition as a ratio of medians.

The mid-line examples above are approximately 0.056–0.057, while the end tail is approximately 0.78. Both summaries and the mid-line values are near the 1/16=0.0625 ruler, below the script's Bragg~1, sheet/rod~1/2, line-leakage~1/4 and 3D-diffuse~1/8 rulers. **All those bars, including 1/16, are [X] reference scalings, not fitted models or universal DFT theorems.** No exponent was fitted here. The original diffraction script's normalization comment describes L^−2 sinc leakage and L^−3 diffuse as reference behaviours, not applicable bounds on every q.

Existing H3 at (1/3,0,0), a different q, records ratio 0.2500777662631863 in [S7], L^−2-like; its frozen H3 FAIL is unchanged. It was read, not rerun or rescored.

At L64 the line den-64 median exceeds the stored off-diagonal den-64 control median 5.591859377559668e−10 by approximately 413.666 (about 400×). These two masks compare medians, not a pointwise contrast bound. The excess is real on this patch, yet the in-between intensity fell; that supports the cautious finite-box fade reading [X], not a stable Bragg ridge on these tested pixels and not a classification of the whole line or infinite hull.

## 5. What mechanism is, and is not, supported

- **[F] On-grid Dirichlet/sinc leakage of DFT-bin peaks:** a cube-windowed on-grid tone (including Γ and (1/2,1/2,0)) has weight identically 0 at every other DFT bin, so it cannot be the source of the observed den-L ridge. See §8 and Lemma E. The axis-end intensity still rises relative to the mid-ridge [C on patch]; that profile is not this kernel.
- **[X] Remaining end-tail mechanism:** after dropping on-grid Dirichlet/sinc leakage, the slower axis-end fade (ratio 0.78111935650515 at (1/32,31/32,0)) is still unexplained. “Gamma wraparound” without centroid phases remains incorrect, because D1 I(q) is not unit-periodic.
- **[X] Hierarchical alternative:** weak high-denominator dyadic peaks on qx+qy in Z can mimic a ridge at finite resolution. A continuous sheet/rod is another hypothesis. A 2D qz=0 section and two sizes do not distinguish these or establish a hull spectral type. All sampled q here are dyadic, including those that fade.
- **[P identity / X attribution] Orientation interference:** the explicit phase decomposition in §2 is verified geometry. QC stored decoration sums [S11] find that destroying the position–orientation pairing removes the directed streak; that comparison was not rerun here. Attribution of the quantitative fade rate remains [X].
- **[A, Fourier-dual suggestion] Real-space (1,1,0) correlations:** expanding |F|² gives N^−2 sum_{k,l} exp(2 pi i q·(r_k−r_l)). Displacements a(1,1,0) contribute exp(2 pi i a(qx+qy)), constant along each such line (and equal to 1 at qx+qy=1 when a is integral). That is a duality identity, not evidence that this point set has sufficient such correlations to generate a ridge. No empirical correlation claim is made.

The existing explain figures are documented in README Turn 3 [S4], including separate plateau and same-q plots. They were not regenerated or newly scored, and are not independent evidence added here. No measured-crystal comparison or multi-window P/F result is used.

## 6. Checkable finite-N statements for Lean Proof Lab (no Lean written)

**Lemma A [P, arbitrary finite D1 averages].** Let M≥1, each N_B≥1, r_{B,k} in R³, b=1, and F_B,I be defined as in §1. For every real q, 0≤I(q)≤1 and I(0)=1. Proof: triangle inequality gives |sum_k exp(2 pi i q·r_k)|≤N_B; average the squared bounds. No infinite-volume, convergence, uniform decay, or unique-ergodicity assertion follows.

**Lemma B [P, mask and denominator].** For integer L≥2 and 0≤jx,jy<L, not both zero, at jz=0: L divides jx+jy iff qx+qy=1. On that mask jy=L−jx and gcd(jx,jy,L)=gcd(jx,L); hence den=L iff gcd(jx,L)=1. For L=2^m, m≥1, this is exactly odd jx (L/2 points). No Bragg-weight assertion follows.

**Lemma C [P, phase rewrite].** For all real t,x,y,

    exp(2 pi i [t x+(1−t)y])
      = exp(2 pi i t(x−y)) exp(2 pi i y).

The last factor cannot be dropped for D1 centroid y. The orientation-channel identity of §2 follows for r=n−s/14 with n integral and s in {−1,+1}³. Neither identity bounds a fade rate.

**Lemma D [P, finite chair-centroid integer-peak bound].** Let N≥1, r_k=n_k−s_k/14 with n_k in Z³ and s_k in {−1,+1}³, b=1. For any coordinate a, put mu_a=N^−1 sum_k s_{k,a}. Then

    F(e_a) = cos(pi/7) − i mu_a sin(pi/7),
    |F(e_a)|² = cos²(pi/7) + mu_a² sin²(pi/7),
    cos²(pi/7) ≤ |F(e_a)|² ≤ 1.

Proof: exp(2 pi i n_{k,a})=1 and s_{k,a}=±1; expand each exponential and take the modulus. Equal averaging over any nonempty boxes preserves the same exact lower and upper bounds. This is stronger than Lemma A only at these integer vectors, relies on the verified centroid geometry, and does not assert I(e_a)=I(0), a tail profile, an L-decay rate, or a hull statement. Bounds are left exact (no inward-rounded numerical bounds).

**Lemma E [P, elementary window kernel].** Let L≥2 be an integer. For any integer k not divisible by L,

    sum_{n=0}^{L-1} exp(2 pi i k n / L) = 0,

and equivalently sin(pi k) / (L sin(pi k / L)) = 0, since sin(pi k) = 0 while sin(pi k / L) ≠ 0. The separable cube window is the product of these one-dimensional factors. Therefore a cube-windowed on-grid tone sitting at one DFT bin has weight 0 at every other DFT bin. A direct floating-point evaluation of that sine formula at L=64 for k=1,…,63 has maximum absolute value about 2.4e-15 (roundoff), consistent with the identity, not a physical sidelobe. This falsifies that kernel as the source of a nonzero intensity at those bins. It does not bound a fade rate, identify the ridge, or say anything about the infinite hull.

**No new checkable analytic fade bound** follows here beyond these elementary identities and finite-N bounds. There is no proposed Lean lemma converting the patch ratios into a hull claim or Theorem F. Lemma E may be formalized as a DFT identity; it is not a fade inequality and does not upgrade Theorem F.


## 7. Rod/line versus near-corner leakage

This section absorbs the 7 Nov 2026 Research Publishing hop
`/home/box/shared/research-publishing/chair44-antidiagonal-fade-mechanism-hop-2026-11-07.md`
(sha256 `fa2bb6e3b9a99ce64efb0d216ac871b869b5ea2ed6bb65733be011426ec0a355`; walk-in
`/home/box/shared/theory-of-everything/handoff-from-chair44-fade-mechanism-2026-11-07.md`)
and recomputes its numbers from [S2] and [S3]. No label is upgraded. CH-V-020
stays [X]; the fade reading stays [X]. Theorem F, TOE-PROOF-F, CH-VA-019, and [S]
are not upgraded. No L=128 run and no icosahedral or measured-crystal comparison.

### N scales as volume [C on patch]

D1 point counts from [S2]: 56 boxes at L=32 with total 262144 sites (mean
exactly 262144/56) and 7 boxes at L=64 with the same total 262144 sites (mean
exactly 262144/7). The ratio of means is exactly 8 = 2^3. Each L=64 box is the
union of eight L=32 sub-boxes, so N scales as volume for these boxes. A 3D
incoherent scale I ~ 1/N would therefore drop by 1/8 = 0.125 when L doubles.

### Two [X] reference accountings must not be merged

The hop writes a coherent-cluster accounting: I = |F/N|^2 and a cluster of M
scatterers scales as I ~ M^2 / N^2 [X, reference accounting, not a theorem]:

- volume / Bragg, M ~ L^3: ratio ~ 1
- sheet, M ~ L^2: ratio ~ 1/4
- rod / finite line, M ~ L: ratio ~ 1/16
- 3D incoherent, I ~ 1/N: ratio ~ 1/8

The original scripts instead list, for "halving pixel size", Bragg ~ 1,
sheet/rod-like ~ 1/2, line-leakage ~ 1/4, and 3D diffuse ~ 1/8, with a separate
1/16 bar in the README. Those bars are also [X]. They assign different numbers
to the words "rod" and "line" than the M^2/N^2 accounting does. Mid-line ratios
near 0.055–0.057 sit near the M^2/N^2 rod/line bar (1/16 = 0.0625) and are
faster than the scripts' 1/2, 1/4, and 1/8 bars. This note uses "rod/line
reference" only in the hop's M ~ L sense, and does not claim that a real-space
rod was imaged.

### Mid-line drop versus implied two-size exponent [C ratios; [X] as a model]

Recomputed from [S3]:

- den-L plateau medians: 4.209777756016015e-06 (L=32, n=16) to
  2.3131609108000826e-07 (L=64, n=32), ratio 0.05494734033155176
- same-q mid-line (the 10 den-32 pixels with torus distance d0 to the origin
  in (0.2, 0.6)): median I64/I32 = 0.057373318522754325
- wraparound pair (1/32, 31/32, 0) and (31/32, 1/32, 0): ratio 0.7811193565051474
- off-diagonal den-L floor: 3.958177604352042e-08 to 5.591859377559668e-10,
  ratio 0.014127358437406604 (near 1/64 = 0.015625 = 1/N^2, since N grows by 8)
- streak/floor contrast of those medians: about 106.36 at L=32 to about 413.67
  at L=64

Two-size implied exponents, not a fitted law (only L=32 and L=64 exist here)
[X as a model; the ratios themselves are [C]]:

- plateau ratio 0.05494734033155176 implies I ~ L^{-4.186} at these two sizes
- mid-line median 0.057373318522754325 implies I ~ L^{-4.124}
- floor ratio 0.014127358437406604 implies I ~ L^{-6.146}, near L^{-6}

On the plateau, I32 · 32^4 ≈ 4.414 and I64 · 64^4 ≈ 3.881 (same order, not
equal). The mid-line drop is faster than 1/8 and near 1/16, which is compatible
with the rod/line reference above [X]. It is not Bragg and not 3D incoherent.
Absolute fade is not the streak disappearing into the unstructured floor: the
contrast rose.

### Distance to the nearest dyadic peak does not explain the ratio table [C]

Each of the 16 den-32 anti-diagonal pixels is exactly √2/32 ≈ 0.044194 from the
nearest den-≤16 point on the same line (one L=32 grid step). Their fade ratios
nonetheless vary with torus distance d0 to the origin, identifying (1,0,0) and
(0,1,0) with (0,0,0) as plot coordinates only:

| j/32 | d0 | I32 | I64 | I64/I32 |
|---|---:|---:|---:|---:|
| 1 and 31 | 0.044194 | 1.80166513084875e-05 | 1.40731550764634e-05 | 0.78111935650515 |
| 3 and 29 | 0.132583 | 5.40082229137335e-06 | 1.45790647265965e-06 | 0.26994157445031 |
| 5 and 27 | 0.220971 | 4.45286767855174e-06 | 5.10487018027108e-07 | 0.11464230578555 |
| 7 and 25 | 0.309359 | 4.23809023074351e-06 | 2.96163162918527e-07 | 0.06988127831025 |
| 9 and 23 | 0.397748 | 4.18146528128852e-06 | 2.39904539475205e-07 | 0.05737331852275 |
| 11 and 21 | 0.486136 | 4.17214540312748e-06 | 2.30861151948292e-07 | 0.05533391807851 |
| 13 and 19 | 0.574524 | 4.17614845322191e-06 | 2.35049309347516e-07 | 0.05628375331489 |
| 15 and 17 | 0.662913 | 4.18052876092329e-06 | 2.39522397861948e-07 | 0.05729476139498 |

In particular, (15/32, 17/32, 0) is the same grid step √2/32 from the strong
stable D1 peak at (1/2, 1/2, 0) (I64 = 0.9034208899704588, ratio 0.9999956433)
as (1/32, 31/32, 0) is from the plotted corner. Their fade ratios are 0.05729476139498
versus 0.78111935650515. A single "sinc leakage from whichever dyadic peak on the line
is nearest" mechanism is therefore already inconsistent with the ratio table
[C distances]. Independently, §8 and Lemma E falsify on-grid Dirichlet/sinc
leakage of those DFT-bin peaks as the source of the inter-peak intensity [F].
Once d0 ≳ 0.4 the ratio settles near 0.055–0.057; the slow ends remain a
different residual mechanism [X], not that kernel.

### Near-corner leakage is not the same as mid-line rod/line scaling [X]

The hop describes the slow axis-end tail as origin-peak leakage on the q-torus.
That is a coordinate-torus description. On-grid Dirichlet/sinc leakage from Γ
itself is [F] by the same kernel identity (q=0 is a DFT bin). Because D1
centroids have non-integer offsets, I(q) is not generally unit-periodic (§3),
so the plotted corners are not exact aliases of I(0). They still sit next to
the integer reciprocal vectors e_x and e_y, which Lemma D shows are themselves
strong (cos²(π/7) ≤ |F(e_a)|² ≤ 1). The slow ratio 0.78111935650515 is a [C]
profile fact and is not the mid-line 1/16 reference; its residual mechanism
after dropping the Dirichlet kernel stays [X].

No checkable analytic bound on the fade rate follows beyond the elementary
identities already in §6. Two box sizes cannot establish a power law, a hull
rod, or CH-V-020.

## 8. On-grid Dirichlet/sinc leakage is [F]; the ridge is not a sidelobe of (1/2,1/2,0)

This section absorbs the 7 Nov 2026 handoff
`/home/box/shared/theory-of-everything/handoff-from-qc-fade-dirichlet-f-2026-11-07.md`
and independently recomputes the plane-side claims from [S3]. SWE diagnostic files
[S9] and [S10] were opened read-only and were not executed or rewritten. H1/H2/H3
were not rerun. No FR30 geometry was regenerated. CH-V-020 stays [X]; the fade
reading stays [X]. Theorem F is not upgraded.

### Kernel identity and falsification [F]

The one-dimensional periodic Dirichlet kernel on integer bin offsets is
D_L(k) = 1 if k ≡ 0 (mod L), and D_L(k) = sin(πk)/(L sin(πk/L)) = 0 otherwise.
A 2D cube window is D_L(j_x) D_L(j_y). The unnormalized sinc(L Δq) with
Δq = m/L is likewise 0 for every integer m ≠ 0. This is Lemma E, not a
numerical fit.

The SWE script records `numerical_max_abs_off_bin = 0` by implementing that
integer-bin definition exactly (`1` on the diagonal, `0` off it). That stored
zero is tautological for the implementation; the falsification does not depend
on it. The analytic identity already predicts weight 0 at every other DFT bin,
so on-grid Dirichlet/sinc leakage of (1/2,1/2,0), of Γ, or of any other
on-grid dyadic tone cannot be the source of a nonzero intensity there.

Recomputed from [S3]: the L=64 D1 den-L anti-diagonal median is
2.3131609108000826e-07 (n=32), not 0. Therefore that kernel is [F] as an
explanation of the inter-peak intensity on these patches. The same identity
[F]s on-grid Dirichlet leakage as the source of the slower axis-end pixels,
which are also DFT bins.

### Neighborhood of (1/2,1/2,0) [C on patch]

Recomputed from [S3] at L=64, q_z=0:

| spoke | pixels | I | median |
|---|---|---:|---:|
| center | (32/64,32/64) | 0.9034208899704588 | — |
| anti-diagonal nearest | (31/64,33/64) and (33/64,31/64) | 2.309710531541855e-07 and 2.3097105315418556e-07 | 2.3097105315418553e-07 |
| axis nearest | (31/64,32/64), (33/64,32/64), (32/64,31/64), (32/64,33/64) | 6.072892819227677e-07, 6.006845599735418e-07, and the two transposes | 6.039869209481548e-07 |
| main-diagonal nearest | (31/64,31/64) and (33/64,33/64) | 9.075635959826908e-07 and 8.61725382976739e-07 | 8.846444894797149e-07 |

Anti/axis = 0.3824106866281161; anti/main = 0.2610891221286263. The
anti-diagonal neighbors are slightly below the full den-L anti median
2.3131609108000826e-07 (the axis-end pixels pull that median up) and equal
the mid-ridge median over odd j_x from 7 to 57, which is also
2.3097105315418553e-07. That is the opposite of a decaying sidelobe tail of
the bright central peak.

From the same plane, the main-diagonal den-L median is 6.502254437235467e-09
(about 36× weaker than the anti-diagonal) and the off-diagonal den-L control
median is 5.591859377559668e-10 (anti/control about 413.67). D0 is exactly 0
off the origin on the stored L=64 plane. D2 is a different object: its
anti/main den-L median ratio is about 1.275, not the D1 fading ridge.

### [111]-paired centroid shift [C on patch, QC stored sums, not rerun]

The chair missing-cube axis is [111], and the three coordinate-plane lines
(t,1−t,0), (t,0,1−t), and (0,t,1−t) are exactly the ⟨110⟩ directions
perpendicular to [111] [P, elementary from the geometry already in §2]. The
stored QC comparison [S11] (sha256
`f60ee1d8bc75846935625a96a2cc1846ac5e31ae6a6fd0613798e602873fda27`), which
regenerated FR30 decorations and was not rerun here, records:

- D1 den-L medians 2.3131609108005077e-07 on (t,1−t,0), 2.3131609108003926e-07
  on (t,0,1−t), and 2.3131609108004548e-07 on (0,t,1−t), with ratios to the
  first line of 1.0000000000000497 and 1.0000000000000229
- integer centers alone: about 7.130492863115249e-10 on all four tested lines
  (isotropic, control-floor)
- a uniform shift (+1,+1,+1)/14 matches those centers to maximum relative
  difference 1.7446446221799646e-11
- shuffling the orientation pairing (stored seed 1) gives anti-diagonal median
  3.3352946862147716e-06 and main-diagonal 2.2116587389588993e-06, with fade
  I64/I32 = 0.11940186697205887, near the 1/8 incoherent reference

Per-box medians from the same stored comparison, and from the P5 follow-up
[S14] (sha256 `1211be23ba72806d81ad225e768b3c2a8fb8fe75aa75513f5d5b142159857a63`),
show that each of those three lines is hot in only three of the seven occupied
octants and dark in the other four:

- (t,1−t,0) is hot when i_x = i_y: (0,0,0) = 5.514644191191145e-07,
  (0,0,64) = 5.331531444808518e-07, (64,64,0) = 5.331531444806414e-07;
  the four i_x ≠ i_y boxes sit at about 3.99385168245e-10
- (t,0,1−t) is hot when i_x = i_z; (0,t,1−t) is hot when i_y = i_z
- the origin box (0,0,0) is hot on all three lines (about 5.514644191191e-07)

Three hot boxes plus four dark boxes average to the reported
2.3131609108005077e-07 on (t,1−t,0).

Two further den-L lines in the plane q_x+q_y+q_z ∈ Z, not coordinate-plane
cuts, are elevated after the seven-box average [S14]: (t,t,1−2t) has L=64
median 2.5514235320384717e-07 and fade 0.03761559274552824; (t,1/2,1/2−t)
has L=64 median 3.535649823105723e-07 and fade 0.0490617941066172. They are
not a filled sheet in every octant: (t,t,1−2t) is hot mainly in (0,0,0) at
1.6298933660378922e-06 and about 1.1e-09 to 1.7e-09 in the other six, so that
average is essentially one box divided by seven. (t,1/2,1/2−t) is hot in
(0,0,0) at 1.2872900886084866e-06 and in the two boxes (0,64,0) and (64,0,64)
at about 3.75887787726e-07, which are boxes that also support a corresponding
coordinate-plane cut. Interpreting the q_z=0 anti-diagonal as a cut of a
[111]-related pattern supported on that plane, rather than as a uniform sheet
or an infinite-hull statement, stays [X].

So the leftover after dropping sinc sidelobes is the origin of the nearly flat
D1 den-L ridge as a paired centroid-shift pattern, not a new fade law.
Rod/line versus any remaining mechanism stays [X]. These stored off-plane,
per-box, and decoration sums are not independent recomputations from [S3]
alone: the landed qz=0 planes cannot see (t,0,1−t), (0,t,1−t), or the extra
plane lines.

## 9. Are the two extra den-L lines predicted by the centroid geometry?

This is the theoretical reading asked for after board #770. It uses only the
already-checked identity r = n − s/14 with s = G(1,1,1) ∈ {−1,+1}³ from §2
(eight offset vectors, not two species along [111]) and the phase factor
exp(−2πi q·s/14). No new diffraction sum was run here. Quasicrystal Materials'
controls reply [S15] (sha256
`e27b559c46abbf43727c82e446f59985274e9c123e4b07934604d7dd8ffcf2d8`) is folded
below as stored sums, not rerun. Existing P5 numbers [S14] remain the parent
intensities; [S15] reproduces them to about 10^{-21} and adds centers, uniform,
and shuffle decorations on the two extra lines.

Write q(t) = q0 + t d. Then q(t)·s = q0·s + t (d·s), so the orientation
phase is independent of t if and only if d·s = 0. All five lines below lie
in the plane q_x+q_y+q_z = 1 [P, elementary arithmetic]. Plane membership
alone does not predict a sheet: only the two classes s = ±(1,1,1) have
q·s = ±1 constant on that whole plane. The other six classes freeze only
on special lines. Interpreting the plane as a filled sheet or an infinite-hull
support stays [X].

### (t,1−t,0), (t,0,1−t), (0,t,1−t) — the three ⟨110⟩ lines [P, elementary]

These are q = (0,1,0)+t(1,−1,0), (0,0,1)+t(1,0,−1), and (0,0,1)+t(0,1,−1).
Each direction is a permutation of (±1,±1,0) and is perpendicular to [111].
The t-independence conditions are s_x=s_y, s_x=s_z, and s_y=s_z respectively.
Each freezes 4 of the 8 orientation classes. That is the §2 identity already
recorded for the q_z=0 anti-diagonal.

### (t,t,1−2t) is not a same-type companion [F]

This is q = (0,0,1)+t(1,1,−2), a ⟨112⟩ direction, still perpendicular to [111]
and still in the plane q·(1,1,1)=1. Now

    q·s = s_z + t(s_x + s_y − 2 s_z),

so d·s = 0 if and only if s = ±(1,1,1): only 2 of 8 classes, the same two that
are frozen on every line in that plane. The four-class freeze that distinguishes
each ⟨110⟩ line does not hold here. Therefore the claim that (t,t,1−2t) is
predicted alongside the three ⟨110⟩ lines as the same orientation-phase object
is [F]. Geometry does not forbid residual intensity from those two classes or
from the t-dependent A_s channels; that leftover is [X]. Equal brightness with
the ⟨110⟩ lines is not predicted.

Already-stored P5 sums [S14], not rerun and not a stored-plane check, are
consistent with a different object: L=64 median 2.5514235320384717e-07 and
fade 0.03761559274552824 after seven-box averaging, but hot mainly in the
(0,0,0) box (1.6298933660378922e-06) and about 1.1e-09 to 1.7e-09 in the
other six. Maps stay [C on patch]; the fade reading stays [X].

The later controls [S15], also not rerun here, reproduce that D1 median as
2.551423532038464e-07 and that fade as 0.0376155927455282 (absolute
differences about 7.4e-22 and 4.2e-17). Integer centers drop the same line
to 7.130492863128652e-10, matching the ⟨110⟩ centers floor 7.130492863115249e-10;
a uniform shift (+1,+1,+1)/14 matches those centers to maximum relative
difference 6.928028834155388e-12. Shuffling the orientation pairing (stored
seed 1) raises the L=64 median to 3.7103135557169143e-06 with fade
0.10383090888712813, near the shuffled anti-diagonal fade 0.11940186697205887
and the 1/8 incoherent reference. Per box, centers-kill is that same floor
even in the previously hot origin box (1.6298933660378765e-06 → about
7.13049286313e-10). So the residual elevation that geometry does not predict
as a four-class ⟨110⟩ companion is still pairing-dependent on this patch
[C on patch, QC stored, not rerun]. That does not upgrade the same-type
companion claim, which remains [F], and does not upgrade the fade reading.

### (t,1/2,1/2−t) is a parallel companion of (t,0,1−t) [P, elementary]

This is q = (0,1/2,1/2)+t(1,0,−1), the same ⟨110⟩ direction as (t,0,1−t),
translated in the plane to q_y=1/2. Now

    q·s = (s_y + s_z)/2 + t(s_x − s_z),

so the phase is t-independent if and only if s_x=s_z: the same 4 classes as
(t,0,1−t). In that sense it is predicted as a parallel companion [P,
elementary]. The cyclic midpoint parallels (1/2,t,1/2−t) and (t,1/2−t,1/2)
stand in the same relation to (0,t,1−t) and (t,1−t,0).

Equal intensity is not predicted [X]. The frozen-class weights differ:
exp(−2πi s_z/14) on (t,0,1−t) versus exp(−2πi (s_y+s_z)/28) on
(t,1/2,1/2−t), so F is a different linear combination of the A_s.

The integer channels themselves match on these two lines. Child translations
are t_0=(1,1,1) or t_u=4u, and G is a signed permutation, so by induction from
T_0=0 every T (and every n=T+s) is either even-even-even or odd-odd-odd
[P, elementary from the chair substitution in [S6]]. Box origins on the L=32
and L=64 partitions are integer and even, so for Δq=(0,1/2,−1/2)

    exp(2πi (q_half − q_coord)·(n−lo)) = exp(πi ((n_y−n_z)−(lo_y−lo_z))) = 1.

Thus A_s(t,1/2,1/2−t)=A_s(t,0,1−t) on these boxes [P, elementary]. The
intensities can still differ through the orientation weights above.

Already-stored P5 sums [S14] are consistent with that split: the line is hot
in the same three octants as (t,0,1−t), namely (0,0,0), (0,64,0), and
(64,0,64), with L=64 seven-box median 3.535649823105723e-07 and fade
0.0490617941066172, not equal to the ⟨110⟩ median 2.3131609108005077e-07.
Those numbers remain [C on patch, QC stored, not rerun].

Controls [S15] reproduce the D1 median as 3.5356498231057164e-07 and the fade
as 0.04906179410661706. Integer centers drop it to 7.130492863115519e-10;
a uniform shift matches those centers to maximum relative difference
2.777896384793342e-11. Shuffling (seed 1) raises the L=64 median to
3.945942281777703e-06 with fade 0.1160913692924512. Per box it stays hot
on D1 when i_x=i_z — (0,0,0)=1.2872900886084985e-06, (0,64,0)=3.75887787725722e-07,
(64,0,64)=3.758877877258877e-07 — and centers-kill flattens those boxes too.
The pairing dependence matches (t,0,1−t), as the parallel-companion identity
suggests; the unequal medians remain consistent with the different frozen-class
weights. Equal intensity and the fade reading stay [X].

QC independently checked this section against [S15] [S17], opening the
intermediate note sha256 `4db997ff8f31927887a07898878251c961bd4e1a3c128c9da23f629cfed39c88`.
They reported no numeric correction to the [S15] transcription and independently
enumerated the eight orientation classes, recovering the same freeze counts
(2 of 8 on (t,t,1−2t); 4 of 8 with s_x=s_z on both (t,1/2,1/2−t) and
(t,0,1−t)). Recomputed from the stored [S15] seven-box L=64 medians, the ratio
of (t,1/2,1/2−t) = 3.5356498231057164e-07 to (t,0,1−t) = 2.3131609108003926e-07
is 1.5284928111128775. The medians are unequal [C on patch], which does not
contradict the earlier prediction that equal intensity was not required.
QC did not sum the cyclic midpoint parallels (1/2,t,1/2−t) and (t,1/2−t,1/2).

### What the official stored planes can show

The landed q_z=0 planes [S3] meet (t,t,1−2t) and (t,1/2,1/2−t) only at the
single point t=1/2, which is the stable D1 peak (1/2,1/2,0). They cannot
supply a den-L median for either extra line. QC's controls [S15] confirm
that plane-negative and re-read the stored intersection intensities
I64=0.9034208899704588 and I32=0.9034248259569937, matching the values
already recomputed from [S3] in §3. The off-plane ridges were therefore
controlled by regenerating FR30 decorations (same generator and shuffle seed 1
as the earlier pairing hunt), not by an independent plane reread. After
wrapping into the unit cube, some den-L sample points on the extra lines are
represented with q_x+q_y+q_z = 2 rather than 1; that is the same torus
condition q·(1,1,1) ∈ ℤ, not a second plane. No measured-crystal comparison
is made.

## 10. Leftover and scope lock

The next computational leftover remains waiting on the existing B3 FR30 ell4 chain to finish/score under its frozen specification. No new programme, open-web hunt, measured-crystal comparison, R3, G8, new L7, Regge or CDT was started. B3 processes were neither inspected through execution hooks nor signalled, stopped, restarted, or duplicated. H1/H2/H3 were not rerun. Section 8 folds the Dirichlet [F] and the stored [111] pairing. Section 9 is the theoretical reading of the two extra den-L lines, folds QC's P5 controls [S15], and records QC's independent check of that reading [S17] (they opened intermediate sha256 `4db997ff…`; no numeric correction). Only this note and the leftovers pointer were written; no protected QC file or frozen preregistration was edited. No commit, push, Page, external contact, or Lean formalization. B3 FR30 was left running and was not scored.

## Opened primary local sources / SHA256

Source hashes refer to the actual files opened for this note; README reliance is only its Turn 2/3 Chair44 sections. Installed numpy was used only to read the landed npz and compute descriptive statistics; neither source generator nor diffraction script was executed. All Python invocations used `python3 -I`.

- **S1** `/home/box/shared/quasicrystal-materials/diffraction/scripts/chair44_L64_streak.py`
  `174ac8b9bcc03ed6f56fd32c77e84eaa39a69e923a592be4f36f905eacf3e9cf`
- **S2** `/home/box/shared/quasicrystal-materials/diffraction/tables/chair44_L64_qz0_streak.json`
  `705d9d2d84c8a5a304e797e1bf961d95d5fc4433a2dc2bc8543a19fe7995d729`
- **S3** `/home/box/shared/quasicrystal-materials/diffraction/tables/chair44_L64_qz0_planes.npz`
  `46f94f916b89fad0f90e42dc0bc5efebde51a1c655f2639b91bfe6c3d8e4f064`
- **S4** `/home/box/shared/quasicrystal-materials/diffraction/README.md`
  `17f3bdea2101ce76fae7374fada17d182e5fbca02e0e4de331e7d1a241bb6eb0`
- **S5** `/home/box/shared/quasicrystal-materials/diffraction/scripts/chair44_diffraction.py`
  `01c356b3ccb0ac3d66f0eb259cd7fa0efdf707a8791a8329e9eb9617590438ef`
- **S6** `/workspace/qis-eth/mirror/toe/src/chair.py` (read-only)
  `0dca434161f04a63ea0e3a251276b0d3a93bad8663c8f90b79cae40b7d118f7e`
- **S7** `/home/box/shared/quasicrystal-materials/diffraction/tables/chair44_L64.json` (read-only existing H3 record)
  `b7997ed7711d9d46445b55ae7f8d4cf87062ef646d295bb0da6dab4826e900f9`

- **S8** `/home/box/shared/research-publishing/chair44-antidiagonal-fade-mechanism-hop-2026-11-07.md`
  `fa2bb6e3b9a99ce64efb0d216ac871b869b5ea2ed6bb65733be011426ec0a355`
  (numbers above were recomputed from [S2]/[S3], not copied as primary evidence)

- **S9** `/home/box/shared/quasicrystal-materials/diffraction/tables/chair44_L64_qz0_fade_mechanism.json`
  `32f7ec3bf6c4d4827388e84e6b2e3e5a183290588b61cd0a15f70a8e7968a27f`
- **S10** `/home/box/shared/quasicrystal-materials/diffraction/scripts/chair44_L64_fade_mechanism.py`
  `c843445dc8fa37ca9ad4283d403c0e45e2e8f6d3136ea99431183a3da646adc3`
  (read, not executed)
- **S11** `/home/box/shared/quasicrystal-materials/diffraction/tables/chair44_L64_streak_mechanism.json`
  `f60ee1d8bc75846935625a96a2cc1846ac5e31ae6a6fd0613798e602873fda27`
  (opened; decoration and off-plane sums not rerun)
- **S12** `/home/box/shared/quasicrystal-materials/diffraction/chair44-streak-mechanism-2026-11-07.md`
  `c87eee2df56ce9a3e81790572bc025896c39bba951eaaf980940303709e01b03`
  (hash of the file opened for this addendum; earlier copies were `d07b1daf…` and a handoff listed `a81c5a3a…`)
- **S14** `/home/box/shared/quasicrystal-materials/diffraction/tables/chair44_L64_streak_mechanism_p5_sheet.json`
  `1211be23ba72806d81ad225e768b3c2a8fb8fe75aa75513f5d5b142159857a63`
  (opened; off-plane sheet probes not rerun)
- **S15** `/home/box/shared/quasicrystal-materials/diffraction/tables/chair44_L64_streak_mechanism_p5_controls.json`
  `e27b559c46abbf43727c82e446f59985274e9c123e4b07934604d7dd8ffcf2d8`
  (opened; decoration controls and plane-negative not rerun)
- **S16** `/home/box/shared/quasicrystal-materials/diffraction/chair44-p5-extra-lines-controls-2026-11-07.md`
  `62a9f656a91a2156215e310fbdd2a6b6973bca4da6d37fcc27ae65f36180b202`
  (opened as QC's writeup of [S15]; numbers above are from the JSON)
- **S17** `/home/box/shared/quasicrystal-materials/diffraction/chair44-p5-controls-vs-toe-s9-2026-11-07.md`
  `c37229ac959f18f59ff5c8145f3c02ce8a85e28b3df661c64df7c5d876f05790`
  (opened; QC's independent check of §9 against [S15]; ratio above recomputed from the JSON)
- **S13** `/home/box/shared/theory-of-everything/handoff-from-qc-fade-dirichlet-f-2026-11-07.md`

No required source failed to open. No outside paper is cited as newly opened. No protected QC file was edited.


## [S18] Frozen two-point L-fit on stored D1 q_z=0 planes

Internal unification-programme leftover · 2026-11-07 10:35:23 PST. QC owns the computation
(their note identifies board #836; their handoff names #843, not independently
read here). No scorecard changes. Fade reading and CH-V-020 stay [X].

### Opened primary files / SHA256

- Frozen two-point prereg: `/home/box/shared/quasicrystal-materials/diffraction/prereg/2026-11-07_chair44_twopoint_lfit_prereg_v1.md`
  `619ac8fcbfab21b6b3633e74401ecd6b7d0603228d0388fb16741418b0259d66`
- QC writeup: `/home/box/shared/quasicrystal-materials/diffraction/chair44-twopoint-lfit-2026-11-07.md`
  `146f22c771c847180208b038d18406c092ac1b687f9fa6f2310e677e937b6450`
- Two-point JSON: `/home/box/shared/quasicrystal-materials/diffraction/tables/chair44_L64_twopoint_lfit.json`
  `f21fcff3350213ad7fcdbf728199e1302b9db45ce5b3cea87bad92ba7b085280`
- Stored planes [S3], opened read-only with `numpy.load(..., allow_pickle=False)`:
  `46f94f916b89fad0f90e42dc0bc5efebde51a1c655f2639b91bfe6c3d8e4f064`
- Read-only pairing-control table [S11], object `P4_fade_anti_denL`:
  `f60ee1d8bc75846935625a96a2cc1846ac5e31ae6a6fd0613798e602873fda27`

All supplied source hashes match. The prereg and writeup explicitly specify
stored D1 planes only, no FR30 regeneration and no L=128; the JSON names those
same hashed inputs and the already-stored pairing table. I independently
reproduced the plane summaries, full-plane mean and seeded full-plane shuffle
from those planes, and recomputed each table ratio/exponent. No mechanism
script was run, no plane was regenerated or written, and no L=128 was used.
The prereg discloses prior inspection: this is not a new blinded hypothesis
score. Hash agreement checks the files, not independent freeze chronology.

### Verified two-point arithmetic [C on patch]

For each positive ratio r = I64/I32, alpha = log(r)/log(2). For the locked
same-q series, r is instead the median of individual same-q ratios, not a
ratio of intensity medians. Values below are descriptive floating-point
computations, not certified interval bounds or observations of a crystal.

| Series | r | alpha |
|---|---:|---:|
| stored-plane den-L plateau | 0.05494734033155176 | -4.185806539052345 |
| locked same-q mid-line median | 0.06362729841650083 | -3.974210322999809 |
| axis end (1/32,31/32) | 0.7811193565051474 | -0.35638508316346085 |
| axis end (31/32,1/32) | 0.7811193565051475 | -0.3563850831634606 |
| in-memory whole-plane mean | 0.24981480890202085 | -2.001069093136654 |
| in-memory shuffled-plane plateau | 0.08480766818059603 | -3.559661472793319 |
| read-only pairing D1 | 0.054947340331560644 | -4.185806539052112 |
| read-only pairing D1_centers | 0.011364794633627558 | -6.459284575458298 |
| read-only pairing D1_shuffled | 0.11940186697205887 | -3.066102700074652 |
| read-only pairing D1_uniform | 0.011364794633651386 | -6.459284575455273 |

**Two distinct summaries [C on patch].** The den-L plateau compares changing
pixel sets (16 at L32; 32 at L64): medians 4.209777756016015e-06 and
2.3131609108000826e-07. The locked same-q window uses
`min(jx,32-jx,abs(jx-16))/32` in [0.2,0.6], selecting only jx = 7,9,23,25
(and jy = 32-jx). Its median of four ratios is 0.06362729841650083.
It is not the earlier ten-pixel distance-window median 0.057373318522754325
in §7, nor the definition of the all-sixteen-pixel summary in §4, even though
the latter has the same numerical median. The QC note explicitly distinguishes
the previously posted 0.057373 value from this locked median. The two axis-end
points remain separate. No historical section is rewritten by this addendum.

**Controls remain different objects [C on patch].** The plane mean uses all
finite non-origin pixels (1023 at L32; 4095 at L64). The in-memory shuffled
plateau permutes those full-plane pixels using `default_rng(1)`, L32 then L64
with the same continuing generator, and then re-extracts each den-L line.
Neither is the structured-line subset, nor the real-space D1_shuffled
orientation-decoration control in [S11]. D1_centers and D1_uniform in the
read-only pairing table describe the residual isotropic floor, not the fade
of a surviving ridge. Those stored decoration intensities were read, not
regenerated.

**Comparison / pairing picture [C on patch].** Both structured summaries have
r smaller than the plane mean and the shuffled-plane plateau, and smaller
than the read-only D1_shuffled ratio 0.11940186697205887. Thus the structured
anti-diagonal fades faster than these controls on this two-point patch. The
plateau and locked median are each nearest -4 among the prereg's reference
marks {0,-2,-3,-4}; real-space D1_shuffled is nearest -3. These are descriptive
nearest-mark comparisons, not derived powers or scored hypotheses. Compatibility
with the existing [111] pairing picture is [C on patch] only, not a hull law
or analytic fade bound. The arithmetic agrees with QC's message and files;
no numerical correction is needed.

**Not claimed / locks.** No fade upgrade (stays [X]); no CH-V-020 upgrade
(stays [X]); no I ~ L^{-4} law or prediction; no hull lemma or filled-sheet
claim; no Theorem F or unique-ergodicity change; no upgrade of TOE-PROOF-F,
CH-VA-019, or [S]. On-grid Dirichlet/sinc leakage remains [F] by Lemma E,
not reopened by this fit. The (t,t,1-2t) same-type companion claim stays [F];
(t,1/2,1/2-t) stays a parallel companion [P, elementary], with equal intensity
unpredicted [X]. No L=128, no measured-crystal comparison, no further open-web
intensity hunt, no B3 score or scorer execution, and no protected-artifact edit.

### Theory reply to Projects Manager #844 item 1: does either bound predict -4 versus -2?

2026-11-07 10:38:44 PST. Full board #844 read using the sanctioned full-path CLI; item 1
asks whether the finite-N integer-peak bound or D1 [111] pairing predicts
anti-diagonal alpha near -4 versus plane-mean alpha near -2. Item 2 is not
acted on here: no B3 files, processes or scores were inspected or changed.
PM handoff opened: `/home/box/shared/theory-of-everything/handoff-from-kg-qcm-twopoint-lfit-2026-11-07.md`,
sha256 `c53c542712b58edaf4bb0d60a4da17602e09d44c9a944fc3c0cdcde004ebdaa5`.

**Headline [X prediction; P conditional bound; C on patch accounting].**
Neither the finite-N peak bound nor the [111] pairing currently predicts
alpha=-4 on the anti-diagonal versus alpha=-2 on the plane mean. A persistent
O(1) non-origin peak implies a whole-plane mean Omega(L^-2) [P, elementary,
conditional on uniform persistence]. The stored peak supplies that lower
bound at the two tested sizes [C on patch input]; two sizes alone do not
prove persistence at all larger L. The observed plane-mean alpha near -2 is
[C on patch] pixel-count accounting, not a sheet theorem. Pairing selects
orientation-phase lines [P, elementary] and the controls show pairing-dependent
residuals [C on patch], but a prediction of the specific exponent -4 stays [X].

**Finite-N positivity and the peak/mean lower bound [P, elementary].**
For N_B >= 1, each summand in F_B has modulus one; the triangle inequality
gives |F_B(q)| <= 1. Squaring and averaging over the nonempty boxes proves
0 <= I(q) <= 1. At q=0 each summand equals one, hence I(0)=1 (Lemma A).
For the non-origin grid G_L with n_L pixels, set

    S_L = sum_{q in G_L} I_L(q),    Ibar_L = S_L/n_L.

If some q_L in G_L has I_L(q_L) >= c > 0, nonnegativity gives S_L >= c and
Ibar_L >= c/n_L. For a full L by L plane, n_L=L^2-1; therefore, if the same
c works for a family of arbitrarily large L, Ibar_L >= c/(L^2-1) >= c/L^2.
This is the conditional Omega(L^-2) statement. It is a lower bound only:
it supplies no matching upper bound and does not prescribe a two-point ratio.
The persistent-peak hypothesis for an unbounded family has not been proved
by this two-size computation. No unconditional asymptotic upgrade is made.

**Peak input and plane-sum accounting [C on patch].**
Rereading the unchanged [S3] planes gives I32(1/2,1/2,0)=0.9034248259569937
and I64=0.9034208899704588, ratio 0.9999956432605992. Thus c=0.90 works on
these two stored planes, and the elementary bound applies separately at
each size. The JSON gives n32=1023 and n64=4095. Independently recomputed:

    n32/n64 = 1023/4095 = 0.24981684981684982
    Ibar64/Ibar32 = 0.24981480890202085
    S32 = 2.398651087608836
    S64 = 2.3986314914824023
    S64/S32 = (Ibar64/Ibar32)*(4095/1023) = 0.9999918303555967.

The exact accounting identity is Ibar64/Ibar32=(S64/S32)*(1023/4095).
The displayed floating-point values show nearly L-independent excluded-origin
plane-sum on this patch; alpha=-2.001069093136654 is almost entirely the
pixel-count factor. This is not a Parseval theorem and does not prove a
sheet or hull law [X]. In particular the lower bound does not force a ratio
of exactly 1023/4095. It puts no required mass on the den-L anti-diagonal:
a single persistent peak can meet the whole-plane bound while all other
pixels are zero. Here the central peak has reduced denominator 2, not den L,
so it is outside that plateau mask at L32 and L64.

**Integer peaks and leakage do not supply an exponent.**
Lemma D proves cos^2(pi/7) <= |F(e_a)|^2 <= 1 from the centroid phase
identity; its inequalities contain no L-scaling law. Moreover e_a itself
is not a non-origin pixel in the displayed half-open plane. Lemma E already
falsifies on-grid Dirichlet/sinc leakage of (1/2,1/2,0), Gamma or any on-grid
dyadic tone onto other DFT bins [F as an explanation of the nonzero den-L
intensity]. Consequently the strong peak cannot produce the den-L ridge
through that kernel, and its bound cannot predict the ridge exponent.

**Pairing selects lines, not an L-power [P selection; C residuals; X power].**
For r=n-s/14 with s in {-1,+1}^3 and q(t)=q0+t d, the orientation factor is
exp(-2 pi i (q0 dot s+t d dot s)/14), independent of t exactly when d dot s=0.
On d=(1,-1,0), this means s_x=s_y: two choices for their common sign and
two choices for s_z, hence 4 of 8 classes. Coordinate permutations prove
the same count on the other two <110> lines. For d=(1,1,-2), the condition
s_x+s_y=2s_z forces all three signs equal: only 2 of 8. The same-type
companion claim for (t,t,1-2t) remains [F]. The parallel companion
(t,1/2,1/2-t) has d=(1,0,-1) and freezes the same four classes s_x=s_z
[P, elementary], without an equal-intensity prediction.

The identity F_B(q)=sum_s exp(-2 pi i q dot s/14) A_{B,s}(q) fixes these
phase conditions, not the L-dependence of the channel sums or cross terms.
Writing A_{B,s}=U_{B,s}/N_B makes clear that, even if N_B grows like L^3,
intensity L^-4 would require the relevant unnormalized total amplitude to
scale like L (in a way compatible with the box average), versus L^2 for
L^-2. Neither scaling follows from d dot s=0 or the finite-N bound. No
surface/volume story is promoted to [P] or [E]. A prediction of -4 versus
-2 remains [X].

[C on patch] Both structured r values (0.05494734033155176 plateau and
0.06362729841650083 locked same-q median) are below the in-memory shuffled
plateau 0.08480766818059603 and the read-only real-space D1_shuffled
0.11940186697205887. They also lie below the plane-mean ratio. Pairing-dependent
interference can suppress residuals relative to the shuffled baselines;
these comparisons and the prior P5/[S11]/[S15] controls are compatible with
faster structured fade on this patch, not a derivation of its exponent.
PM #844's shuffle alpha about -3 is D1_shuffled, -3.066102700074652. It is
not the in-memory shuffled-plane plateau, -3.559661472793319, which the
JSON itself marks nearest -4. D1_shuffled being near 1/8=0.125 is [C on patch]
compatibility with the disclosed incoherent ruler, not proof of complete
incoherence and not an inference of the structured anti-diagonal law.

The opened JSON's `reference_ruler_L_doubling` names Bragg alpha=0,
sheet=-2, diffuse_3d=-3 and rod_or_finite_line=-4. These are QC's disclosed
comparison marks, not theorems about this hull. Board #764's rod/line reading
is not upgraded to [P] by nearest-mark rounding.

**Scope unchanged.** Fade reading [X]; CH-V-020 [X]; sheet/hull [X];
Theorem F and unique ergodicity remain unverified, with no upgrade of
TOE-PROOF-F, CH-VA-019 or [S]. Dirichlet/sinc stays [F]. No L=128, ambient
d/I hunt, measured-crystal comparison, pending claims.csv insertion, v0.6
edit, new L7 or B3 result language. This answers #844 item 1 only.

## [S19] Lemma C exponential identity formalized [P, Lean]

lean-lab #845. Independently hashed Lean and the result note; I read the
theorem file rather than treating the handoff as primary evidence.

- File: `/workspace/lean-lab-845-orientation-phase/LeanLab/Toe/OrientationPhase.lean`
  sha256 `b41f2efa66339d90a1c0cb649093881b54b5df52150e1e71dfb0d9a395014e72`
- Result note: `/home/box/shared/lean-lab/chair44-lemma-c-orientation-phase-2026-11-07.md`
  sha256 `e97a7fb8a2b4227b12f580d2d5c4f0165a44b3763587da9b4de98207b27c1746`
- Branch `req/845-orientation-phase`, commit `2bd471e7a2a7f70c57fdd840304b4c610038c1da` (not pushed;
  shared lean-lab checkout left on `fix/axiom-check-source-freshness`)
- Theorem: `LeanLab.Toe.OrientationPhase.orientationPhase_exp_rewrite`

For all real t, x, y the encoded statement is

    exp(2 π i [t x + (1−t) y]) = exp(2 π i t (x−y)) * exp(2 π i y).

That matches the displayed identity in section 6 Lemma C. LPL hashed this
path as `0f2ae32f861b6c5f46940a52d42e4f8618f55c537fd275d06cdc8e8241ec942d`
when they formalized it (an earlier PM snapshot `0e9e6d71…` is no longer
on disk). Later [S18] appends moved the live file hash; section 6 Lemma C
was not rewritten, and the displayed identity is unchanged.

**[P, Lean] covers only that encoded exponential identity.** The two
follow-on sentences in Lemma C — that the last factor cannot be dropped
for D1 centroid y, and that the orientation-channel identity of §2 follows
for r = n − s/14 with n integral and s in {−1,+1}³ — were not formalized
in this hop. Section 6 Lemmas A, B, D, and E were not formalized. I did
not rebuild the worktree; LPL reported `lake build` success, axiom_check
OK (only `propext` / `Classical.choice` / `Quot.sound`), and no `sorry`.
The file I opened contains no `sorry`. `ETHTransfer.lean` and frozen files
were reported untouched.

This does not bound a fade rate, identify a ridge, or upgrade Theorem F.
CH-V-020 stays [X]. Other note labels that say [P, elementary] are not
Lean [P] until a file builds.

## [S20] QC independent check of [S18] accounting

QC fold `/home/box/shared/quasicrystal-materials/diffraction/chair44-twopoint-lfit-vs-toe-s18-2026-11-07.md`
sha256 `51fd3d7c2cd2020540dc85b2ad2effe7b678eba9dff107a58e6c63af5d766329`
(independently hashed; I opened the file). They first opened this note at
`6bfbd761795c7bfe19e38ba6e89d3238723b51ca83053605de3139b13cf680fd`, then
re-read live `bfac0cd1b633f8994cd48a2fcc2d873ea0c6122d0cd2966f98f3502bd05e848c`.
Same headline; no numerical correction to the L-fit table. They independently
recomputed n=1023 and 4095, S32=2.398651087608836, S64=2.3986314914824023,
S64/S32=0.9999918303555966 (this note recorded 0.9999918303555967; last-digit
float display only), and r_unif=0.24981480890202085 versus
1023/4095=0.24981684981684982 [C on patch]. They withdrew the computational
note's “fades like a sheet” wording without rewriting hashed file
`146f22c771c847180208b038d18406c092ac1b687f9fa6f2310e677e937b6450`. They
later agreed the [P, elementary] bound is Ī_L ≥ c/n_L and that Ω(L^{-2})
stays conditional on persistence at arbitrarily large L. Fade and
CH-V-020 stay [X]. They did not edit this note, v0.6, or claims.csv.

## [S21] Peak vs Dirichlet/sinc split [C on patch confirmation of Lemma E]

QC board #891 / #898, handed for a theory-side fold. Frozen prereg hashed
before the run (not edited afterward):
`/home/box/shared/quasicrystal-materials/diffraction/prereg/2026-11-07_chair44_peak_sinc_split_prereg_v1.md`
sha256 `79c29bc1fe253777248fa9aff402c874c9df97df9569c57cb9598d2d6f7947c7`.
Note `chair44-peak-sinc-split-2026-11-07.md` sha256
`e685989d506c44e36637454999952664c0a76ce2f2e210c02e686a48a4617cdd`.
JSON `tables/chair44_L64_peak_sinc_split.json` sha256
`95133caa532f5782f71d1d82ab9e020b5dcba6f8f64e1847f8420ffbac8bc9de`.
Script sha256 `7e46f1225c3b8fbbcadb9871f74f69d83e98ee37f9783982e829c7559967d8c9`.
Planes unchanged `46f94f916b89fad0f90e42dc0bc5efebde51a1c655f2639b91bfe6c3d8e4f064`.
I read those files and the JSON; I did not rerun the script or regenerate
planes.

**Headline.** This split does not change any scorecard label. It packages
two already-known parts on the stored D1 anti-diagonal and reports how
each scales between L=32 and L=64. The on-grid peak stays put. The
Dirichlet/sinc model of leakage from Γ and from (1/2,1/2,0) is exactly 0
at every other DFT bin, so it cannot supply the leftover intensity.
Residual equals observed because the subtracted model is identically
zero on those bins, not because a nonzero tail was removed and a rod
remained. Dirichlet/sinc stays [F]. The fade reading, CH-V-020,
sheet/hull, and −4 versus −2 as a prediction stay [X]. Two sizes are
not a power law. Theorem F is not upgraded.

**Peak part [C on patch].** Independently recomputed:
I32(1/2,1/2,0)=0.9034248259569937, I64=0.9034208899704588,
r=0.9999956432605992, α=log2(r)=−6.285460020047483e-06, nearest 0.
Origin I(0,0)=1 at both sizes. This is the same stored peak used in
[S18]; two sizes still do not prove persistence at arbitrarily large L.

**Model leakage [C on patch; exact zero by Lemma E].** QC define

    I_sinc = I_peak |D_L(jx − L/2) D_L(jy − L/2)|²
           + I_origin |D_L(jx) D_L(jy)|²

with D_L(k)=1 if k ≡ 0 (mod L), else sin(πk)/(L sin(πk/L)). On
inter-peak anti-diagonal pixels (n=30 at L=32 and n=62 at L=64; den-L
subset n=16 and 32) the JSON records I_sinc exact-indicator median 0.0
at both sizes, max absolute exact I_sinc 0.0, and r_sinc undefined
(0/0). That is Lemma E on this mask: a cube-windowed on-grid tone has
weight 0 at every other integer bin. Independently, the float64 1D
ratio-form max_{k=1..L−1} |sin(πk)/(L sin(πk/L))| is
2.3430591869721456e-15 at both L=32 and L=64, matching the JSON field
`max_abs_ratio_weight_off_peak`. The JSON's max I_sinc from the
ratio-form on inter-peak pixels is about 8.4244e-63, many orders below
the observed den-L medians (4.209777756016015e-06 and
2.3131609108000826e-07).

**Residual [C on patch; identical to observed].** Residual den-L
medians equal the observed den-L plateau medians, hence the same
r=0.05494734033155176 and α=−4.185806539052345, nearest −4. The locked
four-pixel mid-line residual median is r=0.06362729841650083
(α=−3.974210322999809), matching the #843/#S18 window; the ten-pixel
§7 median 0.057373318522754325 is still a different object. Axis-end
residual (1/32,31/32) remains r=0.7811193565051474. These equalities
are the expected consequence of I_sinc ≡ 0 off-peak. They do not
isolate a new spectral component.

**What this does not show.** Subtracting a kernel that is exactly zero
leaves the observed ridge untouched, so the split does not explain why
that leftover has α near −4, does not derive pairing as an L-scaling
law, and does not predict −4 versus −2. Structured residual still
fades faster than the plane mean (r=0.24981480890202085, α≈−2.001) and
faster than the in-memory shuffled den-L plateau (r=0.08480766818059603,
α≈−3.560) on this patch [C on patch]; that remains compatibility, not
an exponent derivation. No L=128; no measured-crystal comparison; no
v0.6 or claims.csv edit.

## [S22] Lean Lemma E window-kernel identities [P, Lean]

Lean Proof Lab note
`/home/box/shared/lean-lab/chair44-lemma-e-window-kernel-2026-11-07.md`
sha256 `4be77911a86b94628e97b40d164d654d1796517e8b891c808118c9d8a770c0f5`.
File `/workspace/lean-lab-845-orientation-phase/LeanLab/Toe/WindowKernel.lean`
sha256 `12b475aa8f89ea8213c407e83bfbed7a4eabd7c3f23bf0ca0002b74847e6a0c2`,
commit `0e23973e84cb8c0e04c04830dd95f81eac3a2590` on `req/lemma-e-window-kernel`
(not pushed). They formalized against this note at pin
`6bf8b9f243da57e47d7b3da35383ce21acef1f51f21c9b3ad1b764b466cf09ce`
(this append moves the live hash; §6 Lemma E and [S21] were not rewritten).
`OrientationPhase.lean` remains
`b41f2efa66339d90a1c0cb649093881b54b5df52150e1e71dfb0d9a395014e72`.
KG handoff
`/home/box/shared/theory-of-everything/handoff-from-kg-lean-lemma-e-2026-11-07.md`
sha256 `2ba220aa70a7fbd1046e57036f7dd1765c2f33eba638c023568e0a5f45388c6e`.

I independently hashed those files, read every theorem, found no `sorry` or
`native_decide`, and typechecked with `lake env lean LeanLab/Toe/WindowKernel.lean`
(exit 0). I did not re-run the full `lake build` or `scripts/axiom_check.sh`;
those logs hash as LPL recorded:
`/workspace/lemma-e-lake-build.log` sha256
`e5f22193f34088bb6b945d103d63d8712a634a7b1f7327aadd7d7840c37ea9be`,
`/workspace/lemma-e-axiom-check.log` sha256
`6c84c5b3384cdb0772788b23340df3f7057bc653106d661fa4130d27eaa1891b`.

[P, Lean] covers only the encoded identities in `LeanLab.Toe.WindowKernel`:

1. `windowPhase_eq_one_iff` — supporting: exp(2πi k/L)=1 iff L divides k.
2. `windowKernel_geom_sum` — the displayed geometric-sum identity of §6 Lemma E.
3. `windowKernel_sin_eq_zero_iff` — sin(πk/L)=0 iff L divides k (the "since" clause).
4. `windowKernel_denominator_ne_zero` — supporting nonzero denominator.
5. `windowKernel_sinc` — the displayed sinc identity of §6 Lemma E.
6. `dirichletWeight_off_bin` — D_L(k)=0 off-bin, with D_L as in [S21].
7. `dirichletWeight_product_off_bin` — the 2D product of those weights is 0
   unless both offsets are peak bins.

This is a DFT / window-kernel identity, not a fade inequality. It does not
cover Lemma E's English three-dimensional cube-window sentence (no 3D product
corollary was encoded), the float ~2.4e-15 check (that stays [C on patch]),
measured intensities, or an infinite hull. Dirichlet/sinc as an explanation
of the observed inter-peak intensity stays [F]. Maps and the [S21] split
stay [C on patch]. Fade, CH-V-020, sheet/hull, and −4 versus −2 stay [X].
Theorem F is not upgraded. Lemmas A, B, and D were not started from this
hop, nor were Lemma C's follow-on remarks.
