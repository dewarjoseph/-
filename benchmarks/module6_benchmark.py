"""
module6_benchmark.py
================================================================================
Module 6 Controlled Benchmark:
  1. Bispectrum Convergence chi_b(R) for R = 6, 8, 10, 12, 14, 16 alongside the
     Exact Analytical Weyl / Katz-Duneau Limit chi_b(infinity) in E_perp.
  2. Dynamical Graph-Laplacian Circular-Polarization Wave Probe D_lap(R) alongside
     its Exact Clipped-Polyhedron Limit D_lap(infinity) on W_b intersect (W_b - d_perp):
     Proving translation invariance, exact vanishing on achiral window (a), exact sign
     inversion on mirror window (-b), and linear proportionality to the bispectrum
     pseudoscalar across both radius R = 6..16 and chiral seed deformation s in [-1.5, +1.5].
================================================================================
"""

import itertools
import time
import numpy as np
from scipy.spatial import ConvexHull, HalfspaceIntersection

# ==============================================================================
# 1. 6D -> 3D ICOSAHEDRAL CUT-AND-PROJECT SUBSTRATE & SYMMETRY GROUPS
# ==============================================================================
TAU = (1.0 + np.sqrt(5.0)) / 2.0
V_PAR = np.array(
    [[1, TAU, 0], [-1, TAU, 0], [0, 1, TAU], [0, -1, TAU], [TAU, 0, 1], [TAU, 0, -1]],
    dtype=float,
).T
V_PERP = np.array(
    [[-TAU, 1, 0], [TAU, 1, 0], [0, -TAU, 1], [0, TAU, 1], [1, 0, -TAU], [1, 0, TAU]],
    dtype=float,
).T
P_PAR = V_PAR / np.sqrt(2.0 * (1.0 + TAU ** 2))
P_PERP = V_PERP / np.sqrt(2.0 * (1.0 + TAU ** 2))
PI_PAR = P_PAR.T @ P_PAR

IH_6D, I_6D = [], []
for perm in itertools.permutations(range(6)):
    Pm = np.zeros((6, 6))
    Pm[np.arange(6), perm] = 1.0
    for signs in itertools.product((-1.0, 1.0), repeat=6):
        g = Pm * np.array(signs)[:, None]
        if np.allclose(g @ PI_PAR, PI_PAR @ g, atol=1e-9):
            IH_6D.append(g)
            if np.linalg.det(P_PAR @ g @ P_PAR.T) > 0:
                I_6D.append(g)

R_PERP_I = [P_PERP @ g @ P_PERP.T for g in I_6D]

# Wavevector module K (462 wavevectors) and 2,250 closed Bragg triangles k1 + k2 + k3 = 0
M_SET = set()
for m0 in [
    (1, 0, 0, 0, 0, 0),
    (1, 1, 0, 0, 0, 0),
    (1, 2, 0, 0, 0, 0),
    (1, 2, 3, 0, 0, 0),
    (1, 2, -3, 0, 0, 0),
    (1, 3, 2, -1, 0, 0),
]:
    for g in IH_6D:
        M_SET.add(tuple(np.round(g @ np.array(m0, float)).astype(int)))
M_LIST = sorted(M_SET)
K_PAR = np.array([2.0 * np.pi * (P_PAR @ np.array(m, float)) for m in M_LIST])
K_PERP = np.array([2.0 * np.pi * (P_PERP @ np.array(m, float)) for m in M_LIST])

M_IDX = {m: i for i, m in enumerate(M_LIST)}
TRIPLETS = []
for i, m1 in enumerate(M_LIST):
    for j, m2 in enumerate(M_LIST):
        if j <= i:
            continue
        m3 = tuple(-np.array(m1) - np.array(m2))
        if m3 in M_IDX and len(TRIPLETS) < 4000:
            TRIPLETS.append((i, j, M_IDX[m3]))
TRIPLETS = np.array(TRIPLETS)
I1, I2, I3 = TRIPLETS[:, 0], TRIPLETS[:, 1], TRIPLETS[:, 2]

# 6 projected hypercubic unit-step vectors d_alpha = P_par e_alpha in R^3
D_ALPHA_PAR = P_PAR
D_ALPHA_PERP = P_PERP
FACTOR_K = 1.0 - np.exp(1j * (K_PAR @ D_ALPHA_PAR))  # shape (|K|, 6)


# ==============================================================================
# 2. VECTORIZED 6D BFS & SINGLE-PASS MULTI-RADIUS FOURIER / LAPLACIAN ENGINE
# ==============================================================================
def bfs_vectorized_6d(hull, R_max):
    """Vectorized BFS along unit edges of Z^6 from the origin up to ||x_par|| <= R_max."""
    A, b = hull.equations[:, :3], hull.equations[:, 3]
    AP = A @ P_PERP
    steps = np.vstack([np.eye(6, dtype=np.int64), -np.eye(6, dtype=np.int64)])
    weights = np.array([64 ** i for i in range(6)], dtype=np.int64)
    offset = 32

    frontier = np.zeros((1, 6), dtype=np.int64)
    visited_keys = np.array([np.sum((frontier[0] + offset) * weights)], dtype=np.int64)
    all_nodes = [frontier]
    R2 = (R_max + 1e-9) ** 2

    while len(frontier) > 0:
        cand = (frontier[:, None, :] + steps[None, :, :]).reshape(-1, 6)
        cand_keys = (cand + offset) @ weights
        u_keys, u_idx = np.unique(cand_keys, return_index=True)
        mask_new = ~np.isin(u_keys, visited_keys, assume_unique=True)
        cand = cand[u_idx[mask_new]]
        u_keys = u_keys[mask_new]
        if len(cand) == 0:
            break
        visited_keys = np.union1d(visited_keys, u_keys)
        cand_f = cand.astype(float)
        x_par = cand_f @ P_PAR.T
        mask_r = np.sum(x_par ** 2, axis=1) <= R2
        cand = cand[mask_r]
        cand_f = cand_f[mask_r]
        if len(cand) == 0:
            break
        mask_w = np.all(cand_f @ AP.T + b[None, :] <= 1e-9, axis=1)
        frontier = cand[mask_w]
        if len(frontier) > 0:
            all_nodes.append(frontier)

    nodes = np.vstack(all_nodes)
    x_par_all = nodes.astype(float) @ P_PAR.T
    r_norms = np.linalg.norm(x_par_all, axis=1)
    return nodes, x_par_all, r_norms


def evaluate_patch_observables(nodes, X, shift_vec=None):
    """
    Computes both:
      (a) Bispectrum B(k1, k2) = Im[ F(k1) F(k2) F(k3) ] and normalized chi = sum|B| / sum|F1 F2 F3|
      (b) Dynamical Graph-Laplacian Circular-Polarization Probe:
          A wave |k2> scatters off the quasicrystal Graph Laplacian L into <-k1| with exact
          transition amplitude:
            M_12^(L) = <-k1 | L | k2> = sum_{alpha=0}^5 (1 - e^{i k1.d_a})(1 - e^{i k2.d_a}) F_alpha(k3)*
          Interfering M_12^(L) in Left (-i) vs. Right (+i) circular quadrature against the
          two-beam Born amplitude A_12 = F(k1) F(k2) yields intensities:
            J_L = |A_12 - i M_12^(L)|^2,   J_R = |A_12 + i M_12^(L)|^2
          and Left-Right Circular Dichroism delta_J_LR = J_L - J_R = 4 Im[ A_12 * conj(M_12^(L)) ].
    """
    if shift_vec is not None:
        X = X + shift_vec[None, :]
    N = len(X)
    weights = np.array([64 ** i for i in range(6)], dtype=np.int64)
    offset = 32
    keys = (nodes + offset) @ weights
    sort_idx = np.argsort(keys)
    sorted_keys = keys[sort_idx]

    W_ind = np.zeros((N, 7), dtype=float)
    W_ind[:, 0] = 1.0
    for ax in range(6):
        nb = nodes.copy()
        nb[:, ax] += 1
        nb_keys = (nb + offset) @ weights
        pos = np.searchsorted(sorted_keys, nb_keys)
        valid = pos < N
        pos_v = pos[valid]
        match = sorted_keys[pos_v] == nb_keys[valid]
        src = np.where(valid)[0][match]
        W_ind[src, ax + 1] = 1.0

    F_all = np.zeros((len(K_PAR), 7), dtype=complex)
    for start in range(0, N, 20000):
        end = min(N, start + 20000)
        Phi_chunk = np.exp(1j * (K_PAR @ X[start:end].T))
        F_all += Phi_chunk @ W_ind[start:end, :]
    F_all /= N

    F = F_all[:, 0]
    F_alpha_conj = np.conj(F_all[:, 1:].T)

    prod_F = F[I1] * F[I2] * F[I3]
    B = np.imag(prod_F)
    chi = np.sum(np.abs(B)) / np.sum(np.abs(prod_F))

    A_12 = F[I1] * F[I2]
    M_12_L = np.sum(FACTOR_K[I1, :] * FACTOR_K[I2, :] * F_alpha_conj[:, I3].T, axis=1)
    J_R = np.abs(A_12 + 1j * M_12_L) ** 2
    J_L = np.abs(A_12 - 1j * M_12_L) ** 2
    delta_J_LR = J_L - J_R
    D_lap = np.sum(np.abs(delta_J_LR)) / (4.0 * np.sum(np.abs(A_12) * np.abs(M_12_L)))

    return chi, D_lap, B, delta_J_LR


# ==============================================================================
# 3. EXACT ANALYTICAL R -> INFINITY THERMODYNAMIC LIMIT IN E_PERP
# ==============================================================================
def integrate_polyhedron_exp(hull_obj, q_vecs, sign=-1.0, n_gl=16):
    pts_1d, wts_1d = np.polynomial.legendre.leggauss(n_gl)
    u = 0.5 * (pts_1d + 1.0)
    wu = 0.5 * wts_1d
    U1, U2, U3_g = np.meshgrid(u, u, u, indexing="ij")
    W1, W2, W3_g = np.meshgrid(wu, wu, wu, indexing="ij")
    b1 = U1.ravel()
    b2 = ((1.0 - U1) * U2).ravel()
    b3 = ((1.0 - U1) * (1.0 - U2) * U3_g).ravel()
    w_tet = (W1 * W2 * W3_g * ((1.0 - U1) ** 2) * (1.0 - U2)).ravel()
    B_bary = np.vstack([b1, b2, b3])

    verts = hull_obj.points
    center = np.mean(verts[hull_obj.vertices], axis=0)
    total_vol = 0.0
    ft_sum = np.zeros(len(q_vecs), dtype=complex)
    for tri in hull_obj.simplices:
        V_rel = verts[tri] - center[None, :]
        detJ = abs(np.linalg.det(V_rel))
        total_vol += detJ / 6.0
        Y_pts = center[None, :] + (V_rel.T @ B_bary).T
        phases = np.exp((1j * sign) * (q_vecs @ Y_pts.T))
        ft_sum += detJ * (phases @ w_tet)
    return ft_sum, total_vol


def compute_analytical_infinity_limits(hull, n_gl=16):
    """
    By P_par^T P_par + P_perp^T P_perp = I_6, exp(i k_par . x_par(n)) = exp(-i k_perp . x_perp(n)).
    By Weyl equidistribution on cut-and-project sets, as R -> infinity:
      F(k_m) -> (1 / Vol(W)) int_W exp(-i k_perp(m) . y) d^3y
      F_alpha(k_m)* -> (1 / Vol(W)) int_{W intersect (W - d_alpha_perp)} exp(+i k_perp(m) . y) d^3y,
    where W_alpha = W intersect (W - d_alpha_perp) is computed exactly via HalfspaceIntersection.
    """
    F_raw, vol_W = integrate_polyhedron_exp(hull, K_PERP, sign=-1.0, n_gl=n_gl)
    F_inf = F_raw / vol_W

    A_eq, b_eq = hull.equations[:, :3], hull.equations[:, 3]
    F_alpha_conj_inf = np.zeros((6, len(K_PERP)), dtype=complex)
    for ax in range(6):
        d_perp = D_ALPHA_PERP[:, ax]
        hs1 = hull.equations
        hs2 = np.hstack([A_eq, (b_eq + A_eq @ d_perp)[:, None]])
        hs_inter = HalfspaceIntersection(np.vstack([hs1, hs2]), -0.5 * d_perp)
        hull_ax = ConvexHull(hs_inter.intersections)
        f_ax_raw, _ = integrate_polyhedron_exp(hull_ax, K_PERP, sign=+1.0, n_gl=n_gl)
        F_alpha_conj_inf[ax] = f_ax_raw / vol_W

    prod_F = F_inf[I1] * F_inf[I2] * F_inf[I3]
    B_inf = np.imag(prod_F)
    chi_inf = np.sum(np.abs(B_inf)) / np.sum(np.abs(prod_F))

    A_12 = F_inf[I1] * F_inf[I2]
    M_12_L = np.sum(FACTOR_K[I1, :] * FACTOR_K[I2, :] * F_alpha_conj_inf[:, I3].T, axis=1)
    delta_J_inf = 4.0 * np.imag(A_12 * np.conj(M_12_L))
    D_lap_inf = np.sum(np.abs(delta_J_inf)) / (4.0 * np.sum(np.abs(A_12) * np.abs(M_12_L)))

    return chi_inf, D_lap_inf, B_inf, delta_J_inf


if __name__ == "__main__":
    t_start = time.time()
    hull_a = ConvexHull((P_PERP @ np.array(list(itertools.product((-0.5, 0.5), repeat=6))).T).T)
    p0 = np.array([0.08, 0.25, 1.48])
    hull_b = ConvexHull(np.array([R @ p0 for R in R_PERP_I]))
    hull_bm = ConvexHull(np.array([-R @ p0 for R in R_PERP_I]))

    print("================================================================================")
    print("MODULE 6 — PART 1: BISPECTRUM chi_b(R) & GRAPH-LAPLACIAN CP DICHROISM D_lap(R)")
    print("                  CONVERGENCE FOR R = 6..16 AND EXACT R -> INFINITY LIMIT")
    print("================================================================================")
    print("Pre-registered predictions:")
    print("  P1: Both chi_a(R) = 0 and D_lap,a(R) = 0 to machine precision on achiral window (a).")
    print("  P2: Both B_b(R) and delta_J_LR(R) are strictly invariant under arbitrary origin shifts")
    print("      and invert sign (B_bm = -B_b, delta_J_bm = -delta_J_b) on the mirror window (-b).")
    print("  P3: As R grows from 6 to 16, chi_b(R) and D_lap,b(R) converge to the exact nonzero")
    print("      analytical Weyl integral limits chi_b(inf) and D_lap,b(inf) on W_b subset E_perp.")

    chi_b_inf, D_lap_b_inf, B_inf, dJ_inf = compute_analytical_infinity_limits(hull_b, n_gl=16)
    print(f"\n[Exact Analytical R -> infinity Weyl Limits on W_b & W_b intersect (W_b - d_perp)]")
    print(f"  chi_b(infinity)   = {chi_b_inf:.6f}")
    print(f"  D_lap,b(infinity) = {D_lap_b_inf:.6f}  (ratio D_lap/chi_b = {D_lap_b_inf/chi_b_inf:.4f})\n")

    nodes_a, Xa_16, ra_16 = bfs_vectorized_6d(hull_a, 16.0)
    nodes_b, Xb_16, rb_16 = bfs_vectorized_6d(hull_b, 16.0)
    nodes_bm, Xbm_16, rbm_16 = bfs_vectorized_6d(hull_bm, 16.0)

    rng = np.random.default_rng(7)
    shift = rng.normal(size=3)

    for RR in (6, 8, 10, 12, 14, 16):
        ma = ra_16 <= RR + 1e-9
        mb = rb_16 <= RR + 1e-9
        mbm = rbm_16 <= RR + 1e-9

        chi_a, D_a, Ba, dJa = evaluate_patch_observables(nodes_a[ma], Xa_16[ma])
        chi_b, D_b, Bb, dJb = evaluate_patch_observables(nodes_b[mb], Xb_16[mb])
        chi_bm, D_bm, Bbm, dJbm = evaluate_patch_observables(nodes_bm[mbm], Xbm_16[mbm])
        _, _, Bb_sh, dJb_sh = evaluate_patch_observables(nodes_b[mb], Xb_16[mb], shift_vec=shift)

        print(
            f"  R={RR:2d} | |Xb|={int(np.sum(mb)):6d} | chi_a={chi_a:.2e} | chi_b={chi_b:.6f} "
            f"| D_lap(a)={D_a:.2e} | D_lap(b)={D_b:.6f} | D_lap/chi_b={D_b/chi_b:.4f} "
            f"| max|dJ_b+dJ_bm|={np.max(np.abs(dJb+dJbm)):.2e} | shift_err={np.max(np.abs(dJb-dJb_sh)):.2e}"
        )

    print("\n================================================================================")
    print("MODULE 6 — PART 2: PROPORTIONALITY OF DYNAMICAL L/R RESPONSE TO BISPECTRUM")
    print("                  ACROSS CHIRAL DEFORMATION FAMILY p0(s) = (0.08*s, 0.25, 1.48)")
    print("================================================================================")
    print("Pre-registered prediction:")
    print("  P4: Across s in {-1.5, -1.0, -0.5, 0.0, +0.5, +1.0, +1.5} at R=10, the signed")
    print("      Graph-Laplacian L/R response <sgn(B_inf) * delta_J_LR> is odd in s, vanishes at")
    print("      s=0 (where p0 lies on the x=0 mirror plane of I_h), and is proportional to chi_b.")

    signed_chi_list = []
    signed_D_list = []

    for s in (-1.5, -1.0, -0.5, 0.0, 0.5, 1.0, 1.5):
        p_s = np.array([0.08 * s, 0.25, 1.48])
        hull_s = ConvexHull(np.array([R @ p_s for R in R_PERP_I]))
        nodes_s, Xs, rs = bfs_vectorized_6d(hull_s, 10.0)
        chi_s, D_s, Bs, dJs = evaluate_patch_observables(nodes_s, Xs)
        sgn_corr_B = np.sum(Bs * B_inf) / (np.linalg.norm(Bs) * np.linalg.norm(B_inf) + 1e-30)
        sgn_corr_J = np.sum(dJs * dJ_inf) / (np.linalg.norm(dJs) * np.linalg.norm(dJ_inf) + 1e-30)
        s_chi = np.sign(sgn_corr_B) * chi_s if abs(sgn_corr_B) > 1e-10 else 0.0
        s_D = np.sign(sgn_corr_J) * D_s if abs(sgn_corr_J) > 1e-10 else 0.0
        signed_chi_list.append(s_chi)
        signed_D_list.append(s_D)
        ratio_str = f"{D_s/chi_s:.4f}" if chi_s > 1e-12 else "   N/A"
        print(
            f"  s={s:+4.1f} | |X|={len(Xs):5d} | signed_chi_b={s_chi:+.6f} "
            f"| signed_D_lap={s_D:+.6f} | |D_lap|/|chi_b|={ratio_str}"
        )

    corr_r = np.corrcoef(signed_chi_list, signed_D_list)[0, 1]
    print(f"\nLinear Pearson correlation r(signed_chi_b, signed_D_lap) = {corr_r:.6f} [elapsed: {time.time()-t_start:.2f}s]")