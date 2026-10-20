"""
module5_benchmark.py
================================================================================
Module 5 Controlled Benchmark:
  Task A: Closing out 3D Chair44 (Aperiodic Level-(k+1) Superchair vs. Rotated-Cell
          Periodic Control Level-k Superchair x 8 along 2^k * Lambda_7, for k=1,2,3)
  Task B: 6D -> 3D Icosahedral Cut-and-Project Quasicrystal (Achiral I_h Window vs.
          Chiral I-Orbit Window & Mirror, testing H1, H2, H3 for R = 6, 8, 10, 12)
================================================================================
"""

import collections
import itertools
import time
import warnings
import numpy as np
from scipy.linalg import eigh
from scipy.sparse import coo_matrix
from scipy.sparse.linalg import eigsh, lobpcg
from scipy.spatial import ConvexHull

warnings.filterwarnings("ignore")

# ==============================================================================
# TASK A: CLOSE OUT CHAIR44 (k = 1, 2, 3 -> N = 64, 512, 4096 TILES)
# ==============================================================================
FR30 = {
    '0': (0, 1, 2),
    (0, 0, 0): (0, 1, 2),
    (0, 0, 1): (0, 2, 1),
    (0, 1, 0): (2, 1, 0),
    (0, 1, 1): (1, 2, 0),
    (1, 0, 0): (1, 0, 2),
    (1, 0, 1): (0, 1, 2),
    (1, 1, 0): (2, 0, 1),
}

U3 = [v for v in itertools.product((0, 1), repeat=3) if v != (1, 1, 1)]
BASE_CENTERS = [np.array([2 * u[0] + 1, 2 * u[1] + 1, 2 * u[2] + 1]) for u in U3]
SIGMA = [
    np.array([[0, 1], [1, 0]], dtype=complex),
    np.array([[0, -1j], [1j, 0]], dtype=complex),
    np.array([[1, 0], [0, -1]], dtype=complex),
]


def perm_mat(p):
    M = np.zeros((3, 3), dtype=int)
    for i in range(3):
        M[i, p[i]] = 1
    return M


def generate_supertile_tiles(frames_dict, level):
    child_ops = [(perm_mat(frames_dict['0']), np.array([1, 1, 1]))]
    for v in U3:
        Ds = np.diag([1 - 2 * v[0], 1 - 2 * v[1], 1 - 2 * v[2]])
        child_ops.append((Ds @ perm_mat(frames_dict[v]), 4 * np.array(v)))
    poses = [(np.eye(3, dtype=int), np.array([0, 0, 0]))]
    for _ in range(level):
        new_poses = []
        for G, T in poses:
            for gc, tc in child_ops:
                new_poses.append((G @ gc, 2 * T + G @ tc))
        poses = new_poses
    tiles = []
    for G, T in poses:
        cubes = {tuple((G @ bc + 2 * T - 1) // 2) for bc in BASE_CENTERS}
        tiles.append((G, T, cubes))
    return tiles


def generate_rotated_cell_periodic(frames_dict, k):
    base_tiles = generate_supertile_tiles(frames_dict, k)
    b1 = np.array([1, 1, 1])
    b2 = np.array([2, 1, -1])
    b3 = np.array([-1, 2, 1])
    scale = 2 ** k
    tiles = []
    for i1, i2, i3 in itertools.product((0, 1), repeat=3):
        shift = scale * (i1 * b1 + i2 * b2 + i3 * b3)
        sh_t = (int(shift[0]), int(shift[1]), int(shift[2]))
        for G, T, cubes in base_tiles:
            new_cubes = {(c[0] + sh_t[0], c[1] + sh_t[1], c[2] + sh_t[2]) for c in cubes}
            tiles.append((G, T + shift, new_cubes))
    return tiles


def smallest_eigs_fast(M_csr, k_eigs=3, is_zero_mode_lap=False):
    n_dim = M_csr.shape[0]
    if n_dim <= 1600:
        return np.sort(np.real(eigh(M_csr.toarray(), eigvals_only=True)))[:k_eigs]
    if is_zero_mode_lap:
        rng = np.random.default_rng(42)
        X0 = rng.standard_normal((n_dim, k_eigs + 2))
        Y0 = np.ones((n_dim, 1))
        ev, _ = lobpcg(M_csr, X0, Y=Y0, largest=False, tol=1e-5, maxiter=1500)
        return np.concatenate(([0.0], np.sort(np.real(ev))[: k_eigs - 1]))
    ev = eigsh(M_csr, k=k_eigs, sigma=2.0, which='LM', return_eigenvectors=False)
    return np.sort(np.real(ev))


def compute_task_a_observables(tiles):
    n = len(tiles)
    owner = {}
    for a, (_, _, cubes) in enumerate(tiles):
        for c in cubes:
            owner[c] = a

    N_panels = collections.defaultdict(lambda: np.zeros((3, 3), dtype=float))
    W = collections.Counter()
    cliff_blocks = collections.defaultdict(lambda: np.zeros((2, 2), dtype=complex))
    diag_cliff = np.zeros(n, dtype=float)

    for (x, y, z), a in owner.items():
        for ax, (dx, dy, dz) in enumerate([(1, 0, 0), (0, 1, 0), (0, 0, 1)]):
            b = owner.get((x + dx, y + dy, z + dz))
            if b is not None and b != a:
                u, v = (a, b) if a < b else (b, a)
                W[(u, v)] += 1
                N_panels[(u, v)][ax, ax] += 1.0

                nf = np.zeros(3)
                nf[ax] = 1.0
                Mu, Mv = tiles[u][0], tiles[v][0]
                uu, uv = Mu.T @ nf, Mv.T @ nf
                sig_u = sum(uu[j] * SIGMA[j] for j in range(3))
                sig_v = sum(uv[j] * SIGMA[j] for j in range(3))
                Cab = sig_u @ sig_v
                diag_cliff[u] += 1.0
                diag_cliff[v] += 1.0
                cliff_blocks[(u, v)] -= Cab

    rows_c, cols_c, vals_c = [], [], []
    for u in range(n):
        rows_c.extend([2 * u, 2 * u + 1])
        cols_c.extend([2 * u, 2 * u + 1])
        vals_c.extend([diag_cliff[u], diag_cliff[u]])
    for (u, v), blk in cliff_blocks.items():
        for r in range(2):
            for c_idx in range(2):
                if abs(blk[r, c_idx]) > 1e-12:
                    rows_c.extend([2 * u + r, 2 * v + c_idx])
                    cols_c.extend([2 * v + c_idx, 2 * u + r])
                    vals_c.extend([blk[r, c_idx], np.conj(blk[r, c_idx])])
    H_cliff_csr = coo_matrix((vals_c, (rows_c, cols_c)), shape=(2 * n, 2 * n)).tocsr()
    cliff_gap = smallest_eigs_fast(H_cliff_csr, k_eigs=2)[0]

    rows_s, cols_s, vals_s = [], [], []
    diag_s = [np.zeros((3, 3), dtype=float) for _ in range(n)]
    for (u, v), w in W.items():
        Mu = tiles[u][0].astype(float)
        Mv = tiles[v][0].astype(float)
        Nuv = N_panels[(u, v)]
        diag_s[u] += w * np.eye(3) + Mu.T @ Nuv @ Mu
        diag_s[v] += w * np.eye(3) + Mv.T @ Nuv @ Mv
        off_uv = -w * np.eye(3) - Mu.T @ Nuv @ Mv
        for r in range(3):
            for c_idx in range(3):
                if abs(off_uv[r, c_idx]) > 1e-12:
                    rows_s.extend([3 * u + r, 3 * v + c_idx])
                    cols_s.extend([3 * v + c_idx, 3 * u + r])
                    vals_s.extend([off_uv[r, c_idx], off_uv[r, c_idx]])
    for u in range(n):
        blk = diag_s[u]
        for r in range(3):
            for c_idx in range(3):
                if abs(blk[r, c_idx]) > 1e-12:
                    rows_s.append(3 * u + r)
                    cols_s.append(3 * u + c_idx)
                    vals_s.append(blk[r, c_idx])
    L_solder_csr = coo_matrix((vals_s, (rows_s, cols_s)), shape=(3 * n, 3 * n)).tocsr()
    solder_eigs = smallest_eigs_fast(L_solder_csr, k_eigs=3)

    I3 = np.eye(3, dtype=int)
    E = set()
    V = set()
    for a, (_, _, cubes) in enumerate(tiles):
        for c in cubes:
            c_arr = np.array(c)
            for ax in range(3):
                for s in (0, 1):
                    nb = list(c)
                    nb[ax] += 1 if s == 1 else -1
                    if tuple(nb) in cubes:
                        continue
                    d = np.zeros(3, dtype=int)
                    d[ax] = s
                    v_arr = c_arr + d
                    a1, a2 = [aa for aa in range(3) if aa != ax]
                    for e_key in [
                        (tuple(v_arr), a1),
                        (tuple(v_arr + I3[a1]), a2),
                        (tuple(v_arr + I3[a2]), a1),
                        (tuple(v_arr), a2),
                    ]:
                        E.add(e_key)
                    for s1, s2 in itertools.product((0, 1), repeat=2):
                        V.add(tuple(v_arr + s1 * I3[a1] + s2 * I3[a2]))
    V = sorted(V)
    E = sorted(E)
    vi = {v_coord: idx for idx, v_coord in enumerate(V)}
    rows_d, cols_d, vals_d = [], [], []
    for idx_e, (v_coord, ax) in enumerate(E):
        w_coord = list(v_coord)
        w_coord[ax] += 1
        rows_d.extend([idx_e, idx_e])
        cols_d.extend([vi[v_coord], vi[tuple(w_coord)]])
        vals_d.extend([-1.0, 1.0])
    d0 = coo_matrix((vals_d, (rows_d, cols_d)), shape=(len(E), len(V))).tocsr()
    Delta0 = d0.T @ d0
    d0_eigs = smallest_eigs_fast(Delta0, k_eigs=3, is_zero_mode_lap=True)
    delta0_gap = d0_eigs[1]

    V_arr = np.array(V, dtype=float)
    V_centered = V_arr - np.mean(V_arr, axis=0, keepdims=True)
    cov_eigs = np.sort(eigh((V_centered.T @ V_centered) / len(V), eigvals_only=True))
    lmax_sq = cov_eigs[-1]

    return cliff_gap, solder_eigs, delta0_gap, lmax_sq


# ==============================================================================
# TASK B: 6D -> 3D ICOSAHEDRAL CUT-AND-PROJECT QUASICRYSTAL (H1, H2, H3)
# ==============================================================================
def run_task_b():
    tau = (1.0 + np.sqrt(5.0)) / 2.0
    V_par = np.array(
        [
            [1, tau, 0],
            [-1, tau, 0],
            [0, 1, tau],
            [0, -1, tau],
            [tau, 0, 1],
            [tau, 0, -1],
        ],
        dtype=float,
    ).T
    P_par = V_par / np.sqrt(2.0 * (1.0 + tau ** 2))

    V_perp = np.array(
        [
            [-tau, 1, 0],
            [tau, 1, 0],
            [0, -tau, 1],
            [0, tau, 1],
            [1, 0, -tau],
            [1, 0, tau],
        ],
        dtype=float,
    ).T
    P_perp = V_perp / np.sqrt(2.0 * (1.0 + tau ** 2))
    Pi_par = P_par.T @ P_par

    preserving_Ih = []
    proper_I = []
    for perm in itertools.permutations(range(6)):
        P_mat = np.zeros((6, 6))
        for i, p in enumerate(perm):
            P_mat[i, p] = 1.0
        for signs in itertools.product((-1.0, 1.0), repeat=6):
            g = P_mat * np.array(signs)[:, None]
            if np.allclose(g @ Pi_par, Pi_par @ g, atol=1e-9):
                preserving_Ih.append(g)
                if np.linalg.det(P_par @ g @ P_par.T) > 0:
                    proper_I.append(g)

    print(
        f"6D Signed Permutations Enumerated: 46080 | Preserving E_par (I_h): {len(preserving_Ih)} "
        f"| Proper Rotations det=+1 on E_par (I): {len(proper_I)}"
    )
    R_perp_I = [P_perp @ g @ P_perp.T for g in proper_I]

    # Window (a): Rhombic triacontahedron (projected 6-cube [-0.5, 0.5]^6, symmetry I_h, achiral)
    cube6 = np.array(list(itertools.product((-0.5, 0.5), repeat=6)))
    hull_a = ConvexHull((P_perp @ cube6.T).T)

    # Window (b): Chiral window = convex hull of 60-point I-orbit of generic p0 in E_perp
    # Three distinct generic orbit seeds in E_perp for H2 and H3:
    p0_1 = np.array([0.08, 0.25, 1.48])
    p0_2 = np.array([0.14, 0.38, 1.52])
    p0_3 = np.array([0.11, 0.33, 1.49])

    hull_b1 = ConvexHull(np.array([R @ p0_1 for R in R_perp_I]))
    hull_b1_mir = ConvexHull(np.array([-R @ p0_1 for R in R_perp_I]))
    hull_b2 = ConvexHull(np.array([R @ p0_2 for R in R_perp_I]))
    hull_b3 = ConvexHull(np.array([R @ p0_3 for R in R_perp_I]))

    def bfs_cut_and_project(hull, R_max):
        A = hull.equations[:, :3]
        b = hull.equations[:, 3]
        AP_perp = A @ P_perp
        root = (0, 0, 0, 0, 0, 0)
        visited = {root}
        q = collections.deque([root])
        accepted = [root]
        R2 = (R_max + 1e-9) ** 2
        while q:
            curr = q.popleft()
            for ax in range(6):
                for step in (-1, 1):
                    nb = list(curr)
                    nb[ax] += step
                    nb_t = tuple(nb)
                    if nb_t not in visited:
                        visited.add(nb_t)
                        nb_arr = np.array(nb_t, dtype=float)
                        x_par = P_par @ nb_arr
                        if np.dot(x_par, x_par) <= R2 and np.all(AP_perp @ nb_arr + b <= 1e-9):
                            accepted.append(nb_t)
                            q.append(nb_t)
        n_mat = np.array(accepted, dtype=float)
        return accepted, (P_par @ n_mat.T).T

    # Test H1: Graph Laplacian spectrum of Window (b) vs its mirror
    pts_b_h1, _ = bfs_cut_and_project(hull_b1, 5.0)
    pts_bm_h1, _ = bfs_cut_and_project(hull_b1_mir, 5.0)

    def build_6d_graph_laplacian(pts_6d):
        idx_map = {pt: i for i, pt in enumerate(pts_6d)}
        N = len(pts_6d)
        L = np.zeros((N, N), dtype=float)
        for i, pt in enumerate(pts_6d):
            for ax in range(6):
                nb = list(pt)
                nb[ax] += 1
                j = idx_map.get(tuple(nb))
                if j is not None:
                    L[i, j] = L[j, i] = -1.0
                    L[i, i] += 1.0
                    L[j, j] += 1.0
        return np.sort(eigh(L, eigvals_only=True))

    ev_b = build_6d_graph_laplacian(pts_b_h1)
    ev_bm = build_6d_graph_laplacian(pts_bm_h1)
    print(
        f"\n[H1 Verification] R=5.0 (|V|={len(pts_b_h1)}): "
        f"max |Spec(L_b) - Spec(L_b_mirror)| = {np.max(np.abs(ev_b - ev_bm)):.3e}"
    )
    print(f"  Window (b) low eigs:        {np.round(ev_b[:6], 6)}")
    print(f"  Window (b) mirror low eigs: {np.round(ev_bm[:6], 6)}")

    # Build icosahedral-module wavevectors k = 2*pi * P_par @ m
    m_base = [
        (1, 0, 0, 0, 0, 0),
        (1, 1, 0, 0, 0, 0),
        (1, 2, 0, 0, 0, 0),
        (1, 2, 3, 0, 0, 0),
        (1, 2, -3, 0, 0, 0),
        (1, 3, 2, -1, 0, 0),
    ]
    m_set = set()
    for m0 in m_base:
        m_arr = np.array(m0, dtype=float)
        for g in preserving_Ih:
            gm = tuple(np.round(g @ m_arr).astype(int))
            m_set.add(gm)
    m_list = sorted(m_set)
    k_vecs = np.array([2.0 * np.pi * (P_par @ np.array(m, dtype=float)) for m in m_list])
    # Fixed mirror sigma: reflection across x=0 plane, sigma = diag(-1, 1, 1) in I_h \ I
    sigma = np.diag([-1.0, 1.0, 1.0])
    k_sig = (sigma @ k_vecs.T).T

    print(f"\n[H2 & H3 Verification] Wavevector module size |K| = {len(k_vecs)} (mirror sigma = diag(-1,1,1)):")
    for R in (6, 8, 10, 12):
        _, xa = bfs_cut_and_project(hull_a, R)
        nb1, xb1 = bfs_cut_and_project(hull_b1, R)
        nb1m, xb1m = bfs_cut_and_project(hull_b1_mir, R)
        _, xb2 = bfs_cut_and_project(hull_b2, R)
        _, xb3 = bfs_cut_and_project(hull_b3, R)

        def metrics(X):
            F = np.sum(np.exp(1j * (k_vecs @ X.T)), axis=1)
            F_s = np.sum(np.exp(1j * (k_sig @ X.T)), axis=1)
            I_k = np.abs(F) ** 2
            I_s = np.abs(F_s) ** 2
            A_int = np.sum(np.abs(I_k - I_s)) / np.sum(I_k)
            A_amp = np.sum(np.abs(F - F_s)) / np.sum(np.abs(F))
            return A_int, A_amp, F

        A_int_a, A_amp_a, _ = metrics(xa)
        A_int_b1, A_amp_b1, F_b1 = metrics(xb1)
        A_int_b1m, A_amp_b1m, F_b1m = metrics(xb1m)
        A_int_b2, A_amp_b2, _ = metrics(xb2)
        A_int_b3, A_amp_b3, _ = metrics(xb3)
        chiral_pts = len(set(nb1) ^ set(nb1m))
        sign_flip_err = np.max(np.abs(np.imag(F_b1) + np.imag(F_b1m)))

        print(
            f"  R={R:2d} | |X_a|={len(xa):5d}, |X_b1|={len(xb1):5d} (|X_b1 Δ X_b1_mir|={chiral_pts:4d})"
        )
        print(
            f"       | H2 Intensity A(R) = sum|I(k)-I(σk)|/sum I(k): "
            f"A_a={A_int_a:.2e}, A_b1={A_int_b1:.2e}, A_b1_mir={A_int_b1m:.2e}, "
            f"A_b2={A_int_b2:.2e}, A_b3={A_int_b3:.2e}"
        )
        print(
            f"       | Complex Structure Factor A_amp(R) = sum|F(k)-F(σk)|/sum|F(k)|: "
            f"A_a={A_amp_a:.2e}, A_b1={A_amp_b1:.6f}, A_b1_mir={A_amp_b1m:.6f} "
            f"(max|Im F_b + Im F_bm|={sign_flip_err:.2e})"
        )
        print(
            f"       | H3 Seed Comparison A_amp(R): "
            f"seed1={A_amp_b1:.6f}, seed2={A_amp_b2:.6f}, seed3={A_amp_b3:.6f}"
        )


if __name__ == "__main__":
    print("================================================================================")
    print("MODULE 5 — TASK A: CLOSING OUT CHAIR44 (APERIODIC VS. ROTATED-CELL PERIODIC)")
    print("================================================================================")
    print("Pre-registered prediction: All local operator ratios (ii)/(i) -> 1 as k grows.")
    for k in (1, 2, 3):
        t0 = time.time()
        ap_tiles = generate_supertile_tiles(FR30, k + 1)
        pe_tiles = generate_rotated_cell_periodic(FR30, k)
        c_ap, s_ap, d0_ap, l2_ap = compute_task_a_observables(ap_tiles)
        c_pe, s_pe, d0_pe, l2_pe = compute_task_a_observables(pe_tiles)
        w_ap = d0_ap * l2_ap
        w_pe = d0_pe * l2_pe
        print(f"\n--- k={k} (N={8**(k+1)} tiles, {7*8**(k+1)} unit cubes) [elapsed: {time.time()-t0:.2f}s] ---")
        print(f"  Clifford gap:            (i) ap={c_ap:.6f} | (ii) pe={c_pe:.6f} | ratio (ii)/(i) = {c_pe/c_ap:.6f}")
        print(f"  Soldered eig 1:          (i) ap={s_ap[0]:.6f} | (ii) pe={s_pe[0]:.6f} | ratio (ii)/(i) = {s_pe[0]/s_ap[0]:.6f}")
        print(f"  Soldered eig 2:          (i) ap={s_ap[1]:.6f} | (ii) pe={s_pe[1]:.6f} | ratio (ii)/(i) = {s_pe[1]/s_ap[1]:.6f}")
        print(f"  Soldered eig 3:          (i) ap={s_ap[2]:.6f} | (ii) pe={s_pe[2]:.6f} | ratio (ii)/(i) = {s_pe[2]/s_ap[2]:.6f}")
        print(f"  Polyhedral Δ0 raw gap:   (i) ap={d0_ap:.6f} | (ii) pe={d0_pe:.6f} | ratio (ii)/(i) = {d0_pe/d0_ap:.6f}")
        print(f"  Polyhedral Δ0 * L_max^2: (i) ap={w_ap:.6f} | (ii) pe={w_pe:.6f} | ratio (ii)/(i) = {w_pe/w_ap:.6f}")

    print("\n================================================================================")
    print("MODULE 5 — TASK B: CHIRALITY ON 6D -> 3D ICOSAHEDRAL CUT-AND-PROJECT QUASICRYSTAL")
    print("================================================================================")
    print("Pre-registered hypotheses:")
    print("  H1: Laplacian spectrum of chiral window (b) and its mirror are identical to machine precision.")
    print("  H2: Structure factor intensity I(k) = |sum_j exp(i k.x_j)|^2 has A_a(R) -> 0 and A_b(R) -> const > 0.")
    print("  H3: Chiral diffraction asymmetry is independent of generic orbit seed point up to patch noise.")
    run_task_b()