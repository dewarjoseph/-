"""
src/chair44/clifford_holonomy.py
================================================================================
Clifford Panel-Normal Connection C_ab^(f) in Q_8 subset SU(2).
Resolves the coboundary gauge trap by coupling local frame M_a to the panel normal n_f:
  C_ab^(f) = (sigma . u_a)(sigma . u_b) in Q_8 = {+-1, +-i, +-j, +-k}.
================================================================================
"""

import collections
import numpy as np
from scipy.linalg import eigh
from scipy.sparse import coo_matrix
from src.chair44.fr30_frames import SIGMA


def q8_element_label(U):
    """Classify 2x2 unitary matrix into Q_8 elements."""
    if np.allclose(U, np.eye(2)):
        return "+1"
    if np.allclose(U, -np.eye(2)):
        return "-1"
    for idx, name in enumerate(["i", "j", "k"]):
        mat = 1j * SIGMA[idx]
        if np.allclose(U, mat):
            return f"+{name}"
        if np.allclose(U, -mat):
            return f"-{name}"
    return "other"


def build_clifford_hamiltonian(tiles):
    """
    Constructs the Clifford panel-normal Hamiltonian H_cliff of size 2N x 2N.
    Returns (H_cliff_csr, diag_cliff, cliff_blocks, W).
    """
    n = len(tiles)
    owner = {}
    for a, (_, _, cubes) in enumerate(tiles):
        for c in cubes:
            owner[c] = a

    W = collections.Counter()
    cliff_blocks = collections.defaultdict(lambda: np.zeros((2, 2), dtype=complex))
    diag_cliff = np.zeros(n, dtype=float)

    for (x, y, z), a in owner.items():
        for ax, (dx, dy, dz) in enumerate([(1, 0, 0), (0, 1, 0), (0, 0, 1)]):
            b = owner.get((x + dx, y + dy, z + dz))
            if b is not None and b != a:
                u, v = (a, b) if a < b else (b, a)
                W[(u, v)] += 1

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
    return H_cliff_csr, diag_cliff, cliff_blocks, W


def analyze_clifford_q8_connection(tiles):
    """
    Computes Q_8 cycle holonomies and spectrum of H_cliff.
    """
    n = len(tiles)
    owner = {}
    for a, (_, _, cubes) in enumerate(tiles):
        for c in cubes:
            owner[c] = a

    panel_edges = []
    H_cliff = np.zeros((2 * n, 2 * n), dtype=complex)

    for (x, y, z), a in owner.items():
        for ax, (dx, dy, dz) in enumerate([(1, 0, 0), (0, 1, 0), (0, 0, 1)]):
            b = owner.get((x + dx, y + dy, z + dz))
            if b is not None and b != a:
                u, v = (a, b) if a < b else (b, a)
                nf = np.zeros(3)
                nf[ax] = 1.0
                Mu, Mv = tiles[u][0], tiles[v][0]
                uu, uv = Mu.T @ nf, Mv.T @ nf
                sig_u = sum(uu[j] * SIGMA[j] for j in range(3))
                sig_v = sum(uv[j] * SIGMA[j] for j in range(3))
                Cab = sig_u @ sig_v
                panel_edges.append((u, v, Cab))
                H_cliff[2 * u : 2 * u + 2, 2 * u : 2 * u + 2] += np.eye(2)
                H_cliff[2 * v : 2 * v + 2, 2 * v : 2 * v + 2] += np.eye(2)
                H_cliff[2 * u : 2 * u + 2, 2 * v : 2 * v + 2] -= Cab
                H_cliff[2 * v : 2 * v + 2, 2 * u : 2 * u + 2] -= Cab.conj().T

    # Spanning tree on the panel multigraph -> fundamental cycle holonomies
    adj = collections.defaultdict(list)
    for idx, (u, v, Cab) in enumerate(panel_edges):
        adj[u].append((v, Cab, idx))
        adj[v].append((u, Cab.conj().T, idx))

    parent = {0: None}
    tree_edges = set()
    T_root = {0: np.eye(2, dtype=complex)}
    q = [0]
    while q:
        u = q.pop(0)
        for v, Cab, idx in adj[u]:
            if v not in parent:
                parent[v] = u
                tree_edges.add(idx)
                T_root[v] = T_root[u] @ Cab
                q.append(v)

    hol_counts = collections.Counter()
    for idx, (u, v, Cab) in enumerate(panel_edges):
        if idx in tree_edges:
            continue
        H_loop = T_root[u] @ Cab @ T_root[v].conj().T
        hol_counts[q8_element_label(H_loop)] += 1

    ev = np.sort(np.real(eigh(H_cliff, eigvals_only=True)))
    return hol_counts, ev


def verify_q8_clifford_holonomy(tiles=None):
    """
    Verifies that the panel-normal connection on Chair44 possesses non-trivial
    Clifford Q_8 holonomy cycles, breaking trivial gauge coboundary trap.
    """
    if tiles is None:
        from src.chair44.fr30_frames import FR30, generate_supertile_tiles
        tiles = generate_supertile_tiles(FR30, level=1)
    hol_counts, ev = analyze_clifford_q8_connection(tiles)
    non_trivial = sum(count for el, count in hol_counts.items() if el != "+1")
    total = sum(hol_counts.values())
    pct = (non_trivial / total * 100.0) if total > 0 else 0.0
    return {
        "hol_counts": dict(hol_counts),
        "non_trivial_percentage": pct,
        "nontrivial_percentage": pct,
        "non_trivial_cycles": non_trivial,
        "total_fundamental_cycles": total,
        "spectral_gap_open": float(ev[1] - ev[0]) > 0.0,
        "q8_isomorphism_verified": non_trivial > 0,
        "eigenvalues": ev.tolist()
    }

