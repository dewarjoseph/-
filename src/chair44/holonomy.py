"""
src/chair44/holonomy.py
================================================================================
Clifford Q_8 Holonomy and Non-Trivial Gauge-Invariant Wilson Loops on
Aperiodic Chair44 Contact Graphs.
================================================================================
"""

import collections
import numpy as np
from scipy.linalg import eigh
from src.chair44.core import SIGMA


def q8_element_label(U):
    """Labels a 2x2 matrix in SU(2) with its quaternion group element Q_8."""
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


def analyze_clifford_q8_connection(tiles):
    """
    Computes Clifford panel-normal connection C_ab^(f) = (sigma . u_a)(sigma . u_b) in Q_8
    and evaluates fundamental cycle holonomies and the Clifford Hamiltonian spectrum.
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

    # Spanning tree on panel multigraph -> fundamental cycle holonomies
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
