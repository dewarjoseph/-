"""
src/chair44/clifford.py
================================================================================
Clifford Panel-Normal Connection C_ab^(f) in Q_8 subset SU(2).
Resolves the coboundary gauge trap by coupling the local tile frame M_a
to the 1-chain panel normal n_f:
  u_a = M_a^T n_f,  u_b = M_b^T n_f in {+-e_0, +-e_1, +-e_2}
  C_ab^(f) = (sigma . u_a)(sigma . u_b) in Q_8 = {+-1, +-i, +-j, +-k} subset SU(2).
================================================================================
"""

import collections
from typing import List, Dict, Tuple, Any
import numpy as np
from scipy.linalg import eigh


# Standard Pauli Spin Matrices in SU(2)
SIGMA: List[np.ndarray] = [
    np.array([[0, 1], [1, 0]], dtype=complex),
    np.array([[0, -1j], [1j, 0]], dtype=complex),
    np.array([[1, 0], [0, -1]], dtype=complex),
]


def quaternion_trace(Q: np.ndarray) -> float:
    """
    Computes the real trace of a 2x2 SU(2) quaternion matrix:
    Tr(Q) = 2 for +1, -2 for -1, 0 for +-i, +-j, +-k.
    """
    return float(np.real(np.trace(Q)))


def q8_element_label(U: np.ndarray) -> str:
    """
    Classifies a 2x2 unitary matrix into one of the 8 elements of the quaternion group Q_8:
      {+1, -1, +i, -i, +j, -j, +k, -k}.
    """
    if np.allclose(U, np.eye(2), atol=1e-6):
        return "+1"
    if np.allclose(U, -np.eye(2), atol=1e-6):
        return "-1"
    for idx, name in enumerate(["i", "j", "k"]):
        mat = 1j * SIGMA[idx]
        if np.allclose(U, mat, atol=1e-6):
            return f"+{name}"
        if np.allclose(U, -mat, atol=1e-6):
            return f"-{name}"
    return "other"


def compute_clifford_holonomy(cycle_matrices: List[np.ndarray]) -> np.ndarray:
    """
    Computes the path-ordered product of SU(2) connection matrices along a closed cycle:
      H_loop = C_0 @ C_1 @ ... @ C_{k-1}.
    """
    H = np.eye(2, dtype=complex)
    for C in cycle_matrices:
        H = H @ C
    return H


def build_clifford_hamiltonian(tiles: List[Tuple[np.ndarray, np.ndarray, Any]]) -> Tuple[np.ndarray, List[Tuple[int, int, np.ndarray]]]:
    """
    Constructs the 2N x 2N parameter-free Clifford connection Hamiltonian:
      H_cliff = sum_{f = <a,b>} ( |a><a| x I_2 + |b><b| x I_2 - |a><b| x C_ab^(f) - |b><a| x C_ba^(f) )
    Returns:
        H_cliff: (2N, 2N) complex Hermitian matrix
        panel_edges: list of (u, v, C_uv) for each shared square panel.
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
                nf = np.zeros(3, dtype=float)
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

    return H_cliff, panel_edges


def analyze_clifford_q8_connection(tiles: List[Tuple[np.ndarray, np.ndarray, Any]]) -> Tuple[collections.Counter, np.ndarray]:
    """
    Analyzes the Clifford Q_8 connection on the panel multigraph of a Chair configuration.
    Extracts fundamental cycle holonomies via a spanning tree and computes the eigenspectrum
    of the Clifford Hamiltonian.
    
    Returns:
        hol_counts: Counter mapping Q_8 labels ('+1', '-1', '+i', '-i', '+j', '-j', '+k', '-k') to cycle counts.
        ev: real eigenvalues of H_cliff.
    """
    H_cliff, panel_edges = build_clifford_hamiltonian(tiles)

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
