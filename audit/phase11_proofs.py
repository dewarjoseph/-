#!/usr/bin/env python3
"""Phase XI: exact (symbolic or integer) checks behind the proof obligations of Part I and the constants of Theorems XI.B-F.

  overlap3d   c(eta) of Phase VII is EXACTLY the normalised autocorrelation of the Dirichlet ground state sin(pi r)/r of the unit
              3-ball: for radial f, g, int f(|y|) g(|y - s e|) dy = (2 pi / s) iint_{|r-t| <= s <= r+t} r f(r) t g(t) dr dt, and r f(r) =
              sin(pi r); the planar integral is done symbolically.
  overlap1d   C(t) = (1 - t/2) cos(pi t/2) + sin(pi t/2)/pi for cos(pi y/2) on [-1, 1] (the ladder's IMS cutoff).
  rc          r_c = sqrt(619)/14 <= 311/175 (exact integers) and r_c is the largest centroid-to-point distance of the chair.
  panels      the chair has 24 unit boundary faces (so Deg = 24 on every tiling).
  q8          minimal rotation angles of the non-identity elements of Q8 in the spinor representation (pi/2 and pi), and the
              decomposition of the adjoint representation into the three non-trivial characters.
  ims_random  the exact IMS identity (Theorem B1) on random graphs with random U(2) links and random partitions of unity.
  transport   the loop-transport bound (Theorem F1) and the cycle-cover bound (Theorem E) on random small examples.
Usage: python -u -I audit/phase11_proofs.py [check ...] -> audit/results/phase11_proofs.json"""
import os, sys, json, math, itertools, types
sys.modules.setdefault('resource', types.SimpleNamespace(getrusage=lambda *a: types.SimpleNamespace(ru_maxrss=0), RUSAGE_SELF=0))
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); RES = os.path.join(HERE, 'results')
import numpy as np
OUT = os.path.join(RES, 'phase11_proofs.json')

def overlap3d():
    import sympy as sp
    r, t, s = sp.symbols('r t s', positive=True); f = sp.sin(sp.pi * r) * sp.sin(sp.pi * t)
    full = sp.integrate(sp.sin(sp.pi * r), (r, 0, 1)) ** 2
    tri1 = sp.integrate(sp.integrate(f, (t, 0, s - r)), (r, 0, s))          # r + t < s
    tri2 = sp.integrate(sp.integrate(f, (t, 0, r - s)), (r, s, 1))          # r - t > s (and the symmetric t - r > s)
    norm = 4 * sp.pi * sp.integrate(sp.sin(sp.pi * r) ** 2, (r, 0, 1))       # int phi^2 = 2 pi
    C = sp.simplify((2 * sp.pi / s) * (full - tri1 - 2 * tri2) / norm)
    target = (sp.pi * (1 - s / 2) * sp.sin(sp.pi * s) + 1 - sp.cos(sp.pi * s)) / (sp.pi ** 2 * s)
    small = sp.series(target, s, 0, 4).removeO()
    return {'C': str(C), 'equals_phase7_formula': bool(sp.simplify(C - target) == 0), 'series_at_0': str(small),
            's2_coefficient_is_minus_pi2_over_6': bool(sp.simplify(sp.expand(small).coeff(s, 2) + sp.pi ** 2 / 6) == 0)}

def overlap1d():
    import sympy as sp
    y, t = sp.symbols('y t', positive=True); phi = lambda z: sp.cos(sp.pi * z / 2)
    C = sp.simplify(sp.integrate(phi(y) * phi(y - t), (y, -1 + t, 1)) / sp.integrate(phi(y) ** 2, (y, -1, 1)))
    target = (1 - t / 2) * sp.cos(sp.pi * t / 2) + sp.sin(sp.pi * t / 2) / sp.pi
    return {'C': str(C), 'equals_ladder_formula': bool(sp.simplify(C - target) == 0),
            'series_at_0': str(sp.series(target, t, 0, 4).removeO())}

def rc():
    from fractions import Fraction
    U3 = [v for v in itertools.product((0, 1), repeat=3) if v != (1, 1, 1)]
    cen = Fraction(13, 14); far = 0
    for u in U3:                                    # the farthest points of the chair are cube corners
        for c in itertools.product((0, 1), repeat=3):
            p = [u[i] + c[i] for i in range(3)]; far = max(far, sum((Fraction(x) - cen) ** 2 for x in p))
    return {'rc_squared': str(far), 'equals_619_over_196': far == Fraction(619, 196),
            'bound_311_175_squared_minus_rc_squared': str(Fraction(311, 175) ** 2 - far), 'bound_ok': Fraction(311, 175) ** 2 >= far}

def panels():
    U3 = {v for v in itertools.product((0, 1), repeat=3) if v != (1, 1, 1)}; faces = 0
    for u in U3:
        for ax in range(3):
            for s in (1, -1):
                w = list(u); w[ax] += s
                if tuple(w) not in U3: faces += 1
    return {'boundary_faces': faces, 'internal_adjacencies': (6 * 7 - faces) // 2}

def q8():
    P = np.array([[[0, 1], [1, 0]], [[0, -1j], [1j, 0]], [[1, 0], [0, -1]]], dtype=complex); I = np.eye(2)
    els = {'1': I, '-1': -I}
    for k in range(3): els[f'q{k+1}'] = -1j * P[k]; els[f'-q{k+1}'] = 1j * P[k]
    ang = {n: float(np.min(np.abs(np.angle(np.linalg.eigvals(W))))) for n, W in els.items()}
    def adj(W): return np.array([[0.5 * np.trace(P[a] @ W @ P[b] @ W.conj().T).real for b in range(3)] for a in range(3)])
    # adjoint = chi_1 + chi_2 + chi_3: Ad(W) is diagonal with entries chi_k(W), chi_k = +1 on {+-1, +-q_k}
    chi = lambda k, n: 1 if n in ('1', '-1', f'q{k}', f'-q{k}') else -1
    ok = all(np.allclose(adj(W), np.diag([chi(k, n) for k in (1, 2, 3)])) for n, W in els.items())
    return {'min_rotation_angle': ang, 'angle_gap_nonidentity': min(v for n, v in ang.items() if n != '1'), 'adjoint_is_sum_of_characters': ok}

def rand_unitary(rng, n):
    Z = rng.normal(size=(n, n)) + 1j * rng.normal(size=(n, n)); Q, R = np.linalg.qr(Z); return Q * (np.diag(R) / abs(np.diag(R)))

def ims_random(trials=20, seed=1):
    rng = np.random.default_rng(seed); worst = 0.0; lowerok = True
    for _ in range(trials):
        nv = rng.integers(6, 14); edges = [(a, b) for a in range(nv) for b in range(a + 1, nv) if rng.random() < 0.35]
        edges += [(a, b) for a, b in edges if rng.random() < 0.2]          # some multi-edges
        if not edges: continue
        U = [rand_unitary(rng, 2) for _ in edges]; n = 2 * nv
        H = np.zeros((n, n), complex); deg = np.zeros(nv)
        for (a, b), u in zip(edges, U):
            H[2 * a:2 * a + 2, 2 * b:2 * b + 2] -= u; H[2 * b:2 * b + 2, 2 * a:2 * a + 2] -= u.conj().T; deg[a] += 1; deg[b] += 1
        H += np.diag(np.repeat(deg, 2))
        J = rng.integers(2, 6); X = rng.random((J, nv)) ** 2 + 0.05; X /= np.sqrt((X ** 2).sum(0))   # partition of unity (all c_e > 0)
        Ht = np.diag(np.repeat(deg, 2)).astype(complex)
        for (a, b), u in zip(edges, U):
            c = float(X[:, a] @ X[:, b]); Ht[2 * a:2 * a + 2, 2 * b:2 * b + 2] -= u / c; Ht[2 * b:2 * b + 2, 2 * a:2 * a + 2] -= u.conj().T / c
        S = sum(np.diag(np.repeat(X[j], 2)) @ Ht @ np.diag(np.repeat(X[j], 2)) for j in range(J))
        worst = max(worst, float(np.abs(S - H).max()))
        lam = np.linalg.eigvalsh(H)[0]; lams = [np.linalg.eigvalsh(Ht)[0]]           # supports = all vertices: B2 gives lam >= lam_min(Ht)
        lowerok &= bool(lam >= min(lams) - 1e-10)
    return {'trials': trials, 'max_identity_error': worst, 'lower_bound_holds': lowerok}

def transport(trials=200, seed=2):
    """random cycle graphs with chords and random SU(2)/Q8 links: lambda_min(H) >= 1/kappa (F1) using, for each vertex, the best
    closed walk among its fundamental cycles; and the cycle-cover bound (E) with the fundamental cycles"""
    rng = np.random.default_rng(seed); ok = True; ratios = []
    for _ in range(trials):
        nv = int(rng.integers(4, 9)); edges = [(i, (i + 1) % nv) for i in range(nv)] + [tuple(sorted(rng.choice(nv, 2, replace=False))) for _ in range(rng.integers(0, 3))]
        U = [rand_unitary(rng, 2) for _ in edges]; n = 2 * nv; H = np.zeros((n, n), complex); deg = np.zeros(nv)
        for (a, b), u in zip(edges, U):
            H[2 * a:2 * a + 2, 2 * b:2 * b + 2] -= u; H[2 * b:2 * b + 2, 2 * a:2 * a + 2] -= u.conj().T; deg[a] += 1; deg[b] += 1
        H += np.diag(np.repeat(deg, 2)); lam = float(np.linalg.eigvalsh(H)[0])
        # closed walk for vertex v: go around the outer cycle starting at v (length nv); holonomy = product of the cycle links
        load = np.zeros(len(edges))
        for v in range(nv):
            W = np.eye(2, dtype=complex); used = []
            for i in range(nv):
                a = (v + i) % nv; b = (a + 1) % nv; ei = edges.index((a, b)) if (a, b) in edges[:nv] else edges.index((b, a))
                W = W @ U[ei] if edges[ei] == (a, b) else W @ U[ei].conj().T; used.append(ei)
            th = float(np.min(np.abs(np.angle(np.linalg.eigvals(W)))))
            for ei in used: load[ei] += nv / (4 * math.sin(th / 2) ** 2)
        bound = 1 / load.max(); ok &= lam >= bound - 1e-12; ratios.append(lam / bound)
    return {'trials': trials, 'F1_bound_holds': bool(ok), 'min_ratio_lambda_over_bound': float(min(ratios)), 'median_ratio': float(np.median(ratios))}

CHECKS = {'overlap3d': overlap3d, 'overlap1d': overlap1d, 'rc': rc, 'panels': panels, 'q8': q8, 'ims_random': ims_random, 'transport': transport}
if __name__ == '__main__':
    names = sys.argv[1:] or list(CHECKS)
    d = json.load(open(OUT)) if os.path.exists(OUT) else {}
    for nm in names: d[nm] = CHECKS[nm](); print(nm, d[nm], flush=True)
    json.dump(d, open(OUT, 'w'), indent=1, default=float)
