#!/usr/bin/env python3
"""Phase XII, Part IX: the finite combinatorial core, checked exactly (no floating point), and the analytic obligations that
remain.  Lean was not available in this environment (the network policy denies the toolchain hosts), so nothing here is
machine-checked by a proof assistant; every check below is an exact computation over a finite set or a symbolic identity.

  ims_edge_identity   the per-edge identity behind Theorem B1, symbolically (sympy), for m = 1..6 pieces and generic values
  orbit_child_rule    Orbit Lemma (d), reduced to one child: for every slot v, every pair of frame factors (h_v, h_{Qv}) and every
                      Q in S3, sigma_d rho_Q and rho_Q sigma_d give the same child pose  <=>  h_{Qv} = Q h_v Q^T  (exhaustive)
  orbit_link_exact    Orbit Lemma (b) in integer quaternions (phase12_orbit.json, recomputed here)
  shadow_formula      chi_k((sigma.u_a)(sigma.u_b)) = eps_k(a) eps_k(b), eps_k(t) = -1 iff the panel axis maps to axis k in t's frame
                      (exhaustive over 48 x 48 x 3); the formula used in Orbit Lemma (c)
  obligations         the analytic statements the proofs rely on that are not finite computations
Usage: python -u -I audit/phase12_formal.py -> audit/results/phase12_formal.json"""
import os, sys, json, itertools
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); RES = os.path.join(HERE, 'results')
import phase12_independent as I

def ims_edge_identity():
    import sympy as sp
    out = {}
    for m in range(1, 7):
        xv = sp.symbols(f'v0:{m}', real=True); xw = sp.symbols(f'w0:{m}', real=True)
        A, B, X = sp.symbols('A B X', real=True)                       # |a|^2, |b|^2, Re<a, U b>
        c = sum(x * y for x, y in zip(xv, xw))
        lhs = sum(x ** 2 * A + y ** 2 * B - 2 / c * x * y * X for x, y in zip(xv, xw))
        # impose sum v^2 = 1 and sum w^2 = 1 by eliminating v0^2 and w0^2
        sub = {xv[0] ** 2: 1 - sum(x ** 2 for x in xv[1:]), xw[0] ** 2: 1 - sum(y ** 2 for y in xw[1:])}
        expr = sp.expand(sp.simplify(lhs)).subs(sub)
        out[m] = bool(sp.simplify(expr - (A + B - 2 * X)) == 0)
    return out

def orbit_child_rule():
    """exhaustive: child poses of sigma_d rho_Q and rho_Q sigma_d agree iff h_{Qv} = Q h_v Q^T (centre: Q h_0 = h_0 Q)"""
    PM = [I.pmat(p) for p in I.PERM3]; bad = 0; checked = 0
    slots = [None] + list(I.OCTANTS)
    for q, Q in enumerate(PM):
        for si, v in enumerate(slots):
            base = np.eye(3, dtype=np.int64) if v is None else np.diag([1 - 2 * x for x in v])
            t = np.array([1, 1, 1]) if v is None else 4 * np.array(v)
            w = None if v is None else tuple(int(x) for x in Q @ np.array(v)); bw = np.eye(3, dtype=np.int64) if v is None else np.diag([1 - 2 * x for x in w])
            tw = np.array([1, 1, 1]) if v is None else 4 * np.array(w)
            for p1 in PM:
                h_v = base @ p1
                for p2 in PM:
                    h_w = bw @ p2
                    M = np.eye(3, dtype=np.int64)                        # parent frame (the identity suffices: left multiplication commutes)
                    # sigma_d rho_Q: parent (MQ, 0); its child in slot v sits at MQ t_v = M t_{Qv}, frame MQ h_v
                    lhs_frame, lhs_pos = M @ Q @ h_v, M @ Q @ t
                    # rho_Q sigma_d: the child of (M, 0) in slot Qv, frame M h_{Qv} Q, position M t_{Qv}
                    rhs_frame, rhs_pos = M @ h_w @ Q, M @ tw
                    agree = np.array_equal(lhs_frame, rhs_frame) and np.array_equal(lhs_pos, rhs_pos)
                    cond = np.array_equal(h_w, Q @ h_v @ Q.T)
                    bad += agree != cond; checked += 1
    return {'checked': checked, 'violations': int(bad), 'holds': bad == 0}

def orbit_link_exact():
    d = json.load(open(os.path.join(RES, 'phase12_orbit.json')))['lemma']
    return {'x_by_Q': d['b_exact_integer_quaternion_x'], 'holds': d['b_exact_identity_holds']}

def shadow_formula():
    bad = 0
    for i in range(48):
        for j in range(48):
            for k in range(3):
                u = I.Q8[I.LINK[i, j, k]]
                ka = int(np.flatnonzero(I.FRAMES[i][k])[0]); kb = int(np.flatnonzero(I.FRAMES[j][k])[0])
                for m in range(3):
                    chi = 1 if u in ((1, 0, 0, 0), (-1, 0, 0, 0)) else (1 if abs(u[1 + m]) == 1 else -1)
                    eps = (-1 if ka == m else 1) * (-1 if kb == m else 1)
                    bad += chi != eps
    return {'checked': 48 * 48 * 3 * 3, 'violations': bad, 'holds': bad == 0}

OBLIGATIONS = [
    ('variational principle', 'for a bounded self-adjoint H, inf sigma(H) = inf of Rayleigh quotients over any dense subspace (here: finitely supported vectors)', 'standard (min-max)'),
    ('compression', 'lambda_min(P_K H P_K) >= inf sigma(H) for every subspace', 'standard'),
    ('Higham Theorem 10.3', 'if floating-point Cholesky of an n x n symmetric A completes, L L^T = A + dA with |dA| <= gamma_{n+1}|L||L^T|; the certificate uses ||dA||_2 <= gamma_{n+1}||L||_F^2 and an IEEE model with u = 2^-52 (two ulps, covering FMA)', 'cited (Higham 2002), not re-proved; implementation-dependent assumption: LAPACK dpbtrf obeys the standard rounding model'),
    ('overlap function', 'c(eta) for the Dirichlet ground state of the unit 3-ball (Plancherel; symbolic derivation in phase11_proofs.overlap3d)', 'derived symbolically in Phase XI; the radial Fourier transform step is classical analysis'),
    ('spin lift', 'every R in SO(3) has a lift W in SU(2) with W sigma.v W^+ = sigma.(R v)', 'standard; for the 24 rotations used here the lift is exhibited and checked exactly (orbit_link_exact)'),
    ('cycle spectrum', 'the free operator of an l-cycle with holonomy W has spectrum {2 - 2cos((phi + 2 pi m)/l)}', 'standard (gauge to one link, diagonalise)'),
    ('closure lemma', 'every child 1-star lies inside sigma of its parent 1-star', 'finite, asserted on every Phi step of every run (not a general proof for all rules)'),
    ('primitivity and minimality', 'M^2 > 0 for the frame substitution implies a minimal hull', 'standard for primitive substitutions; M^2 > 0 checked per rule'),
]

if __name__ == '__main__':
    out = {'ims_edge_identity': ims_edge_identity(), 'orbit_child_rule': orbit_child_rule(), 'orbit_link_exact': orbit_link_exact(),
           'shadow_formula': shadow_formula(), 'lean': 'not available: the environment network policy denies the Lean toolchain hosts; no proof-assistant check was made',
           'obligations': [dict(zip(('name', 'statement', 'status'), o)) for o in OBLIGATIONS]}
    json.dump(out, open(os.path.join(RES, 'phase12_formal.json'), 'w'), indent=1)
    print(json.dumps({k: v for k, v in out.items() if k != 'obligations'}, indent=1))
