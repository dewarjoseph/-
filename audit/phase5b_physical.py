#!/usr/bin/env python3
"""Phase V-B, Workstream F: robustness of the FR30 edge and of a distinguishing observable under imperfect links.

Hamiltonian realised: H = sum_tiles 24 |a><a| x I_2 - sum_panels ( |a><b| x C_ab + h.c. ), C_ab in SU(2), i.e. a spin-1/2
(two-orbital) tight-binding model with unit hopping on the chair tiling, with the hopping matrix on each shared unit panel
equal to the Q8 element (sigma.M_a^T n)(sigma.M_b^T n); in a Peierls / synthetic-gauge-field realisation the link C_ab is
the SU(2) phase acquired on the bond.  Observables: lowest eigenvalue of a finite pinned patch (hard wall: on-site energy
24 on every tile, including boundary tiles whose coordination is < 24), its gap to the next Kramers pair, and the lowest
eigenvalue of the free patch (on-site energy = coordination).

Experiments here (all level 4, 4096 tiles, dim 8192, LOBPCG residual <= 1e-7):
  (1) link noise: C_ab -> exp(i eps n_ab . sigma) C_ab with i.i.d. random unit vectors n_ab and fixed eps; the bottom's shift
      and spread over 6 realisations, for FR30 and for the control decoration (census index given), eps in EPS.
  (2) on-site disorder: 24 -> 24 + W u_a, u_a uniform in [-1/2, 1/2]; same protocol.
  (3) boundary: pinned vs free bottom and the boundary weight, to show which observable survives an open boundary.
Everything printed is computed in this run.  Usage: python3 -u -I audit/phase5b_physical.py <control_census_index>
"""
import os, sys, time, json
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
RES = os.path.join(HERE, 'results')
import numpy as np
from independent_clifford_q8_audit import FR30, tiles_at_level, panel_edges
from phase5a_controls import clifford_links, build_H, degrees
from phase5a_scaling_controls import eig_lobpcg
import phase5b_sweep as sw

SIG = [np.array([[0, 1], [1, 0]], complex), np.array([[0, -1j], [1j, 0]], complex), np.array([[1, 0], [0, -1]], complex)]
EPS = [0.0, 0.02, 0.05, 0.1, 0.2]; W = [0.5, 1.0, 2.0]; NREAL = 6; LEVEL = 4

def su2(nvec, eps):
    n = nvec / np.linalg.norm(nvec); return np.cos(eps) * np.eye(2) + 1j * np.sin(eps) * sum(n[k] * SIG[k] for k in range(3))

def lowest(H, k=4):
    lam, V, res, _ = eig_lobpcg(H, 4, extra=2, tol=1e-7)
    return [float(x) for x in lam[:4]], float(max(res[:2])), V[:, 0]

def study(dec, label):
    t0 = time.time(); tiles = tiles_at_level(dec, LEVEL); _, edges = panel_edges(tiles); n = len(tiles); deg = degrees(n, edges)
    links = clifford_links(tiles, edges); out = {'label': label, 'n': n}
    H = build_H(n, edges, links, np.full(n, 24.0)); lam, res, psi = lowest(H)
    p = np.abs(psi[0::2]) ** 2 + np.abs(psi[1::2]) ** 2; p /= p.sum()
    out['pinned'] = {'lambda': lam, 'residual': res, 'gap_pairs': lam[2] - lam[0], 'boundary_weight': float(p[deg < 24].sum())}
    Hf = build_H(n, edges, links, deg.astype(float)); lamf, resf, psif = lowest(Hf)
    pf = np.abs(psif[0::2]) ** 2 + np.abs(psif[1::2]) ** 2; pf /= pf.sum()
    out['free'] = {'lambda': lamf, 'residual': resf, 'boundary_weight': float(pf[deg < 24].sum())}
    print(f"[{label}] pinned {lam[0]:.6f} (gap to next pair {lam[2]-lam[0]:.5f}, bw {out['pinned']['boundary_weight']:.4f}); free {lamf[0]:.6f} (bw {out['free']['boundary_weight']:.3f})  ({time.time()-t0:.0f}s)", flush=True)
    out['link_noise'] = []
    for eps in EPS[1:]:
        vals = []
        for r in range(NREAL):
            rng = np.random.default_rng(1000 * r + int(eps * 1000))
            nl = [su2(rng.normal(size=3), eps) @ C for C in links]
            Hn = build_H(n, edges, nl, np.full(n, 24.0)); l, rs, _ = lowest(Hn); vals.append(l[0])
        out['link_noise'].append({'eps': eps, 'mean': float(np.mean(vals)), 'sd': float(np.std(vals, ddof=1)), 'values': vals})
        print(f"[{label}] link noise eps={eps}: bottom {np.mean(vals):.5f} +- {np.std(vals, ddof=1):.5f} (shift {np.mean(vals)-lam[0]:+.5f})", flush=True)
    out['onsite'] = []
    for w in W:
        vals = []
        for r in range(NREAL):
            rng = np.random.default_rng(5000 * r + int(w * 100)); d = 24.0 + w * (rng.random(n) - 0.5)
            Hd = build_H(n, edges, links, d); l, rs, _ = lowest(Hd); vals.append(l[0])
        out['onsite'].append({'W': w, 'mean': float(np.mean(vals)), 'sd': float(np.std(vals, ddof=1)), 'values': vals})
        print(f"[{label}] on-site disorder W={w}: bottom {np.mean(vals):.5f} +- {np.std(vals, ddof=1):.5f} (shift {np.mean(vals)-lam[0]:+.5f})", flush=True)
    out['seconds'] = time.time() - t0
    return out

if __name__ == '__main__':
    os.environ.setdefault('OMP_NUM_THREADS', '1')
    ctrl = int(sys.argv[1]); res = {'fr30': study(FR30, 'FR30'), f'dec{ctrl}': study(sw.decoration(ctrl), f'control census index {ctrl}')}
    with open(os.path.join(RES, 'phase5b_physical.json'), 'w') as f: json.dump(res, f, indent=1)
    a, b = res['fr30'], res[f'dec{ctrl}']
    print(f"\nDIFFERENCE of pinned bottoms FR30 - control: {a['pinned']['lambda'][0]-b['pinned']['lambda'][0]:+.5f}; "
          f"largest noise sd at eps=0.2: FR30 {a['link_noise'][-1]['sd']:.4f}, control {b['link_noise'][-1]['sd']:.4f}")
