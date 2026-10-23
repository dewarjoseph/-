#!/usr/bin/env python3
"""Phase VI ablation: is the non-Abelian (Q8) structure needed for the spectral floor?  Reflection-only frames (all permutation
parts = identity, so M_a = product of octant reflections D_s(v) along the hierarchy) give links in {+1, -1} (an Abelian Z2 gauge
field, i.e. Toulouse-type sign frustration).  Pinned (24 - A) and free (Deg - A) bottoms for FR30, reflection-only and trivial
links on the same chair graph, levels 2..5.  Usage: python -u -I audit/phase6_z2_ablation.py -> audit/results/phase6_z2_ablation.json"""
import os, sys, json, time
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); RES = os.path.join(HERE, 'results')
import numpy as np, scipy.sparse.linalg as spl
import phase6_gauge_audit as G
REFL = {'0': (0, 1, 2)}; REFL.update({v: (0, 1, 2) for v in G.U3})
def bottoms(frames, level, trivial=False):
    tl = G.tiles(frames, level); pn = G.panels(tl); n = len(tl)
    links = [G.I2 if trivial else G.link(tl[a][0], tl[b][0], k) for a, b, k, _ in pn]
    deg = np.zeros(n)
    for a, b, k, _ in pn: deg[a] += 1; deg[b] += 1
    out = {}
    for name, diag in (('pinned', np.full(n, 24.0)), ('free', deg)):
        H = G.operator(tl, pn, links, diag)
        if n <= 600: w = np.linalg.eigvalsh(H.toarray())[:2]
        else: w = np.sort(spl.eigsh(H.tocsc(), k=2, sigma=-1e-2, which='LM', tol=1e-10, return_eigenvectors=False))
        out[name] = float(w[0])
    out['abelian'] = all(abs(abs(np.trace(C).real) - 2) < 1e-9 for C in links)
    out['minus_one_link_fraction'] = float(np.mean([np.trace(C).real < -1.5 for C in links]))
    return out
res = {}
for L in (2, 3, 4):                                                 # level 5 exceeded the 50-min budget (shift-invert LU, 3 systems)
    t0 = time.time(); res[L] = {'fr30': bottoms(G.FR30, L), 'reflection_only_Z2': bottoms(REFL, L), 'trivial': bottoms(G.FR30, L, trivial=True)}
    print(L, json.dumps(res[L]), f'{time.time()-t0:.0f}s', flush=True)
# exact certificate: E_inf(Z2) <= E_4(Z2) (Theorem E6: the reflection-only rule is a substitution with identical child blocks) and
# E_4(Z2) <= <p, H p>/<p, p> for p = round(2^24 psi) (integer arithmetic; H has integer entries for +-1 links)
tl = G.tiles(REFL, 4); pn = G.panels(tl); n = len(tl); links = [G.link(tl[a][0], tl[b][0], k) for a, b, k, _ in pn]
H = G.operator(tl, pn, links, np.full(n, 24.0)).tocsr(); w, V = spl.eigsh(H.tocsc(), k=2, sigma=-1e-2, which='LM', tol=1e-12)
psi = V[:, np.argmin(w)]; psi = psi * np.exp(-1j * np.angle(psi[np.argmax(np.abs(psi))]))
Hr = np.rint(H.toarray().real).astype(np.int64); Hi = np.rint(H.toarray().imag).astype(np.int64); assert np.abs(H.toarray().imag).max() < 1e-12
S = 2 ** 24; pr = [int(x) for x in np.rint(psi.real * S)]; pim = [int(x) for x in np.rint(psi.imag * S)]
from fractions import Fraction
Hpr = Hr @ np.array(pr, dtype=object); Hpi = Hr @ np.array(pim, dtype=object)
num = sum(a * b for a, b in zip(pr, Hpr)) + sum(a * b for a, b in zip(pim, Hpi)); den = sum(a * a for a in pr) + sum(a * a for a in pim)
q = Fraction(int(num), int(den)); res['z2_level4_certified_upper'] = {'numerator': str(q.numerator), 'denominator': str(q.denominator), 'value': float(q), 'float_eig': float(min(w))}
print('certified: E_inf(Z2) <= E_4(Z2) <=', q.numerator, '/', q.denominator, '=', float(q), flush=True)
json.dump(res, open(os.path.join(RES, 'phase6_z2_ablation.json'), 'w'), indent=1)
