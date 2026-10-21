"""
Does contact-language closure (few relative contact poses, Kamenetsky's criterion) control the renormalization
spectrum?  For every parity-admissible decoration, |P_0| at level 2 is computed; for all decorations attaining the
minimum (26), the FR30 value (30), and a matched sample with large |P_0|, the type-substitution spectrum is computed.
Run from the repository root:  python3 -u -I audit/phase5_closure_vs_spectrum.py
"""
import os, sys, itertools, collections, io, contextlib
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np, sympy as sp
from independent_clifford_q8_audit import U3, FR30, perm_mat, tiles_at_level
src = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'phase5_universality_types.py')).read()
src = src.split("ACHIRAL = {k: (0, 1, 2) for k in FR30}")[0]
ns = {"__name__": "u", "__file__": os.path.join(os.path.dirname(os.path.abspath(__file__)), 'phase5_universality_types.py')}
exec(compile(src, "universality", "exec"), ns)
analyse, chair_geometry = ns['analyse'], ns['chair_geometry']
perms = list(itertools.permutations(range(3)))
even = [p for p in perms if round(np.linalg.det(perm_mat(p))) == 1]; odd = [p for p in perms if round(np.linalg.det(perm_mat(p))) == -1]
keys = ['0'] + U3
def p0_count(frames, lvl=2):
    tiles = tiles_at_level(frames, lvl); owner = {c: a for a, (_, _, cs) in enumerate(tiles) for c in cs}; poses = set()
    for c, a in owner.items():
        for ax in range(3):
            c2 = (c[0] + (ax == 0), c[1] + (ax == 1), c[2] + (ax == 2)); b = owner.get(c2)
            if b is not None and b != a:
                for u, v in ((a, b), (b, a)):
                    Gu, Tu, _ = tiles[u]; Gv, Tv, _ = tiles[v]
                    poses.add((tuple(map(tuple, Gu.T @ Gv)), tuple(Gu.T @ (Tv - Tu))))
    return len(poses)
rows = []
for combo in itertools.product(*[even if (k == '0' or sum(k) % 2 == 0) else odd for k in keys]):
    fr = dict(zip(keys, combo)); rows.append((p0_count(fr), fr))
hist = collections.Counter(r[0] for r in rows); print("|P0| histogram:", dict(sorted(hist.items())), flush=True)
def spectrum_summary(name, fr):
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf): cpM, cpB, freqs = analyse(name, *chair_geometry(fr))
    lam = sp.Symbol('lambda')
    rootsM = sorted({complex(r) for r in sp.Poly(cpM, lam).all_roots()} if False else set(), key=abs)
    # extract nonzero eigenvalues (as factors) compactly
    facM = [str(f) for f, m in sp.factor_list(cpM)[1] if f != lam]; facB = [str(f) for f, m in sp.factor_list(cpB)[1] if f != lam]
    clean = set(facM) <= {'lambda - 4', 'lambda - 1'} and set(facB) <= {'lambda - 2', 'lambda - 1'}
    print(f"{name}: |P0|={p0_count(fr)}  M-factors={facM}  B-factors={facB}  clean={clean}  f(+1)={freqs['1']} f(-1)={freqs['-1']}", flush=True)
    return clean
for target in (26, 29, 30):
    sel = [fr for p0, fr in rows if p0 == target]
    print(f"\n=== decorations with |P0| = {target}: {len(sel)} ===")
    for i, fr in enumerate(sel): spectrum_summary(f"  |P0|={target} #{i}", fr)
rng = np.random.default_rng(5)
big = [fr for p0, fr in rows if p0 >= 50]; idx = rng.choice(len(big), size=6, replace=False)
print(f"\n=== sample of decorations with |P0| >= 50 (of {len(big)}) ===")
for i in idx: spectrum_summary(f"  large-P0 #{i}", big[i])
mid = [fr for p0, fr in rows if p0 in (36, 37, 38)]; idx = rng.choice(len(mid), size=6, replace=False)
print(f"\n=== sample of decorations with |P0| in 36..38 (of {len(mid)}) ===")
for i in idx: spectrum_summary(f"  mid-P0 #{i}", mid[i])
