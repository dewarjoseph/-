"""Unit tests for audit/phase5b_d_scaling.py: IPR, box-counting S2, interface sets and the own geometry builder on a
tiny level-2 FR30 patch (64 tiles) and on the level-2 cube control.  Runs in a few seconds."""
import os, sys
import numpy as np
import scipy.sparse as sps
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.dirname(HERE)
sys.path.insert(0, os.path.join(ROOT, 'audit'))
import phase5b_d_scaling as D
from independent_clifford_q8_audit import FR30, tiles_at_level, panel_edges

def test_ipr_definitions():
    n = 64
    assert abs(D.IPR(np.full(n, 1.0 / n)) * n - 1.0) < 1e-12          # uniform state: IPR*n = 1
    p = np.zeros(n); p[:5] = 0.2
    assert abs(1.0 / D.IPR(p) - 5.0) < 1e-12                           # uniform on 5 tiles: participation 5

def test_S2_profile_uniform_and_single_child():
    L = 2; n = 8 ** L
    S2 = D.S2_profile(np.full(n, 1.0 / n), L)
    assert np.allclose(S2, [8.0 ** (-d) for d in range(L + 1)])        # uniform: S2(d) = 8^-d, local D2 = 3
    assert np.allclose(D.local_D2(S2), [3.0, 3.0])
    p = np.zeros(n); p[:8] = 1.0 / 8                                   # one depth-1 child (tiles 0..7) uniformly
    S2 = D.S2_profile(p, L)
    assert np.allclose(S2, [1.0, 1.0, 1.0 / 8]) and np.allclose(D.local_D2(S2), [0.0, 3.0])

def test_geometry_matches_object_builder_level2():
    geo = D.geometry('fr30', 2)
    tiles = tiles_at_level(FR30, 2); owner, edges = panel_edges(tiles)
    assert geo['n'] == len(tiles) == 64 and len(geo['ea']) == len(edges)
    Gref = np.array([G for G, _, _ in tiles]); assert (Gref == geo['G']).all()      # same depth-first tile order
    # same multiset of (a, b, axis) panels
    own = sorted(zip(geo['ea'].tolist(), geo['eb'].tolist(), geo['eax'].tolist()))
    ref = sorted((a, b, int(np.argmax(nf))) for a, b, nf, _, _ in edges)
    assert own == ref
    H = D.build_H('fr30', geo)
    val = D.validate_against_objects('fr30', geo, H)
    assert val['max_abs_dev'] == 0.0 and val['degrees_identical'] and val['tile_order_identical']
    assert abs(H - H.getH()).max() == 0.0

def test_interface_sets_level2_brute_force():
    geo = D.geometry('fr30', 2); masks = D.interface_masks(geo); n = geo['n']
    # brute force: depth-1 children are tiles 0-7, 8-15, ...; a tile is in I_1 iff it shares a panel with a tile of another child
    I1 = np.zeros(n, bool)
    for a, b in zip(geo['ea'], geo['eb']):
        if a // 8 != b // 8: I1[a] = I1[b] = True
    assert (masks[1] == I1).all() and int(I1.sum()) == 53                # T_2 = 53 (phase 3 reference)
    assert masks[2].all()                                                # depth 2: every tile has a neighbour in another tile (every tile is its own child)

def test_cube_control_and_trivial_operator():
    geo = D.geometry('cube', 2); assert geo['n'] == 64 and geo['deg'].max() == 6
    H = D.build_H('cube', geo); assert H.shape == (128, 128) and abs(H - H.getH()).max() == 0.0
    geo = D.geometry('trivial', 2); H = D.build_H('trivial', geo)
    assert H.shape == (64, 64) and not np.iscomplexobj(H.data)
    w = np.linalg.eigvalsh(H.toarray()); assert w.min() > 0            # pinned tile operator 24 - A_0 is positive definite
    val = D.validate_against_objects('trivial', geo, H); assert val['max_abs_dev'] == 0.0

def test_dirichlet_box_closed_form():
    b = D.dirichlet_box(3)
    assert abs(b['ipr_n'] - b['ipr_n_closed_form']) < 1e-12 and abs(b['ipr_n'] - 3.375 * (8 / 9) ** 3) < 1e-12
    assert np.allclose(b['S2'][0], 1.0) and all(x > 0 for x in b['local_D2'])

def test_cheb_fsi_level2_against_dense():
    geo = D.geometry('fr30', 2); H = D.build_H('fr30', geo)
    w = np.linalg.eigvalsh(H.toarray())
    th, X, res, nmv, hist = D.cheb_fsi(H, 4, 12, 48.0, tol=1e-9, deg_max=60, log=lambda s: None)
    assert np.abs(th[:4] - w[:4]).max() < 1e-8 and res[:4].max() < 1e-9

if __name__ == '__main__':
    for name, fn in list(globals().items()):
        if name.startswith('test_'): fn(); print('ok', name)
