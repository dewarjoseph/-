#!/usr/bin/env python3
"""Phase V-E: provisional level-7 outputs from the newest checkpoint of audit/phase5e_level7_runner.py, for use when the solver
has not reached its 1e-7 residual criterion by the reporting deadline.  Nothing is recomputed except one Rayleigh-Ritz on the
4 lowest Ritz vectors (exact Rayleigh quotients and residuals); the eigenstate statistics use the V-B functions unchanged.
Writes the same file names the converged run writes (phase5e_level7.json, phase5e_fr30_level7_lowest4.npy, ..._weights.npy), with
'converged': false and the checkpoint pass, so a later converged run simply overwrites them.
Usage: python -u -I audit/phase5e_level7_extract.py
"""
import os, sys, json, time
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); RES = os.path.join(HERE, 'results')
import phase5e_level7_runner as R          # installs the resource stub and the phase5e output names
import numpy as np
L7 = R.L7; D = L7.D

def main(level=7):
    nm = L7.names(level); ck = L7.load_newest(nm['ck']); t0 = time.time()
    X = np.ascontiguousarray(ck['X'][:, :4]); th_ck = ck['theta']; res_ck = ck['res']; p = int(ck['pass_']); nmv = int(ck['nmv']); el = float(ck['elapsed'])
    del ck
    geo = D.geometry('fr30', level); del geo['G']
    geo['ea'] = geo['ea'].astype(np.int32); geo['eb'] = geo['eb'].astype(np.int32)
    H = L7.build_H_per_axis(geo, print)
    Q, _ = np.linalg.qr(X); HQ = H @ Q; G = Q.conj().T @ HQ; G = 0.5 * (G + G.conj().T); th, U = np.linalg.eigh(G)
    V = Q @ U; HV = HQ @ U; res = np.array([np.linalg.norm(HV[:, j] - th[j] * V[:, j]) for j in range(4)]); del HQ, HV, Q
    np.save(nm['vec'], V)
    p1 = D.tile_density(V[:, 0], True); p2 = D.tile_density(V[:, 1], True); pg = 0.5 * (p1 + p2); np.save(nm['w'], pg)
    masks = D.interface_masks(geo); st = D.state_stats(pg, geo, masks)
    rec = dict(level=level, n=geo['n'], dim=2 * geo['n'], converged=False, source=f'checkpoint after pass {p} ({nmv} block matvecs, {el:.0f} s solve)',
               tol_criterion=1e-7, eigenvalues=th.tolist(), residuals=res.tolist(), checkpoint_theta=th_ck[:8].tolist(), checkpoint_residuals=res_ck[:8].tolist(),
               kramers_split=float(th[1] - th[0]), gap_to_second_pair=float(th[2] - th[0]), ipr=st['ipr'], ipr_n=st['ipr_n'], P=1 / st['ipr'],
               S2={d: st['S2'][d] for d in range(1, level + 1)}, local_D2=st['local_D2'], interface_weight={d: st['interface_weight'][d] for d in (1, 2, 3)},
               interface_fraction={d: st['interface_fraction'][d] for d in (1, 2, 3)}, boundary_weight=st['boundary_weight'], boundary_fraction=st['boundary_fraction'],
               s50=st['s50'], s90=st['s90'], extract_seconds=time.time() - t0)
    with open(nm['js'], 'w') as f: json.dump(rec, f, indent=1, default=D.conv)
    print(json.dumps({k: v for k, v in rec.items() if k not in ('S2',)}, indent=1, default=D.conv))

if __name__ == '__main__': main()
