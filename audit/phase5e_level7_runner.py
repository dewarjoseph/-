#!/usr/bin/env python3
"""Phase V-E: portable runner for the EXISTING Phase V-B level-7 FR30 solver (audit/phase5b_d_level7.py), unchanged.

The solver itself (operator, Chebyshev filter, Rayleigh-Ritz, tolerance 1e-7, block 16, K = 4, seed 7) is imported and run
as is.  This wrapper changes only three environment details, none of which touches a definition:
  1. a stub for the Unix-only `resource` module (peak RSS is then reported as 0 on Windows; psutil is used if present);
  2. the checkpoint directory (the V-B path was a /tmp directory of a Linux session that no longer exists);
  3. the output names: phase5e_level7*.{log,json,npy} instead of phase5b_d_level7*, so the frozen V-B log is not appended to.
Usage (repository root):
  python -u -I audit/phase5e_level7_runner.py run 7 [--resume]
  python -u -I audit/phase5e_level7_runner.py certify 7
  python -u -I audit/phase5e_level7_runner.py run 5          # validation run (compares with the stored V-B level-5 value)
Checkpoints: <repo>/.ckpt_phase5e_level7/ (git-ignored; about 1 GB per generation at level 7).
"""
import os, sys, types
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
try:
    import resource  # noqa: F401
except ImportError:
    def _rss():
        try:
            import psutil; return types.SimpleNamespace(ru_maxrss=psutil.Process().memory_info().peak_wset / 1e3)
        except Exception: return types.SimpleNamespace(ru_maxrss=0)
    sys.modules['resource'] = types.SimpleNamespace(getrusage=lambda *a: _rss(), RUSAGE_SELF=0)
import phase5b_d_level7 as L7

L7.CKDIR = os.path.join(os.path.dirname(HERE), '.ckpt_phase5e_level7')
_names = L7.names
def names(level):
    nm = _names(level)
    return {k: ([p.replace('phase5b_d_', 'phase5e_') for p in v] if isinstance(v, list) else v.replace('phase5b_d_', 'phase5e_'))
            for k, v in nm.items()}
L7.names = names

if __name__ == '__main__':
    import argparse
    ap = argparse.ArgumentParser(); ap.add_argument('cmd'); ap.add_argument('level', type=int); ap.add_argument('--resume', action='store_true')
    ap.add_argument('--tol', type=float, default=1e-7); ap.add_argument('--block', type=int, default=16); ap.add_argument('--K', type=int, default=4)
    a = ap.parse_args()
    if a.cmd == 'run': L7.run(a.level, a.resume, a.tol, a.block, a.K)
    elif a.cmd == 'certify': L7.certify(a.level)
    else: raise SystemExit(__doc__)
