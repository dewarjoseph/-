#!/usr/bin/env python3
"""Phase XI, Part II, stage X7: exact level-6 upper bounds (pinned T_6, 262 144 tiles) for the remaining non-orbit survivors.
Usage: python -u -I audit/phase11_y6.py <j> ... -> audit/results/phase11_frontier_X7.jsonl
       python -u -I audit/phase11_y6.py --out=phase11_orbit_Y6.jsonl <j> ...   (the six orbit members: independent level-6 bounds)"""
import os, sys, json, time, types
sys.modules.setdefault('resource', types.SimpleNamespace(getrusage=lambda *a: types.SimpleNamespace(ru_maxrss=0), RUSAGE_SELF=0))
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); RES = os.path.join(HERE, 'results')
import phase11_frontier as F
if __name__ == '__main__':
    args = sys.argv[1:]; out = 'phase11_frontier_X7.jsonl'
    if args and args[0].startswith('--out='): out = args.pop(0)[6:]
    for j in map(int, args):
        t0 = time.time(); _, lam, num, den = F.upper_job((j, 6))
        rec = {'j': j, 'L': 6, 'float': lam, 'upper_num': str(num), 'upper_den': str(den), 'upper': num / den,
               'inferior': num * F.L_REF.denominator < F.L_REF.numerator * den, 'seconds': time.time() - t0}
        print(rec, flush=True)
        with open(os.path.join(RES, out), 'a') as f: f.write(json.dumps(rec) + '\n')
