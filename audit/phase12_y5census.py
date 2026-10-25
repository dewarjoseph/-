#!/usr/bin/env python3
"""Phase XII, Part VIII: the target of the preregistered predictive study (phase12_preregistration.json): exact level-5 upper
bounds Y5 for the representative of every one of the 1098 proper gauge classes (phase11_frontier.upper_job), recomputing the
222 Phase X values as a cross-check.  Usage: python -u -I audit/phase12_y5census.py [nproc] -> audit/results/phase12_y5_census.jsonl"""
import os, sys, json, time, types
sys.modules.setdefault('resource', types.SimpleNamespace(getrusage=lambda *a: types.SimpleNamespace(ru_maxrss=0), RUSAGE_SELF=0))
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); RES = os.path.join(HERE, 'results')
import phase11_chair as C, phase11_frontier as F
OUT = os.path.join(RES, 'phase12_y5_census.jsonl')
if __name__ == '__main__':
    os.environ.setdefault('OMP_NUM_THREADS', '1')
    cen = json.load(open(os.path.join(RES, 'phase10_census.json')))['classes']
    done = {json.loads(l)['class'] for l in open(OUT)} if os.path.exists(OUT) else set()
    t0 = time.time()
    for r in cen:
        if r['class'] in done: continue
        j = F.ext_index(C.proper_decoration(r['class'])); t = time.time(); _, lam, num, den = F.upper_job((j, 5))
        rec = {'class': r['class'], 'j': j, 'float': lam, 'upper_num': str(num), 'upper_den': str(den), 'upper': num / den, 'seconds': time.time() - t}
        with open(OUT, 'a') as fh: fh.write(json.dumps(rec) + '\n')
        print(f"[{time.time() - t0:7.0f}s] {rec['class']} {rec['upper']:.7f}", flush=True)
