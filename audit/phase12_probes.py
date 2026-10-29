#!/usr/bin/env python3
"""Phase XII: the sampled radius-R probes of the frontier rules (Phase XI protocol, phase11_chair.probe_lowest_types: the 10 legal
1-star types of lowest U1, 6 random legal centres in each, seed 0, m = 5), one file per rule and radius so that an interrupted
queue resumes: audit/results/phase12_probe_<name>_R<R>.json.  The minimum over the sample is an upper bound on the best radius-R
certificate (report section 2.4 of Phase XI); it is not a certificate.
Usage: python -u -I audit/phase12_probes.py <spec>:<name>:<R,R,...> ..."""
import os, sys, types
os.environ.setdefault('OMP_NUM_THREADS', '1')
sys.modules.setdefault('resource', types.SimpleNamespace(getrusage=lambda *a: types.SimpleNamespace(ru_maxrss=0), RUSAGE_SELF=0))
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); RES = os.path.join(HERE, 'results')
import phase11_chair as C
if __name__ == '__main__':
    for job in sys.argv[1:]:
        spec, name, Rs = job.split(':')
        for R in map(int, Rs.split(',')):
            out = f'phase12_probe_{name}_R{R}.json'
            if os.path.exists(os.path.join(RES, out)): continue
            C.probe_lowest_types(spec, (R,), out, nproc=1); print(spec, R, 'done', flush=True)
