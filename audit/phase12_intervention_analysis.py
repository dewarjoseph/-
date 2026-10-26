#!/usr/bin/env python3
"""Phase XII, Part V: analysis of the one-child intervention data (phase12_intervention.jsonl).

For every single-child neighbour j of a base b (FR30 = 4752; 4753 in class 1387):
  Delta(R)      Lambda_R(j) - Lambda_R(b) (float), R = 6, 8; sign persistence across R
  local         per geometric 1-star configuration (16 shapes, decoration-independent) the worst pinned inflated-1-star energy U1:
                raised / lowered / equal against the base (phase11_mechanism.star_fingerprints); the radius-1 data of phase11_local
  transport     the support-sensitive transport data of Theorem 6.1 (alpha_min, alpha_max, W) against the base
  agreement     sign(Delta(R)) against sign(dU1) and sign(dY5) (preregistered outcome, phase11_frontier_counterfactual_Y5)
Usage: python -u -I audit/phase12_intervention_analysis.py -> audit/results/phase12_intervention_analysis.json"""
import os, sys, json, collections, types
sys.modules.setdefault('resource', types.SimpleNamespace(getrusage=lambda *a: types.SimpleNamespace(ru_maxrss=0), RUSAGE_SELF=0))
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); RES = os.path.join(HERE, 'results')
import numpy as np
from scipy import stats
import phase11_chair as C, phase11_frontier as F, phase11_mechanism as M, phase12_transport as Tr
def JL(n): return [json.loads(l) for l in open(os.path.join(RES, n))]
def sgn(x, tol=1e-8): return 0 if abs(x) < tol else (1 if x > 0 else -1)

_FP = {}
def fingerprints(spec):
    if spec not in _FP: _FP[spec] = M.star_fingerprints(spec)
    return _FP[spec]
def shape_minima(spec):
    out = {}
    for r in fingerprints(spec): out[r['shape']] = min(out.get(r['shape'], 1e9), r['U1'])
    return out
def fpset(spec): return {(r['shape'], r['fp']) for r in fingerprints(spec)}

if __name__ == '__main__':
    os.environ.setdefault('OMP_NUM_THREADS', '1')
    rows = JL('phase12_intervention.jsonl'); loc = {r['rule']: r for r in JL('phase11_local_counterfactual.jsonl')}
    y5 = {r['j']: r['float'] for r in JL('phase11_frontier_counterfactual_Y5.jsonl')}
    lam = collections.defaultdict(dict)
    for r in rows: lam[(r['base'], r['j'])][r['R']] = r['Lambda_float']
    out = {}
    for base in ('4752', '4753'):
        jb = F.ext_index(C.proper_decoration(int(base))); sb = shape_minima('x%d' % jb); tb = Tr.bound('x%d' % jb)
        recs = []
        for r in rows:
            if r['base'] != base or r['R'] != 6 or r['j'] == jb or not r['change'] or r['change']['slot'] is None: continue
            j = r['j']; L = lam[(base, j)]; Lb = lam[(base, jb)]
            sj = shape_minima('x%d' % j); tj = Tr.bound('x%d' % j)
            d = {R: L[R] - Lb[R] for R in L if R in Lb}
            raised = sum(sj[s] > sb[s] + 1e-9 for s in sb if s in sj); lowered = sum(sj[s] < sb[s] - 1e-9 for s in sb if s in sj)
            lj = loc.get('x%d' % j, {}); lb_ = loc.get(base, {})
            recs.append({'j': j, 'slot': r['change']['slot'], 'from': r['change']['from'], 'to': r['change']['to'], 'types': r['types'],
                         'Delta': {str(k): v for k, v in d.items()}, 'dU1': (lj.get('U1', np.nan) - lb_.get('U1', np.nan)) if lj and lb_ else None,
                         'dY5': y5[j] - y5[jb] if j in y5 and jb in y5 else None, 'shapes_raised': raised, 'shapes_lowered': lowered,
                         'shapes_total': len(sb), 'transport_alpha_min': tj['alpha_min'], 'transport_bound': tj['bound'],
                         'twocycle_flat_types': lj.get('types_without_nontrivial_twocycle'),
                         'radius1_fingerprints_subset_of_base': fpset('x%d' % j) <= fpset('x%d' % jb),
                         'radius1_fingerprints_superset_of_base': fpset('x%d' % j) >= fpset('x%d' % jb),
                         'radius1_fingerprints_shared': len(fpset('x%d' % j) & fpset('x%d' % jb))})
        def frac(f):
            v = [f(x) for x in recs]; v = [x for x in v if x is not None]; return (sum(v), len(v))
        both = [x for x in recs if '6' in x['Delta'] and '8' in x['Delta']]
        summary = {'neighbours': len(recs), 'Delta6_positive': sum(x['Delta']['6'] > 1e-8 for x in recs), 'Delta6_negative': sum(x['Delta']['6'] < -1e-8 for x in recs),
                   'Delta8_available': len(both), 'sign_persists_6_to_8': frac(lambda x: sgn(x['Delta']['6']) == sgn(x['Delta']['8']) if x in both else None),
                   'sign_Delta6_eq_sign_dU1': frac(lambda x: sgn(x['Delta']['6']) == sgn(x['dU1']) if x['dU1'] is not None else None),
                   'sign_Delta6_eq_sign_dY5': frac(lambda x: sgn(x['Delta']['6']) == sgn(x['dY5']) if x['dY5'] is not None else None),
                   'Delta6_positive_iff_no_shape_lowered': frac(lambda x: (x['Delta']['6'] > 0) == (x['shapes_lowered'] == 0)),
                   'A2_hypothesis_holds_at_radius1 (neighbour language subset of base)': sum(x['radius1_fingerprints_subset_of_base'] for x in recs),
                   'neighbours_sharing_no_radius1_environment_with_base': sum(x['radius1_fingerprints_shared'] == 0 for x in recs),
                   'spearman_Delta6_dU1': float(stats.spearmanr([x['Delta']['6'] for x in recs if x['dU1'] is not None], [x['dU1'] for x in recs if x['dU1'] is not None]).statistic),
                   'spearman_Delta6_dY5': float(stats.spearmanr([x['Delta']['6'] for x in recs if x['dY5'] is not None], [x['dY5'] for x in recs if x['dY5'] is not None]).statistic),
                   'base': {'Lambda': lam[(base, jb)], 'transport_alpha_min': tb['alpha_min'], 'transport_bound': tb['bound']}}
        out[base] = {'summary': summary, 'rows': sorted(recs, key=lambda x: -x['Delta']['6'])}
        print(base, json.dumps(summary, indent=1), flush=True)
    json.dump(out, open(os.path.join(RES, 'phase12_intervention_analysis.json'), 'w'), indent=1)
