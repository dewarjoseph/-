#!/usr/bin/env python3
"""Phase XII, Part V: analysis of the one-child intervention data (phase12_intervention.jsonl).

For every single-child neighbour j of a base b (FR30 = 4752; 4753 in class 1387):
  Delta(R)      Lambda_R(j) - Lambda_R(b) (float), R = 6, 8; sign persistence across R
  DeltaD(R)     D_R(j) - D_R(b) (float): the same intervention seen from the upper (Dirichlet) side
  local         per geometric 1-star configuration (16 shapes, decoration-independent) the worst pinned inflated-1-star energy U1:
                raised / lowered / equal against the base (phase11_mechanism.star_fingerprints); the radius-1 data of phase11_local
  transport     the support-sensitive transport data of Theorem 6.1 (alpha_min, alpha_max, W) against the base
  agreement     sign(Delta(R)) against sign(dU1) and sign(dY5) (preregistered outcome, phase11_frontier_counterfactual_Y5)
  density       the fraction of panels of the pinned supertile T_L (L = 2, 3, 4; tiles identified by position) whose link
                changes under the intervention: why rank-counting (interlacing) cannot bound Delta
Usage: python -u -I audit/phase12_intervention_analysis.py -> audit/results/phase12_intervention_analysis.json
Optional: PHASE12_CACHE=<file> keeps the per-rule local data (shape minima, radius-1 fingerprints, transport data) between runs;
`... precompute` fills it for every rule already in phase12_intervention.jsonl.  The cache only saves time: the values are the
same functions of the rule."""
import os, sys, json, collections, types
sys.modules.setdefault('resource', types.SimpleNamespace(getrusage=lambda *a: types.SimpleNamespace(ru_maxrss=0), RUSAGE_SELF=0))
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); RES = os.path.join(HERE, 'results')
import numpy as np
from scipy import stats
import phase11_chair as C, phase11_frontier as F, phase11_mechanism as M, phase12_transport as Tr
def JL(n): return [json.loads(l) for l in open(os.path.join(RES, n))]
def sgn(x, tol=1e-8): return 0 if abs(x) < tol else (1 if x > 0 else -1)

CACHE = os.environ.get('PHASE12_CACHE'); _C = json.load(open(CACHE)) if CACHE and os.path.exists(CACHE) else {}
def local(spec):
    """per rule: worst inflated 1-star energy U1 per geometric 1-star shape, the radius-1 gauge-class fingerprints, transport data"""
    if spec not in _C:
        fps = M.star_fingerprints(spec); sm = {}
        for r in fps: sm[str(r['shape'])] = min(sm.get(str(r['shape']), 1e9), r['U1'])
        t = Tr.bound(spec)
        _C[spec] = {'shape_minima': sm, 'fpset': sorted({json.dumps([r['shape'], r['fp']], default=str) for r in fps}),
                    'transport': {k: t[k] for k in ('alpha_min', 'alpha_max', 'W', 'bound')}}
        if CACHE: json.dump(_C, open(CACHE, 'w'))
    return _C[spec]
def shape_minima(spec): return local(spec)['shape_minima']
def changed_panel_fraction(base, spec, L):
    import phase9_pair as P9
    def dec_of(s):
        d = C.rule(s); return {'0': d[0], **{v: d[k + 1] for k, v in enumerate(P9.U3)}}
    S0 = P9.build([dec_of(base)] * L); S = P9.build([dec_of(spec)] * L, ref=S0['grid'])
    assert np.array_equal(S['a'], S0['a']) and np.array_equal(S['b'], S0['b'])           # same geometry, same panels
    U0 = P9.links(S0['G'], S0['a'], S0['b'], S0['ax']); U = P9.links(S['G'], S['a'], S['b'], S['ax'])
    return float(np.mean(np.abs(U - U0).reshape(len(U), -1).max(1) > 1e-12))
def fpset(spec): return set(local(spec)['fpset'])

if __name__ == '__main__':
    os.environ.setdefault('OMP_NUM_THREADS', '1')
    rows = JL('phase12_intervention.jsonl'); loc = {r['rule']: r for r in JL('phase11_local_counterfactual.jsonl')}
    if len(sys.argv) > 1 and sys.argv[1] == 'precompute':
        for r in rows:
            if r['R'] == 6: local('x%d' % r['j']); print('cached', r['j'], flush=True)
        sys.exit(0)
    y5 = {r['j']: r['float'] for r in JL('phase11_frontier_counterfactual_Y5.jsonl')}
    lam = collections.defaultdict(dict); dd = collections.defaultdict(dict)
    for r in rows: lam[(r['base'], r['j'])][r['R']] = r['Lambda_float']; dd[(r['base'], r['j'])][r['R']] = r['D_float']
    out = {}
    for base in ('4752', '4753'):
        jb = F.ext_index(C.proper_decoration(int(base))); sb = shape_minima('x%d' % jb); tb = local('x%d' % jb)['transport']
        recs = []
        for r in rows:
            if r['base'] != base or r['R'] != 6 or r['j'] == jb or not r['change'] or r['change']['slot'] is None: continue
            j = r['j']; L = lam[(base, j)]; Lb = lam[(base, jb)]
            sj = shape_minima('x%d' % j); tj = local('x%d' % j)['transport']
            d = {R: L[R] - Lb[R] for R in L if R in Lb}; dD = {R: dd[(base, j)][R] - dd[(base, jb)][R] for R in dd[(base, j)] if R in dd[(base, jb)]}
            raised = sum(sj[s] > sb[s] + 1e-9 for s in sb if s in sj); lowered = sum(sj[s] < sb[s] - 1e-9 for s in sb if s in sj)
            lj = loc.get('x%d' % j, {}); lb_ = loc.get(base, {})
            recs.append({'j': j, 'slot': r['change']['slot'], 'from': r['change']['from'], 'to': r['change']['to'], 'types': r['types'],
                         'Delta': {str(k): v for k, v in d.items()}, 'DeltaD': {str(k): v for k, v in dD.items()}, 'dU1': (lj.get('U1', np.nan) - lb_.get('U1', np.nan)) if lj and lb_ else None,
                         'dY5': y5[j] - y5[jb] if j in y5 and jb in y5 else None, 'shapes_raised': raised, 'shapes_lowered': lowered,
                         'shapes_total': len(sb), 'transport_alpha_min': tj['alpha_min'], 'transport_bound': tj['bound'],
                         'twocycle_flat_types': lj.get('types_without_nontrivial_twocycle'),
                         'radius1_fingerprints_subset_of_base': fpset('x%d' % j) <= fpset('x%d' % jb),
                         'radius1_fingerprints_superset_of_base': fpset('x%d' % j) >= fpset('x%d' % jb),
                         'radius1_fingerprints_shared': len(fpset('x%d' % j) & fpset('x%d' % jb)),
                         'changed_panel_fraction': {str(L): changed_panel_fraction(base, 'x%d' % j, L) for L in (2, 3, 4)}})
        def frac(f):
            v = [f(x) for x in recs]; v = [x for x in v if x is not None]; return (sum(v), len(v))
        both = [x for x in recs if '6' in x['Delta'] and '8' in x['Delta']]
        summary = {'neighbours': len(recs), 'Delta6_positive': sum(x['Delta']['6'] > 1e-8 for x in recs), 'Delta6_negative': sum(x['Delta']['6'] < -1e-8 for x in recs),
                   'DeltaD6_positive': sum(x['DeltaD']['6'] > 1e-8 for x in recs), 'DeltaD6_negative': sum(x['DeltaD']['6'] < -1e-8 for x in recs),
                   'sign_Delta6_eq_sign_DeltaD6': frac(lambda x: sgn(x['Delta']['6']) == sgn(x['DeltaD']['6'])),
                   'Delta8_available': len(both), 'sign_persists_6_to_8': frac(lambda x: sgn(x['Delta']['6']) == sgn(x['Delta']['8']) if x in both else None),
                   'sign_Delta6_eq_sign_dU1': frac(lambda x: sgn(x['Delta']['6']) == sgn(x['dU1']) if x['dU1'] is not None else None),
                   'sign_Delta6_eq_sign_dY5': frac(lambda x: sgn(x['Delta']['6']) == sgn(x['dY5']) if x['dY5'] is not None else None),
                   'sign_Delta6_eq_shape_rule (+1: raised on some shape, lowered on none; -1: lowered on some; 0: unchanged)':
                       frac(lambda x: sgn(x['Delta']['6']) == (-1 if x['shapes_lowered'] > 0 else 1 if x['shapes_raised'] > 0 else 0)),
                   'sign_Delta6_eq_sign_dtransport_bound': frac(lambda x: sgn(x['Delta']['6']) == sgn(x['transport_bound'] - tb['bound'], 1e-12)),
                   'dtransport_bound_zero_while_Delta6_nonzero': sum(sgn(x['transport_bound'] - tb['bound'], 1e-12) == 0 and sgn(x['Delta']['6']) != 0 for x in recs),
                   'A2_hypothesis_holds_at_radius1 (neighbour language subset of base)': sum(x['radius1_fingerprints_subset_of_base'] for x in recs),
                   'neighbours_sharing_no_radius1_environment_with_base': sum(x['radius1_fingerprints_shared'] == 0 for x in recs),
                   'spearman_Delta6_dU1': float(stats.spearmanr([x['Delta']['6'] for x in recs if x['dU1'] is not None], [x['dU1'] for x in recs if x['dU1'] is not None]).statistic),
                   'spearman_Delta6_dY5': float(stats.spearmanr([x['Delta']['6'] for x in recs if x['dY5'] is not None], [x['dY5'] for x in recs if x['dY5'] is not None]).statistic),
                   'changed_panel_fraction_range': {L: [min(x['changed_panel_fraction'][L] for x in recs), max(x['changed_panel_fraction'][L] for x in recs)] for L in ('2', '3', '4')},
                   'spearman_Delta6_DeltaD6': float(stats.spearmanr([x['Delta']['6'] for x in recs], [x['DeltaD']['6'] for x in recs]).statistic),
                   'base': {'Lambda': lam[(base, jb)], 'D': dd[(base, jb)], 'transport_alpha_min': tb['alpha_min'], 'transport_bound': tb['bound']}}
        out[base] = {'summary': summary, 'rows': sorted(recs, key=lambda x: -x['Delta']['6'])}
        print(base, json.dumps(summary, indent=1), flush=True)
    json.dump(out, open(os.path.join(RES, 'phase12_intervention_analysis.json'), 'w'), indent=1)
