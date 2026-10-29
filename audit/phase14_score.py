#!/usr/bin/env python3
"""Phase XIV: score the frozen predictions of audit/results/phase14_preregistration_dynamical.json against the completed run
audit/results/phase14_dynamical.json -> audit/results/phase14_score.json and audit/results/phase14_ledger.json.

Every verdict is computed here from the stored samples with the preregistered rule; nothing is typed.  Items marked
'not preregistered' are descriptive and carry no verdict.  One extra check (C4, not preregistered): the frame-rule background of
1387 inserted into the Phase XIV matter operator gives back the Phase XII-XIII value Y3(1387).
Usage: python -u -I audit/phase14_score.py"""
import os, sys, json, hashlib, subprocess
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); RES = os.path.join(HERE, 'results')
import numpy as np

PRE = os.path.join(RES, 'phase14_preregistration_dynamical.json')
PRE_SHA = 'da1e379d7112ec1c02bac1d13277ae81a53c548c7edaa1f853099b5d416eb958'
Y3_1387_PREREG = 9.95592

def frame_floors():
    """Y3 of the frame-rule backgrounds, read from the Phase XIII record (spinor block = Chair44 floor)"""
    d = json.load(open(os.path.join(RES, 'phase13_ug_label_extended.json')))
    return {r['rule']: r['floors']['spinor (quaternion form)'] for r in d if r['L'] == 3}

def c4_frame_background(spec='1387'):
    import phase12_unique_games as UG
    from phase14_dynamical import lmat
    n, a, b, U, _, _, _ = UG.game(spec, 3); H = 24.0 * np.eye(4 * n)
    for x, y, u in zip(a, b, U):
        M = lmat(UG.Q[u].astype(float)); H[4 * x:4 * x + 4, 4 * y:4 * y + 4] -= M; H[4 * y:4 * y + 4, 4 * x:4 * x + 4] -= M.T
    return float(np.linalg.eigvalsh(H)[0])

def score(d, y3):
    runs = d['runs']; by = {(r['beta'], r['start']): r for r in runs}
    betas = sorted({r['beta'] for r in runs}); hot = [by[b, 'hot'] for b in betas]; cold = [by[b, 'cold'] for b in betas]
    # C3: beta = 0 link frequencies within 5 % of 1/8, over all 40 configurations (each start)
    f0 = [by[0.0, s]['link_frequencies'] for s in ('hot', 'cold')]
    c3 = {'frequencies': f0, 'passes': all(abs(x - 0.125) <= 0.05 * 0.125 for f in f0 for x in f)}
    def rises(series):
        out = []
        for r0, r1 in zip(series, series[1:]):
            inc = r1['floor_mean'] - r0['floor_mean']; tol = 3 * np.hypot(r0['floor_err'], r1['floor_err'])
            if inc > tol: out.append({'from': r0['beta'], 'to': r1['beta'], 'increase': inc, 'three_se': tol})
        return out
    h1 = rises(hot)
    smax = {b: max(by[b, 'hot']['floor_max'], by[b, 'cold']['floor_max']) for b in betas}
    h2 = [b for b in betas if smax[b] >= y3['1387']]
    drops = [(r0['floor_mean'] - r1['floor_mean'], r0['beta'], r1['beta']) for r0, r1 in zip(hot, hot[1:])]
    prise = [(r1['P_inter'] - r0['P_inter'], r0['beta'], r1['beta']) for r0, r1 in zip(hot, hot[1:])]
    dmax, pmax = max(drops), max(prise); steps = abs(betas.index(dmax[1]) - betas.index(pmax[1]))
    agree = [{'beta': b, 'hot': by[b, 'hot']['floor_mean'], 'cold': by[b, 'cold']['floor_mean'],
              'agree_3se': bool(abs(by[b, 'hot']['floor_mean'] - by[b, 'cold']['floor_mean'])
                                <= 3 * np.hypot(by[b, 'hot']['floor_err'], by[b, 'cold']['floor_err']))} for b in betas]
    inside = {k: [b for b in betas if min(by[b, s]['floor_min'] for s in ('hot', 'cold')) <= v <= smax[b]] for k, v in y3.items()}
    return {
        'C3': c3,
        'H1': {'rule': 'hot series: no increase of <lambda_min> between consecutive betas larger than 3 standard errors',
               'violations': h1, 'holds': not h1},
        'H2': {'rule': 'Y3(1387) exceeds the largest sampled lambda_min at every beta', 'Y3_1387': y3['1387'],
               'largest_sample_per_beta': {str(b): smax[b] for b in betas}, 'betas_violating': h2, 'holds': not h2},
        'H3': {'rule': 'largest hot-series floor drop within one grid step of the largest hot-series <P> rise',
               'largest_floor_drop': {'size': dmax[0], 'from': dmax[1], 'to': dmax[2]},
               'largest_P_rise': {'size': pmax[0], 'from': pmax[1], 'to': pmax[2]}, 'grid_steps_apart': steps, 'holds': steps <= 1},
        'descriptive (not preregistered)': {
            'cold_series_rises_beyond_3se': rises(cold),
            'hot_cold_agreement': agree,
            'betas_where_frame_rule_Y3_lies_inside_the_sampled_range': inside,
            'hot_start_P_inter_at_beta_6': by[6.0, 'hot']['P_inter'], 'cold_start_P_inter_at_beta_6': by[6.0, 'cold']['P_inter']}}

if __name__ == '__main__':
    sha = hashlib.sha256(open(PRE, 'rb').read()).hexdigest(); assert sha == PRE_SHA, 'the preregistration file changed'
    d = json.load(open(os.path.join(RES, 'phase14_dynamical.json'))); y3 = frame_floors()
    assert abs(y3['1387'] - Y3_1387_PREREG) < 1e-5
    c4 = c4_frame_background(); s = score(d, y3)
    s['checks'] = {'C1': {'value': d['checks']['C1_trivial_floor'], 'passes': d['checks']['C1_passes']},
                   'C2': {'max_dev': d['checks']['C2_gauge_covariance_max_dev'], 'passes': d['checks']['C2_passes']},
                   'C3': s.pop('C3'),
                   'C4 (not preregistered)': {'value': c4, 'Y3_1387': y3['1387'], 'passes': abs(c4 - y3['1387']) < 1e-9}}
    s['preregistration_sha256'] = sha; s['frame_rule_Y3'] = y3
    s['label'] = '[E] simulated Monte Carlo ensemble on one finite patch (512 tiles); no continuum, infinite-volume or physical claim'
    json.dump(s, open(os.path.join(RES, 'phase14_score.json'), 'w'), indent=1)
    v = lambda h: 'holds' if s[h]['holds'] else '[F] fails'
    claims = [
        ('XIV.C', 'checks C1-C3 of the frozen protocol pass; C4 (frame-rule background gives Y3(1387)) passes',
         '[C]' if all(c['passes'] for c in s['checks'].values()) else 'failed', 'phase14_score.json:checks', 'test_checks_record, test_c1_c2_live'),
        ('XIV.H1', 'hot-series <lambda_min>(beta) non-increasing within 3 SE', '[E] ' + v('H1'), 'phase14_score.json:H1', 'test_scores_recomputed'),
        ('XIV.H2', 'Y3(1387) exceeds every sampled lambda_min at every beta', '[E] ' + v('H2'), 'phase14_score.json:H2', 'test_scores_recomputed'),
        ('XIV.H3', 'the floor falls fastest where the inter-tile plaquette rises fastest (within one grid step)', '[E] ' + v('H3'), 'phase14_score.json:H3', 'test_scores_recomputed'),
        ('XIV.inf', 'any statement about the infinite hull or a continuum limit', 'not claimed', 'deliverables/PHASE14_REPORT.md section 5', ''),
    ]
    led = {'commit': subprocess.run(['git', 'rev-parse', '--short', 'HEAD'], capture_output=True, text=True, cwd=HERE).stdout.strip(),
           'report': 'deliverables/PHASE14_REPORT.md',
           'claims': [dict(zip(('id', 'statement', 'status', 'evidence', 'test'), c)) for c in claims]}
    json.dump(led, open(os.path.join(RES, 'phase14_ledger.json'), 'w'), indent=1)
    print(json.dumps({k: s[k]['holds'] for k in ('H1', 'H2', 'H3')}), {k: c['passes'] for k, c in s['checks'].items()})
