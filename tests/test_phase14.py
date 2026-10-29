"""Phase XIV: the Chair44 matter floor in a dynamical Q8 gauge ensemble ([E], simulated).  The preregistration is checked
unchanged, the stored scores are recomputed from the stored samples, and the operator checks C1, C2 are rerun live."""
import os, sys, json, hashlib
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__)); AUD = os.path.join(HERE, '..', 'audit'); RES = os.path.join(AUD, 'results')
sys.path.insert(0, AUD)
import phase14_score as S

def J(name): return json.load(open(os.path.join(RES, name)))

def test_preregistration_unchanged():
    assert hashlib.sha256(open(S.PRE, 'rb').read()).hexdigest() == S.PRE_SHA

def test_run_matches_protocol():
    pre, d = J('phase14_preregistration_dynamical.json'), J('phase14_dynamical.json')
    got = sorted((r['beta'], r['start'], r['seed']) for r in d['runs'])
    assert got == sorted((b, s, 0 if s == 'hot' else 1) for b in pre['run']['betas'] for s in ('hot', 'cold'))
    assert all(len(r['floors']) == 40 for r in d['runs'])
    for r in d['runs']:
        assert abs(np.mean(r['floors']) - r['floor_mean']) < 1e-12 and min(r['floors']) == r['floor_min'] and max(r['floors']) == r['floor_max']

def test_checks_record():
    s = J('phase14_score.json')
    assert all(c['passes'] for c in s['checks'].values())
    assert abs(s['checks']['C1']['value'] - 1.66951) < 1e-5 and abs(s['checks']['C4 (not preregistered)']['value'] - 9.95592) < 1e-5

def test_scores_recomputed():
    """the verdicts follow from the stored samples by the preregistered rules: H1 and H2 fail, H3 holds"""
    s = S.score(J('phase14_dynamical.json'), S.frame_floors()); stored = J('phase14_score.json')
    for h in ('H1', 'H2', 'H3'): assert s[h]['holds'] == stored[h]['holds']
    assert not s['H1']['holds'] and not s['H2']['holds'] and s['H3']['holds']
    assert s['H2']['betas_violating'] == [0.0, 0.25, 0.5, 0.75, 1.0, 1.25]
    assert s['descriptive (not preregistered)']['cold_series_rises_beyond_3se'] == []

def test_c1_c2_live():
    import phase14_dynamical as D
    ck, hull = D.checks()
    assert ck['C1_passes'] and ck['C2_passes'] and ck['dynamical_links'] == 5376 and ck['tiles'] == 512
