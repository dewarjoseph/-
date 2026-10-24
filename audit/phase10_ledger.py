#!/usr/bin/env python3
"""Phase X: machine-readable ledger -> audit/results/phase10_ledger.json (numbers read from the result files).

1. bounds: every quoted bound on an infinite-volume floor E_*(r) = inf sigma(H_Y), Y in Omega_r (H = 24 - A_U), or on a Z^3 floor,
   with ONE label: rigorous (proof, or computer-assisted with exact arithmetic or a rigorous rounding bound), fv_certificate
   (rigorous about a finite matrix only), numerical (floating point), conjectural (rests on an unproved hypothesis).
2. claims: each with a status (proved / certified / empirical / conjectural / falsified / pending) and a novelty category
   (1 established mathematics, 2 new computation or application, 3 potential mathematical novelty, 4 physical conjecture).
Usage: python -u -I audit/phase10_ledger.py [commit]"""
import os, sys, json, subprocess
from fractions import Fraction
HERE = os.path.dirname(os.path.abspath(__file__)); RES = os.path.join(HERE, 'results'); ROOT = os.path.join(HERE, '..')
def J(n):
    p = os.path.join(RES, n); return json.load(open(p)) if os.path.exists(p) else None
def JL(n):
    p = os.path.join(RES, n); return [json.loads(l) for l in open(p)] if os.path.exists(p) else []
def git(*a):
    try: return subprocess.run(['git', *a], cwd=ROOT, capture_output=True, text=True).stdout.strip()
    except Exception: return None
T = 'python -m pytest -q tests/test_phase10.py'
p7, ch5, cert, y5 = J('phase7_ims.json'), J('phase8_chain_m5.json'), {r['class']: r for r in JL('phase10_certify.jsonl')}, {r['class']: r for r in JL('phase10_y5.jsonl')}
ims = JL('phase10_ims.jsonl'); z3, sh, hier, prom, imp, impf = J('phase10_z3_pairs.json'), J('phase10_shadows.json'), J('phase10_hierarchy.json'), J('phase10_stageB_promotion.json'), J('phase10_improper_top.json'), J('phase10_improper_f1.json')
def ims_rec(dec, R): return next((r for r in reversed(ims) if r['class'] == dec and r['R'] == R and r.get('all_balls_certified')), None)

bounds = []
if p7 and ch5:
    bounds += [{'rule': 'FR30 (class 1386)', 'quantity': 'E_*', 'direction': '>=', 'value': float(Fraction(p7['12']['L_R_certified'])), 'label': 'rigorous', 'source': 'Phase VII (phase7_ims.json, R = 12)'},
               {'rule': 'FR30 (class 1386)', 'quantity': 'E_*', 'direction': '<=', 'value': ch5['rayleigh_upper'], 'exact': ch5['rayleigh_upper_exact'], 'label': 'rigorous', 'source': 'Phase VIII (phase8_chain_m5.json)'}]
for R in (8, 12, 14):
    r = ims_rec(1387, R)
    if r: bounds.append({'rule': 'class 1387', 'quantity': 'E_*', 'direction': '>=', 'value': r['Lambda_R_certified'], 'label': 'rigorous',
                         'statement': f"Theorem X.7 at R = {R}: {r['distinct_balls']} legal balls ({r['one_star_types']} Phi-closed 1-star types), each certified by a Higham-bounded Cholesky at mu = {r['mu']}" + (' (prescribed-mu mode)' if r.get('mode') else ''),
                         'artifact': 'audit/results/phase10_ims.jsonl', 'regenerate': f"python -u -I audit/phase10_ims.py 1387 {R} {r['m']} <nproc>" + (f" {r.get('mu_float', '')}" if r.get('mode') else '')})
if 1387 in y5 and y5[1387].get('Y5_upper'):
    bounds.append({'rule': 'class 1387', 'quantity': 'E_*', 'direction': '<=', 'value': y5[1387]['Y5_upper'], 'exact': y5[1387]['Y5_upper_exact'], 'label': 'rigorous',
                   'statement': 'exact rational Rayleigh quotient of an integer vector on the pinned level-5 supertile (a legal patch; compression)', 'artifact': 'audit/results/phase10_y5.jsonl'})
if cert:
    lo = min(r['certified_lower'] for r in cert.values())
    bounds.append({'rule': 'every proper Chair44 rule (all 1098 classes)', 'quantity': 'E_*', 'direction': '>=', 'value': lo, 'label': 'rigorous',
                   'statement': 'Theorem X.2: E_* >= lambda_min H_free(T_3), Higham-certified Cholesky, per class; with the exact Y4 Rayleigh upper bound per class', 'artifact': 'audit/results/phase10_certify.jsonl'})
if z3 and 'certificate_v2' in z3:
    v = z3['certificate_v2']
    bounds += [{'rule': 'Z^3 connection A (period 2)', 'quantity': 'E_*', 'direction': '<=', 'value': v['E_low_upper'], 'exact': v['E_low_upper_exact'], 'label': 'rigorous', 'artifact': 'audit/results/phase10_z3_pairs.json'},
               {'rule': 'Z^3 connection B (period 2)', 'quantity': 'E_*', 'direction': '>=', 'value': v['E_high_lower_free_cell'], 'label': 'rigorous', 'statement': 'free 2x2x2 cell (bracketing), Higham-certified', 'artifact': 'audit/results/phase10_z3_pairs.json'}]
if sh:
    for d, rec in sh.items():
        for k, v in rec.items():
            u = [x for x in v if x.endswith('_upper')]
            if u: bounds.append({'rule': f'Abelian shadow {k} o U of decoration {d}', 'quantity': 'E_*', 'direction': '<=', 'value': v[u[0]], 'exact': v[u[0] + '_exact'], 'label': 'rigorous', 'artifact': 'audit/results/phase10_shadows.json'})
if prom:
    for r in prom['rows']:
        bounds.append({'rule': f"class {r['class']}", 'quantity': 'E_*', 'value': r['baseline_estimate'], 'label': 'conjectural', 'statement': 'last-ratio geometric-tail extrapolation from Y4, Y5, Y6 (unproved ratio hypothesis)', 'artifact': 'audit/results/phase10_stageB_promotion.json'})

claims = [
 {'id': 'X1-flatness', 'status': 'proved', 'category': 1, 'statement': 'SU(2) links on a connected finite graph: flat <=> gauge-trivial <=> lambda_min(H_U) = 0', 'tests': [T + ' -k pauli']},
 {'id': 'X2-bracketing', 'status': 'proved', 'category': '1 (method) / 2 (application)', 'statement': 'F_k(r) <= E_*(r) <= Y_L(r) for every decoration (lower side without recognizability or minimality)', 'tests': [T + ' -k bracketing']},
 {'id': 'X3-positivity', 'status': 'proved + census certified', 'category': '1/2', 'statement': 'E_*(r) > 0 <=> some T_k(r) is not flat; all 1098 proper classes have primitive frame substitutions and E_* >= 3.788 (certified)',
  'evidence': {'certified_lower_min': min(r['certified_lower'] for r in cert.values()) if cert else None, 'improper_flatness': impf}},
 {'id': 'X4-no-go', 'status': 'proved', 'category': '1 (mechanism) / 2 (explicit family)', 'statement': 'no lower bound on E_* from plaquette class frequencies: flat islands on Z^3, non-trivial fraction >= 0.78, E_* <= 6(1 - cos(pi/(R+1)))', 'tests': [T + ' -k no_go']},
 {'id': 'X5-insufficiency', 'status': 'proved + certified (infinite volume)', 'category': 2, 'statement': 'two period-2 Pauli-frame connections on Z^3 with identical plaquette trace fields and certified different floors (separation >= 0.18)',
  'evidence': z3.get('certificate_v2') if z3 else None, 'tests': [T + ' -k z3_trace']},
 {'id': 'X6-2D-abelian', 'status': 'proved', 'category': 1, 'statement': 'Pauli-frame connections are Z4-valued (Abelian) in two dimensions'},
 {'id': 'X7-localization', 'status': 'proved (Phase VII Thm 7.1 generalized; completeness via the Phi-closure)', 'category': '1 (machinery) / 2', 'statement': 'Lambda_R(r) <= E_*(r) <= D_R(r), D_R - Lambda_R = O(R^-2), for every decoration with a primitive frame substitution', 'tests': [T + ' -k ims']},
 {'id': 'D1-fr30-not-optimal-finite', 'status': 'certified at finite volume (fv_certificate) and numerical', 'category': 2, 'statement': 'class 1387 (FR30 with the centre child reframed) exceeds FR30 at levels 3, 4, 5',
  'evidence': {c: {k: y5[c].get(k) for k in ('Y5', 'Y5_upper')} for c in (1386, 1387) if c in y5}},
 {'id': 'D2-1387-above-fr30-infinite', 'status': 'certified' if (ims_rec(1387, 14) and ch5 and ims_rec(1387, 14)['Lambda_R_certified'] > ch5['rayleigh_upper']) else 'pending or not established',
  'category': 2, 'statement': 'E_*(1387) >= Lambda_14(1387) > 8.7642270381 >= E_*(FR30)', 'evidence': ims_rec(1387, 14)},
 {'id': 'S1-stageB-promotion', 'status': 'computed', 'category': 2, 'statement': 'registered promotion checks for the deep-stage classes', 'evidence': prom},
 {'id': 'S2-improper-extension', 'status': 'computed (numerical)', 'category': 2, 'statement': 'stage C: improper frames (6^8 decorations), controlled baseline = the proper census', 'evidence': imp and imp.get('top10_distinct')},
 {'id': 'H1-hierarchy', 'status': (hier or {}).get('decision', 'pending'), 'category': 2, 'statement': 'Part V pre-registered test: hierarchy descriptors vs local descriptors, held-out gauge classes, Y4 and Y5', 'evidence': hier and {t: {l: {k: hier[t][l][k] for k in ('rmse', 'gain_ci95')} for l in ('ols', 'hgb')} for t in ('Y4', 'Y5_sample')}},
 {'id': 'N1-kamenetsky', 'status': 'falsified (novelty)', 'category': 2, 'statement': 'Phase VII Thm 6.2 (radius-1 matching rule for FR30) is Kamenetsky Thm A (arXiv:2610.00916) for his assignment frames30 = FR30; Phase IX category C corrected to 2'},
 {'id': 'P1-physics', 'status': 'none claimed', 'category': 4, 'statement': 'no physical law, quantum mechanics, Standard Model or mass spectrum follows from a positive spectral floor'},
]
out = {'commit': sys.argv[1] if len(sys.argv) > 1 else git('rev-parse', '--short', 'HEAD'), 'branch': git('rev-parse', '--abbrev-ref', 'HEAD'), 'report': 'deliverables/PHASE10_REPORT.md', 'bounds': bounds, 'claims': claims}
json.dump(out, open(os.path.join(RES, 'phase10_ledger.json'), 'w'), indent=1, default=float); print(f"{len(bounds)} bounds, {len(claims)} claims")
