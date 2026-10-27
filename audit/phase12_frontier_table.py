#!/usr/bin/env python3
"""Phase XII, Part X: the certified frontier table, regenerated from the stored certificates (never from the report).

Rows: every frame rule not proven inferior to the leader, the rules eliminated in Phase XI-XII with the certificate that did it,
and FR30 for reference.  Each endpoint carries its source and its certificate type:
  lower  IMS + Higham banded Cholesky (phase11_cert.jsonl; phase12_independent.jsonl: the independent rerun, and the preregistered
         certificates of this phase, tag prereg_*)
  upper  exact rational Rayleigh quotient on a pinned supertile (phase11_orbit_Y6.jsonl, phase12_y7.jsonl, phase11_fr30_upper.json)
Status against the leader's certified lower bound: leader / contender (intervals overlap) / proven_inferior (U < L_leader).
Printed decimals are rounded outward (lower endpoints down, upper endpoints up), computed exactly from the stored values.
Usage: python -u -I audit/phase12_frontier_table.py -> audit/results/phase12_frontier.json, .csv"""
import os, json, csv, math
from fractions import Fraction
HERE = os.path.dirname(os.path.abspath(__file__)); RES = os.path.join(HERE, 'results')
def JL(n):
    p = os.path.join(RES, n); return [json.loads(l) for l in open(p)] if os.path.exists(p) else []
def outward(x, up, d=7):
    """x (float or Fraction, positive) to d decimals, rounded up (upper bound) or down (lower bound), exactly."""
    q = Fraction(x) * 10 ** d; n = math.ceil(q) if up else math.floor(q)
    return f'{n // 10 ** d}.{n % 10 ** d:0{d}d}'
if __name__ == '__main__':
    cert = {}
    for r in JL('phase11_cert.jsonl'):
        if r.get('all_balls_certified') and (r.get('tag') or '').startswith(('audit_', 'target_')): cert.setdefault(r['rule'], []).append(r)
    ind = {}
    for r in JL('phase12_independent.jsonl'):
        if r.get('all_balls_certified') and (r.get('tag') or '').startswith('independent_'): ind.setdefault(r['rule'], []).append(r)
        if r.get('all_balls_certified') and (r.get('tag') or '').startswith('prereg_'):   # preregistered certificates of this phase
            cert.setdefault(r['rule'], []).append({**r, 'implementation_tag': 'phase12_independent'})
    y7 = {}
    for r in JL('phase12_y7.jsonl'):                                   # least stored level-7 bound of each rule
        q = Fraction(int(r['upper_num']), int(r['upper_den']))
        if r['L'] == 7 and (r['j'] not in y7 or q < y7[r['j']]): y7[r['j']] = q
    p10 = {r.get('extended_index'): r for r in JL('phase10_ims.jsonl') if r.get('extended_index')}
    y6 = {r['j']: r for r in JL('phase11_orbit_Y6.jsonl')}
    fr = json.load(open(os.path.join(RES, 'phase11_fr30_upper.json')))['chain'][-1]
    members = [('1387', 184323, '1387'), ('539311', 539311, 'x539311'), ('1389', 184338, '1389'), ('539291', 539291, 'x539291'),
               ('1391', 184342, '1391'), ('539288', 539288, 'x539288')]
    rows = []
    for name, j, spec in members:
        cs = cert.get(spec, []); best = max(cs, key=lambda r: r['Lambda_R_certified']) if cs else None
        if best: L, Ls = best['Lambda_R_certified'], f"IMS R={best['R']}, {best['distinct_balls']} balls ({best.get('implementation_tag', 'phase11_chair')})"
        else: L, Ls = p10[j]['Lambda_R_certified'], f"IMS R={p10[j]['R']}, {p10[j]['distinct_balls']} balls (Phase X)"
        ind_note = None
        for r in ind.get(spec, []): ind_note = f"independently reproduced: IMS R={r['R']} >= {outward(r['Lambda_R_certified'], False)} (phase12_independent)"
        U = Fraction(int(y6[j]['upper_num']), int(y6[j]['upper_den'])); Us = 'Y6, pinned T6, 262 144 tiles (phase11_orbit_Y6)'
        if j in y7 and y7[j] < U: U, Us = y7[j], 'Y7, pinned T7, 2 097 152 tiles (phase12_y7)'
        rows.append({'rule': name, 'extended_index': j, 'L': L, 'L_source': Ls, 'L_type': 'IMS + Higham banded Cholesky', 'L_independent': ind_note,
                     'U': float(U), 'U_exact': f'{U.numerator}/{U.denominator}', 'U_source': Us,
                     'U_type': 'exact rational Rayleigh quotient'})
    Lmax = max(r['L'] for r in rows); lead = [r for r in rows if r['L'] == Lmax]
    for r in rows:
        r['status'] = 'leader' if r['L'] == Lmax else ('proven_inferior' if Fraction(r['U_exact']) < Fraction(Lmax) else 'contender')
    U5 = Fraction(fr['upper_exact'])
    rows.append({'rule': 'FR30 (1386)', 'extended_index': 184320, 'L': 7.954291278163518, 'L_source': 'IMS R=12, 2315 balls (phase11_chair)',
                 'L_type': 'IMS + Higham banded Cholesky', 'L_independent': None, 'U': float(U5), 'U_exact': fr['upper_exact'],
                 'U_source': 'sigma^5 of the minimising self-loop 1-star type, 884 736 tiles (phase11_fr30_upper)',
                 'U_type': 'exact rational Rayleigh quotient', 'status': 'proven_inferior'})
    out = {'leader': lead[0]['rule'], 'L_leader': Lmax, 'frontier': [r['rule'] for r in rows if r['status'] in ('leader', 'contender')],
           'statement': 'the maximiser of E_* over all 6^8 frame rules is one of the frontier rules (phase11_frontier_summary.json for the '
                        'other 1 679 610 rules; the two eliminations in this table)', 'rows': rows}
    json.dump(out, open(os.path.join(RES, 'phase12_frontier.json'), 'w'), indent=1)
    with open(os.path.join(RES, 'phase12_frontier.csv'), 'w', newline='') as f:
        w = csv.writer(f); w.writerow(['rule', 'L', 'L_source', 'U', 'U_source', 'status', 'L_independent'])
        for r in rows: w.writerow([r['rule'], outward(r['L'], False), r['L_source'], outward(Fraction(r['U_exact']), True), r['U_source'],
                                   r['status'], r['L_independent'] or ''])
    for r in rows: print(f"{r['rule']:>12} [{outward(r['L'], False)}, {outward(Fraction(r['U_exact']), True)}] {r['status']}")
