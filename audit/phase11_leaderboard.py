#!/usr/bin/env python3
"""Phase XI, Part II: the rigorous interval leaderboard of the 1098 proper gauge classes, plus the leading extended decorations.

For every class r: L_r = max of the certified lower bounds available (free level-3 bound, Phase X and Phase XI localization
certificates), U_r = min of the exact upper bounds available (Y4 exact, Y5 exact, Y6 exact (Phase X artifact), D_R exact).
Every bound carries its source and certificate type.  Classification against the leader (the class with the largest L):
  proven_inferior   U_r < L_best
  contender         intervals overlap (U_r >= L_best) and the class is not the leader
  proven_superior   L_r > U_reference  (with reference = the leader; none expected)
Usage: python -u -I audit/phase11_leaderboard.py -> audit/results/phase11_leaderboard.json / .csv"""
import os, sys, json, csv
from fractions import Fraction
HERE = os.path.dirname(os.path.abspath(__file__)); RES = os.path.join(HERE, 'results')
def J(n, d=None):
    p = os.path.join(RES, n); return json.load(open(p)) if os.path.exists(p) else d
def JL(n):
    p = os.path.join(RES, n); return [json.loads(l) for l in open(p)] if os.path.exists(p) else []

def main():
    cen = J('phase10_census.json')['classes']; members = {r['class']: r['members'] for r in cen}
    rep_of = {m: r for r, ms in members.items() for m in ms}
    lo, up = {}, {}
    def add_lo(c, v, src, kind):
        if v is None: return
        lo.setdefault(c, []).append({'value': float(v), 'source': src, 'type': kind})
    def add_up(c, v, src, kind, exact=None):
        if v is None: return
        up.setdefault(c, []).append({'value': float(v), 'source': src, 'type': kind, **({'exact': exact} if exact else {})})
    # Phase X brackets
    for r in JL('phase10_certify.jsonl'):
        c = r.get('class'); add_lo(c, r.get('F3_certified', r.get('lower')), 'phase10_certify F3', 'Higham Cholesky (free T3)')
        add_up(c, r.get('Y4_upper', r.get('upper')), 'phase10_certify Y4', 'exact rational Rayleigh')
    for r in JL('phase10_y5.jsonl'):
        add_up(r.get('class'), r.get('Y5_upper'), 'phase10_y5', 'exact rational Rayleigh')
    for r in JL('phase10_deep.jsonl'):
        add_up(r.get('class'), r.get('Y6_upper'), 'phase10_deep Y6 (artifact; vector not stored)', 'exact rational Rayleigh', r.get('Y6_upper_exact'))
    for r in JL('phase10_ims.jsonl'):
        if r.get('class') is None: continue
        c = rep_of.get(r['class'], r['class'])
        add_lo(c, r.get('Lambda_R_certified'), f"phase10_ims R={r['R']}", 'IMS + Higham (GPU or CPU dense)')
        add_up(c, r.get('D_R_upper', r.get('D_R_float') if False else None), f"phase10_ims D_R={r['R']}", 'exact rational Rayleigh')
    fr = 1386
    add_up(fr, 8.764227038115036, 'phase8_chain_m5 (artifact; vector not stored)', 'exact rational Rayleigh', '95969095435322528/10950092349041091')
    add_lo(fr, 7.954292264597248, 'phase7 IMS R=12', 'IMS + Higham')
    # Phase XI independent bounds
    cen11 = J('phase11_frontier_census.json', {}).get('rows', [])
    for r in cen11:
        add_lo(r['class'], r['F3_certified'], 'phase11 census F3 (independent)', 'Higham banded Cholesky (free T3)')
        add_up(r['class'], r['Y4_upper'], 'phase11 census Y4 (independent)', 'exact rational Rayleigh', f"{r['Y4_num']}/{r['Y4_den']}")
    for r in JL('phase11_cert.jsonl'):
        if not (r.get('tag') or '').startswith(('audit_', 'target_')) or r['rule'].startswith('x') or not r.get('all_balls_certified'): continue
        c = rep_of.get(int(r['rule']), int(r['rule']))
        add_lo(c, r['Lambda_R_certified'], f"phase11 IMS R={r['R']} ({r['distinct_balls']} balls, independent)", 'IMS + Higham banded Cholesky')
    import phase11_frontier as F
    import phase11_chair as C
    ext2cls = {}
    for c, ms in members.items():
        for mm in ms: ext2cls[F.ext_index(C.proper_decoration(mm))] = c
    for name in ('twins_Y5', 'counterfactual_Y5', 'X5'):
        for r in JL(f'phase11_frontier_{name}.jsonl'):
            c = ext2cls.get(r['j'])
            if c is not None: add_up(c, r['upper'], f'phase11 {name} (independent)', 'exact rational Rayleigh', f"{r['upper_num']}/{r['upper_den']}")
    rows = []
    for c in members:
        L = max(lo.get(c, [{'value': 0.0, 'source': 'none', 'type': 'trivial'}]), key=lambda x: x['value'])
        U = min(up.get(c, [{'value': 48.0, 'source': 'none', 'type': 'norm bound'}]), key=lambda x: x['value'])
        rows.append({'class': c, 'members': members[c], 'L': L['value'], 'L_source': L['source'], 'L_type': L['type'], 'U': U['value'], 'U_source': U['source'],
                     'U_type': U['type'], 'U_exact': U.get('exact'), 'width': U['value'] - L['value']})
    rows.sort(key=lambda r: -r['L']); best = rows[0]; Lb = best['L']
    for r in rows:
        r['status'] = ('leader' if r is best else 'proven_inferior' if r['U'] < Lb else 'proven_superior' if r['L'] > best['U'] else 'contender')
        r['above_FR30'] = r['L'] > min(x['value'] for x in up[fr]) if r['class'] != fr else None
    counts = {s: sum(r['status'] == s for r in rows) for s in ('leader', 'proven_inferior', 'contender', 'proven_superior')}
    below_fr30 = sum(r['U'] < max(x['value'] for x in lo[fr]) for r in rows if r['class'] != fr)
    out = {'L_best': Lb, 'leader': best['class'], 'counts': counts, 'classes_rigorously_below_FR30': below_fr30,
           'classes_certified_above_FR30': [r['class'] for r in rows if r['above_FR30']], 'rows': rows}
    json.dump(out, open(os.path.join(RES, 'phase11_leaderboard.json'), 'w'), indent=0, default=float)
    with open(os.path.join(RES, 'phase11_leaderboard.csv'), 'w', newline='') as f:
        w = csv.writer(f); w.writerow(['rank', 'class', 'L', 'L_source', 'U', 'U_source', 'status'])
        for i, r in enumerate(rows): w.writerow([i + 1, r['class'], f"{r['L']:.7f}", r['L_source'], f"{r['U']:.7f}", r['U_source'], r['status']])
    print({k: v for k, v in out.items() if k != 'rows'})
    for r in rows[:8]: print(r['class'], round(r['L'], 7), r['L_source'], round(r['U'], 7), r['U_source'], r['status'])

if __name__ == '__main__': sys.path.insert(0, HERE); main()
