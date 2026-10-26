#!/usr/bin/env python3
"""Phase XII, Part I: directed-rounding audit of the deliverables.

A printed interval endpoint is a valid bound only if it is rounded outward: an upper bound up, a lower bound down.  This script
collects every stored bound with its direction (exact rational upper bounds; certified lower bounds) and flags each decimal number
in the deliverables that is a rounding of one of them in the wrong direction (to the printed number of decimals):
  - every number printed with >= 4 decimals;
  - every number printed with 2 or 3 decimals directly after '>=' or '<=' (a bound claim at low precision).
Not flagged: numbers after '≈' (marked approximate), and the occurrences in ALLOW, each a literal context with the reason it is
not a bound (a requested certificate level mu, a command line, a floating-point value, or another phase's value that is itself
rounded outward).
Usage: python -u -I audit/phase12_rounding_audit.py [--fix] -> prints the findings (and with --fix rewrites the outward values)."""
import os, re, sys, json, gzip, math
HERE = os.path.dirname(os.path.abspath(__file__)); RES = os.path.join(HERE, 'results'); ROOT = os.path.dirname(HERE)
DOCS = ['deliverables/PHASE11_REPORT.md', 'deliverables/PHASE11_STRONGEST_THEOREM.md', 'deliverables/PHASE12_REPORT.md',
        'deliverables/PHASE12_STRONGEST_THEOREM.md', 'deliverables/PHASE12_DECISION_MEMO.md']
ALLOW = [  # (document, literal context containing the number, reason)
    ('deliverables/PHASE11_REPORT.md', '**1387, R = 20** (μ = 9.1105)', 'requested level mu, not a bound'),
    ('deliverables/PHASE11_REPORT.md', '(R = 18, μ = 8.7645) is not excluded** (8.8037 > 8.7645)', 'requested level mu, not a bound'),
    ('deliverables/PHASE11_REPORT.md', '(R = 20, μ = 9.1105) is not excluded** (9.1251 > 9.1105)', 'requested level mu, not a bound'),
    ('deliverables/PHASE11_REPORT.md', '`1389 16 4 4 8.7645 target_1389_R16`', 'command line (mu)'),
    ('deliverables/PHASE11_REPORT.md', '`1391 18 5 4 8.7645 target_1391_R18`', 'command line (mu)'),
    ('deliverables/PHASE11_REPORT.md', '`1387 20 5 4 9.1105 target_1387_R20`', 'command line (mu)'),
    ('deliverables/PHASE11_REPORT.md', '| 1391 | 1614 | 9.40093 | 6.91984 |', 'floating-point Lambda_8 (phase11_mechanism.json '
     '6.9198404), labelled as such; the certificate is the separate value 6.9198389'),
    ('deliverables/PHASE11_STRONGEST_THEOREM.md', '(Λ_R ≤ 9.17 and ≤ 9.19,', 'probe upper values 9.1674838 and 9.1850577 '
     'rounded up (the near-coincidence with the census Y4 of 1391 is not a reference to it)'),
    ('deliverables/PHASE12_DECISION_MEMO.md', '(Λ_R ≤ 9.17 and ≤ 9.19 ', 'probe upper values 9.1674838 and 9.1850577 rounded up'),
    ('deliverables/PHASE12_REPORT.md', 'the preregistered 9.1105 rounded down', 'requested level mu, not a bound'),
    ('deliverables/PHASE12_REPORT.md', "reproducing Phase X's 3.655558585", "Phase X's certified value 3.655558585359 "
     '(phase10_ims 4752 R = 6), rounded down'),
    ('deliverables/PHASE12_REPORT.md', '(μ = 3.6556,', 'requested level mu of the adversarial test, not a bound'),
    ('deliverables/PHASE12_REPORT.md', 'cert 1387 20 5 3 9.1105 independent_1387_R20', 'command line (mu)'),
    ('deliverables/PHASE12_REPORT.md', "and Phase X's own value 3.655558585.", 'the allow-list itself, described (C6)'),
    ('deliverables/PHASE12_REPORT.md', 'Y₆(539311) = 9.38859371623… had been printed 9.3885937 as an upper bound',
     'C6 quotes the former wrong printing; the exact value is shown truncated with an ellipsis'),
    ('deliverables/PHASE12_REPORT.md', '(it was printed 1.69927)', 'C6 quotes the former wrong printing'),
]

def JL(n):
    p = os.path.join(RES, n)
    if os.path.exists(p): return [json.loads(l) for l in open(p)]
    return [json.loads(l) for l in gzip.open(p + '.gz', 'rt')] if os.path.exists(p + '.gz') else []
def J(n): return json.load(open(os.path.join(RES, n)))

def bounds():
    """(value, 'U' or 'L', source)"""
    B = []
    for r in JL('phase11_cert.jsonl'):
        if r.get('Lambda_R_certified'): B.append((r['Lambda_R_certified'], 'L', f"phase11_cert {r.get('tag')}"))
    for r in JL('phase12_independent.jsonl'):
        if r.get('Lambda_R_certified'): B.append((r['Lambda_R_certified'], 'L', f"phase12_independent {r.get('tag')}"))
    for r in JL('phase10_ims.jsonl'):
        if r.get('Lambda_R_certified'): B.append((r['Lambda_R_certified'], 'L', f"phase10_ims {r.get('class', r.get('extended_index'))} R={r['R']}"))
    B.append((7.954292264597248, 'L', 'Phase VII R = 12 (FR30)'))
    for r in J('phase11_frontier_census.json')['rows']: B.append((r['F3_certified'], 'L', f"census F3 {r['class']}"))
    for k, r in J('phase12_transport.json').items(): B += [(r['bound'], 'L', f'transport bound {k}'), (r['alpha_min'], 'L', f'transport alpha_min {k}')]
    z = J('phase11_z3.json')['audit']['class_matched']
    B += [(z['E_A_upper'], 'U', 'Z3 pair E(A) upper'), (z['E_B_lower_free_cell'], 'L', 'Z3 pair E(B) lower'),
          (z['certified_separation'], 'L', 'Z3 pair separation')]
    for name in ('phase11_orbit_Y6.jsonl', 'phase11_frontier_X5.jsonl', 'phase11_frontier_X7.jsonl', 'phase11_frontier_twins_Y5.jsonl',
                 'phase11_frontier_counterfactual_Y5.jsonl', 'phase12_y5_census.jsonl'):
        for r in JL(name): B.append((r['upper'], 'U', f"{name} {r.get('j', r.get('class'))}"))
    for r in JL('phase11_frontier_X6.jsonl'): B.append((r['D8_upper'], 'U', f"X6 D8 {r['j']}"))
    for n in ('1387', '1391', '539311'):            # sampled probes: upper bounds on the best certificate at radius R
        for r in J(f'phase11_probe_{n}.json')['records']: B.append((r['Lambda_R_upper'], 'U', f"probe {n} R={r.get('R')}"))
    for r in J('phase11_fr30_upper.json')['chain']: B.append((r['upper'], 'U', f"FR30 U{r['m']}"))
    B.append((8.764227038115036, 'U', 'Phase VIII U5 (artifact)'))
    for r in JL('phase10_deep.jsonl'):
        if r.get('Y6_upper'): B.append((r['Y6_upper'], 'U', f"phase10_deep Y6 {r.get('class')}"))
    for r in JL('phase10_y5.jsonl'):
        if r.get('Y5_upper'): B.append((r['Y5_upper'], 'U', f"phase10_y5 {r.get('class')}"))
    for r in JL('phase10_improper_certify.jsonl'):
        for k in ('Y5_upper', 'Y6_upper'):
            if r.get(k): B.append((r[k], 'U', f"phase10_improper {k} {r['j']}"))
    for r in J('phase11_frontier_census.json')['rows']: B.append((r['Y4_upper'], 'U', f"census Y4 {r['class']}"))
    return B

NUM = re.compile(r'(?<![\d.])(\d+\.\d{4,})(?![\d])')
CMP = re.compile(r'[≥≤] ?(\d+\.\d{2,3})(?![\d])')
def _allowed_spans(doc, text):
    spans = []
    for d, lit, _ in ALLOW:
        if d != doc: continue
        i = text.find(lit)
        while i >= 0: spans.append((i, i + len(lit))); i = text.find(lit, i + 1)
    return spans

def audit(fix=False, docs=None):
    B = bounds(); found = []
    for doc in docs or DOCS:
        path = os.path.join(ROOT, doc); text = open(path).read(); repl = []; spans = _allowed_spans(doc, text)
        cands = [(m.start(1), m.end(1), m.group(1)) for m in NUM.finditer(text)]
        cands += [(m.start(1), m.end(1), m.group(1)) for m in CMP.finditer(text)]
        for a, b, s in cands:
            if any(x <= a and b <= y for x, y in spans): continue
            if text[max(0, a - 2):a].strip().endswith('≈'): continue
            d = len(s.split('.')[1]); x = float(s); tol = 0.5 * 10 ** -d + 1e-15
            for v, kind, src in B:
                if abs(v - x) <= tol and v != x and ((kind == 'U' and x < v) or (kind == 'L' and x > v)):
                    good = (math.ceil(v * 10 ** d) if kind == 'U' else math.floor(v * 10 ** d)) / 10 ** d
                    found.append({'doc': doc, 'printed': s, 'value': v, 'kind': kind, 'source': src, 'outward': f'{good:.{d}f}',
                                  'line': text.count('\n', 0, a) + 1})
                    repl.append((a, b, f'{good:.{d}f}'))
                    break
        if fix and repl:                           # rewrite exactly the flagged occurrences (never an allowed one)
            for a, b, g in sorted(set(repl), reverse=True): text = text[:a] + g + text[b:]
            open(path, 'w').write(text)
    return found

if __name__ == '__main__':
    f = audit('--fix' in sys.argv)
    seen = set()
    for r in f:
        k = (r['doc'], r['printed'])
        if k in seen: continue
        seen.add(k); print(f"{r['doc']}:{r['line']}: {r['printed']} -> {r['outward']}  ({r['kind']}, {r['source']}, exact {r['value']:.12f})")
    print(len(seen), 'distinct wrong-direction roundings')
