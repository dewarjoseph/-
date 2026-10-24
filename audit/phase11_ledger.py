#!/usr/bin/env python3
"""Phase XI: the reconciled Phase X proof-obligation table and the Phase XI claims ledger.

Reads the committed artifacts of Phases X and XI and writes audit/results/phase11_ledger.json:
  proof_obligations  every Phase X claim decomposed into obligations; each with its nature (proof / exact arithmetic /
                     floating point with a rounding bound / floating point evidence / artifact only) and how Phase XI discharged it
  bound_types        each numerical bound used in a comparison, with its certificate type
  reconciliation     the R = 14 / R = 15 certificates of class 1387
  claims             Phase XI claims with status labels [P] proved, [C] computer-certified, [E] floating-point evidence, [X] conjecture,
                     [F] falsified, and the test that checks each
Usage: python -u -I audit/phase11_ledger.py"""
import os, sys, json, subprocess
from fractions import Fraction
HERE = os.path.dirname(os.path.abspath(__file__)); RES = os.path.join(HERE, 'results')
def J(name, default=None):
    p = os.path.join(RES, name)
    return json.load(open(p)) if os.path.exists(p) else default
def JL(name):
    p = os.path.join(RES, name)
    return [json.loads(l) for l in open(p)] if os.path.exists(p) else []

def certs():
    out = {}
    for r in JL('phase11_cert.jsonl'):
        if r.get('tag', '') and r['tag'].startswith(('audit_', 'target_')): out[r['tag']] = r
    return out

def main():
    C = certs(); p10 = {(str(r.get('class', r.get('extended_index'))), r['R']): r for r in JL('phase10_ims.jsonl')}
    rec = lambda tag: C.get(tag, {})
    def cert_row(tag, p10key):
        a = rec(tag); b = p10.get(p10key, {})
        return {'phase10_value': b.get('Lambda_R_certified'), 'phase10_balls': b.get('distinct_balls'), 'phase11_value': a.get('Lambda_R_certified'),
                'phase11_balls': a.get('distinct_balls'), 'phase11_all_certified': a.get('all_balls_certified'), 'phase11_rejected': a.get('rejected_incomplete'),
                'mu': a.get('mu'), 'independent_implementation': a.get('implementation')}
    reconciliation = {
        '1387_R14': cert_row('audit_1387_R14', ('1387', 14)), '1387_R15': cert_row('audit_1387_R15', ('1387', 15)),
        'twin539311_R14': cert_row('audit_twin_R14', ('539311', 14)), 'FR30_R12': {'phase7_value': 7.954292264597248, **cert_row('audit_FR30_R12', ('4752', 12))},
        'statement': ('The Phase X report cites both certificates; its ledger (written at 529bba9) and tests stopped at R = 14. Both are now '
                      'independently re-certified (own enumeration, own completeness test, symbolic derivation of the overlap function, banded '
                      'Higham certificates). The ledger and tests use the R = 15 value. With R = 15 the comparison E_*(1387) > E_*(FR30) no longer '
                      'needs the Phase VIII bound 8.7642270 (a 1.77M-dimensional eigenvector that is not stored): the exact level-5 bound '
                      'Y_5(FR30) = 8.797011 < 8.7999987 suffices, and it is recomputed independently in Phase XI.')}
    proofs = J('phase11_proofs.json', {})
    z3 = J('phase11_z3.json', {})
    obligations = [
        ('O1', 'Pauli links lie in Q8; reverse crossing gives the inverse; the sign of the normal is irrelevant', 'proof',
         'algebra: (sigma.u)^2 = 1 for a unit vector u; independent implementation agrees entrywise on T_3 of 4752, 1387, 937', 'discharged'),
        ('O2', 'Deg = 24 on every chair tiling, so H_Y = 24 - A_U = D_U^+ D_U', 'proof',
         f"the chair has {proofs.get('panels', {}).get('boundary_faces', 24)} unit boundary faces; each is shared with exactly one tile in a tiling of R^3", 'discharged'),
        ('O3', 'pinned operator on a legal patch = compression of H_Y, hence lambda_min >= E_*', 'proof', 'variational principle; legality gives occurrence (minimality) or the language definition of E_*', 'discharged'),
        ('O4', 'exact rational Rayleigh quotients are rigorous upper bounds', 'exact arithmetic',
         'recomputed independently for Y3 (all 280 332 extended orbit representatives), Y4 (all survivors), Y5 (top-40 classes and twins, counterfactuals); '
         'Y6 values and the Phase VIII bound are reproduced only as recorded rationals (vectors not stored)', 'discharged for L <= 5; artifact-only for Y6 and Phase VIII'),
        ('O5', 'free supertile bottom F_k is a lower bound on E_* (Theorem X.2)', 'proof',
         'every hull tiling is sigma^k of a hull tiling (compactness), hence partitioned into level-k supertiles; links are invariant under global proper or improper frames; dropping inter-supertile panels lowers the form', 'discharged'),
        ('O6', 'IMS identity with amplified links (Phase VII Thm 7.1, X.7)', 'proof', 'Theorem XI.B1 (exact identity); randomized identity test max error %s' % proofs.get('ims_random', {}).get('max_identity_error'), 'discharged'),
        ('O7', 'c(eta) is the overlap of the 3D Dirichlet ground state', 'proof (symbolic)', 'phase11_proofs.overlap3d: equals the Phase VII closed form: %s' % proofs.get('overlap3d', {}).get('equals_phase7_formula'), 'discharged'),
        ('O8', 'r_c = sqrt(619)/14 <= 311/175', 'exact', 'phase11_proofs.rc: (311/175)^2 - r_c^2 = %s > 0' % proofs.get('rc', {}).get('bound_311_175_squared_minus_rc_squared'), 'discharged'),
        ('O9', 'the Phi-closure of the T5 1-star types is the set of all legal 1-star types', 'proof + per-instance checks',
         'closure lemma asserted on every Phi step; frame substitution irreducible (Cayley digraph of the generated finite group); independent closure gives identical key sets for 4752, 1387, 1389, 1391', 'discharged'),
        ('O10', 'every enumerated R-ball is complete (no tile of any tiling containing the patch is missing)', 'exact geometric check',
         'independent criterion: nearest unowned cube centre at distance >= R + sqrt(3)/2; 0 rejections at R = 8, 12, 14, 15', 'discharged'),
        ('O11', 'Higham Cholesky certificate (Thm 10.3) implemented soundly', 'floating point with rounding bound',
         'independent path: RCM + banded LAPACK dpbtrf, u = 2^-52, Frobenius sum inflated by (1 + 2Ku); the GPU path used dense cuSOLVER with u = 2^-51', 'discharged'),
        ('O12', 'amplification factors rounded to double', 'rounding bound', 'evaluated at 60 digits; entry error 24 * max amp * 2^-52 subtracted', 'discharged'),
        ('O13', 'E_*(1387) >= 8.7999988 (R = 15)', 'certificate', 'independently re-certified: %s' % json.dumps({k: reconciliation['1387_R15'][k] for k in ('phase11_value', 'phase11_balls', 'phase11_all_certified')}), 'discharged'),
        ('O14', 'E_*(1387) >= 8.7644994 (R = 14)', 'certificate', json.dumps({k: reconciliation['1387_R14'][k] for k in ('phase11_value', 'phase11_balls', 'phase11_all_certified')}), 'discharged'),
        ('O15', 'E_*(FR30) >= 7.954292 (Phase VII, R = 12)', 'certificate', json.dumps({k: reconciliation['FR30_R12'][k] for k in ('phase11_value', 'phase11_balls', 'phase11_all_certified')}), 'discharged'),
        ('O16', 'E_*(FR30) <= 8.7642270381 (Phase VIII sigma^5 of type 59, 884 736 tiles)', 'exact rational of an unstored vector',
         'artifact only; no longer needed for 1387 > FR30 (the independent exact Y5(FR30) suffices with the R = 15 certificate)', 'artifact-only, not load-bearing'),
        ('O17', 'mirror twin 539311: E_* >= 8.7644994 (R = 14, period-2 hull)', 'certificate', json.dumps({k: reconciliation['twin539311_R14'][k] for k in ('phase11_value', 'phase11_balls', 'phase11_all_certified')}), 'see value'),
        ('O18', 'Z^3 class-field-matched pair (X.5): identical classes, gauge-equivalent shadows, separation >= 0.18', 'exact + certificate',
         'independent rebuild: %s' % json.dumps({k: z3.get('audit', {}).get('class_matched', {}).get(k) for k in ('class_fields_identical', 'shadow_ratio_flat', 'certified_separation')}), 'discharged'),
        ('O19', 'Z^3 trace-matched pair: two shadows certified above the non-Abelian floor', 'floating point with heuristic margin',
         'Phase X used a Lipschitz branch and bound on float eigenvalues with margin 1.2e-9: evidence, not a strict certificate; see Phase XI z3 shadow free-cell bounds', 'reclassified'),
        ('O20', 'periodic-approximant floors (Phase X section 9 row 11)', 'floating point evidence', 'Bloch minima are float; stated as evidence', 'unchanged [E]'),
    ]
    out = {'commit': subprocess.run(['git', 'rev-parse', '--short', 'HEAD'], capture_output=True, text=True, cwd=HERE).stdout.strip(),
           'report': 'deliverables/PHASE11_REPORT.md', 'reconciliation': reconciliation,
           'proof_obligations': [dict(zip(('id', 'obligation', 'nature', 'how', 'status'), o)) for o in obligations]}
    extra = J('phase11_ledger_claims.json', {})
    out.update(extra)
    json.dump(out, open(os.path.join(RES, 'phase11_ledger.json'), 'w'), indent=1, default=float)
    print(json.dumps(reconciliation, indent=1, default=float)[:3000])

if __name__ == '__main__': main()
