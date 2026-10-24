#!/usr/bin/env python3
"""Phase IX: machine-readable ledger -> audit/results/phase9_ledger.json.

1. bounds: every quoted number about E_* = inf sigma(H_Y), Y in Omega_FR30 (H = 24 - A_U on l^2(Y) x C^2), with ONE label:
     rigorous      a proof, or a computer-assisted proof whose arithmetic is exact or has a rigorous rounding bound
     fv_certificate a rigorous statement about a FINITE matrix (it bounds E_* only through a stated compression argument)
     numerical     floating-point evidence
     conjectural   rests on an unproved hypothesis (e.g. on decrement ratios)
   with what it depends on and the artifact that regenerates it.
2. claims: the Phase IX claims, each with a novelty category (A standard machinery, B new application, C model-specific
   mathematical novelty, D potentially new physical principle), evidence, prior theory and the smallest remaining gap.
Usage: python -u -I audit/phase9_ledger.py [commit]"""
import os, sys, json, subprocess
from fractions import Fraction
HERE = os.path.dirname(os.path.abspath(__file__)); RES = os.path.join(HERE, 'results'); ROOT = os.path.join(HERE, '..')
def J(n):
    p = os.path.join(RES, n); return json.load(open(p)) if os.path.exists(p) else None
def git(*a):
    try: return subprocess.run(['git', *a], cwd=ROOT, capture_output=True, text=True).stdout.strip()
    except Exception: return None
ims, ch5, pb, p5e = J('phase7_ims.json'), J('phase8_chain_m5.json'), J('phase8_patch_bounds.json'), J('phase5e_level7.json')
cert7 = J('phase5e_level7_certified.json')
pair, mom, loops, state, ladder, steps, edge, pre, cert4, lad01 = (J(f'phase9_{n}.json') for n in ('pair', 'moments', 'loops', 'state', 'ladder', 'steps', 'edge', 'preregistration', 'cert4', 'ladder_m01'))
ladder = ladder or lad01
rg = [json.loads(l) for l in open(os.path.join(RES, 'phase8_copy_rg.jsonl'))] if os.path.exists(os.path.join(RES, 'phase8_copy_rg.jsonl')) else []

bounds = [
 {'quantity': 'E_*', 'direction': '>=', 'value': float(Fraction(ims['12']['L_R_certified'])) if ims else 7.954292, 'exact': ims['12']['L_R_certified'] if ims else None, 'label': 'rigorous',
  'statement': 'E(Y) >= Lambda_12 for every Y in T_12 = Omega_FR30 (infinite volume)',
  'depends_on': ['Phase VII Thm 7.1 (exact IMS identity with explicit overlap c(eta); proof in PHASE7_REPORT s.7)', 'Phase VII Thm 6.2 (T_1 = Omega_FR30; computer-assisted finite checks P, R0, S, A, B)',
                 'completeness of the enumeration of the 2315 legal 12-balls (asserted instance by instance; single implementation at R = 12, two independent implementations agree at R = 6, 8)',
                 'floating Cholesky with Higham Thm 10.3 rounding bound; amplification factors in mpmath interval arithmetic'],
  'not_dependent_on': ['any ratio or extrapolation hypothesis'], 'artifact': 'audit/results/phase7_ims.json', 'regenerate': 'IMS_PROCS=12 IMS_PLAIN_MAX=12 python -u -I audit/phase7_ims.py 12 (about 1 h)'},
 {'quantity': 'E_*', 'direction': '<=', 'value': ch5['rayleigh_upper'] if ch5 else None, 'exact': ch5['rayleigh_upper_exact'] if ch5 else None, 'label': 'rigorous',
  'statement': 'E_* <= exact rational Rayleigh quotient of an integer vector supported on the legal patch sigma^5(tau_59) (884 736 tiles)',
  'depends_on': ['variational principle: the pinned patch operator is the compression P H_Y P (definitions s.5)', 'legality of sigma^5(tau_59): tau_59 is a 1-star occurring in FR30 supertiles, and sigma maps occurring patches to occurring patches',
                 'minimality of Omega_FR30 (every hull element has the same infimum)', 'H has Gaussian-integer entries (LINKGI in {-1,0,1}; verified), so the integer arithmetic of the quotient is exact'],
  'not_dependent_on': ['any ratio or extrapolation hypothesis'], 'artifact': 'audit/results/phase8_chain_m5.json', 'regenerate': 'python -u -I audit/phase8_chain5.py 5 59 (about 30 min)'},
 {'quantity': 'E_*', 'direction': '<=', 'value': 8.7649120247, 'label': 'rigorous', 'statement': 'V-E: exact Rayleigh quotient on the pinned level-7 supertile T_7 (superseded by the sigma^5(tau_59) bound)',
  'depends_on': ['compression', 'exact integer arithmetic'], 'artifact': 'audit/results/phase5e_level7_certified.json'},
 {'quantity': 'E_*', 'direction': '<=', 'value': pb['certificate']['rayleigh_upper'] if pb else None, 'label': 'rigorous', 'statement': 'm = 4 member (type 39): exact Rayleigh quotient', 'artifact': 'audit/results/phase8_patch_bounds.json'},
 {'quantity': 'lambda_min(H_pin(T_7))', 'value': p5e['eigenvalues'][0] if p5e else 8.764911988, 'label': 'numerical', 'statement': 'float eigenvalue, residual 1.0e-8 (its certificate is the upper bound 8.7649120247 on the same finite matrix: fv_certificate)', 'artifact': 'audit/results/phase5e_level7.json'},
 {'quantity': 'lambda_min(H | sigma^5(tau_59))', 'value': ch5['lambda_float'] if ch5 else None, 'label': 'numerical', 'statement': 'float eigenvalue, residual 5e-12', 'artifact': 'audit/results/phase8_chain_m5.json'},
 {'quantity': 'E_*', 'interval': [8.76385, 8.76423], 'label': 'conjectural', 'statement': 'holds IF every later chain decrement ratio is <= 0.1541 (V-E Thm E7 then gives the lower end)', 'depends_on': ['unproved ratio hypothesis'], 'artifact': 'audit/results/phase8_patch_bounds.json, phase8_chain_m5.json'},
 {'quantity': 'E_*', 'interval': [8.7631, 8.7637], 'label': 'conjectural', 'statement': 'V-E extrapolations of the pinned supertiles (last-ratio geometric tail)', 'depends_on': ['unproved ratio hypothesis']},
 {'quantity': 'E_*', 'interval': [7.954292, 8.7642270381], 'label': 'rigorous', 'statement': 'two-sided enclosure: both endpoints are rigorous infinite-volume bounds on the same quantity inf sigma(H_Y), Y in Omega_FR30; neither uses an extrapolation'},
]
if pair:
    c = pair['levels']['3']['certified']
    bounds += [{'quantity': 'lambda_min(H_pin(T_3)) for rule %s' % r, 'interval': [c[r]['lower'], c[r]['upper']], 'label': 'fv_certificate',
                'statement': 'finite matrix only: exact Rayleigh quotient above, Higham-certified Cholesky below', 'artifact': 'audit/results/phase9_pair.json'} for r in ('937', '938')]
if cert4:
    bounds += [{'quantity': 'lambda_min(H_pin(T_4)) for rule %s' % r, 'interval': [cert4[r]['lower'], cert4[r]['upper']], 'label': 'fv_certificate',
                'statement': 'finite matrix only: exact Rayleigh quotient above, Higham-certified Cholesky below', 'artifact': 'audit/results/phase9_cert4.json'} for r in ('937', '938')]

def ref(*k): return list(k)
claims = [
 {'id': 'N1-recursion', 'category': 'A', 'statement': 'exact child-to-parent Schur recursion of the labelled surface response; Loewner monotone, concave, gauge covariant (Phase V-D/VIII Prop 8.1)',
  'evidence': 'proof; tests/test_phase8.py', 'prior': ref('Haynsworth 1968 (inertia)', 'Li-Mathias 2000; Anderson-Trapp 1975 (Schur complement monotone/concave)', 'Sire-Bellissard 1990 (Schur-formula RG on the octagonal tiling)', 'Malozemov-Teplyaev 2003, Sabot 2003 (spectral decimation)', 'Chen-Guo 2020 (gauge-covariant U(1) decimation)'),
  'gap': 'none for the statement; applying it to an SU(2) connection on a substitution tiling appears new (provisional)'},
 {'id': 'N2-selection-chain', 'category': 'B', 'statement': 'Theorem 8.3: along every Phi-self-loop 1-star type, U_m(tau) decreases to E_*; the minimiser over the 72 types is the self-loop pair 59/63 for m <= 3 (4-way tie at m = 4)',
  'evidence': 'proof (interlacing + exhaustion + minimality) + computation (phase8_patch_bounds.json)', 'prior': ref('min-max principle; Lenz-Stollmann (constancy of spectrum on minimal hulls)'), 'gap': 'selection for all m unproved; rate unproved'},
 {'id': 'N3-enclosure', 'category': 'B', 'statement': 'E_* in [7.954292, 8.7642270381], rigorous', 'evidence': 'computer-assisted (bounds section)',
  'prior': ref('Cycon-Froese-Kirsch-Simon (IMS)', 'Hege-Moscolari-Teufel 2022 (rigorous two-sided patch bounds, scalar/U(1) operators on quasicrystals)'), 'gap': 'width 0.81; the lower side converges only as O(R^-2)'},
 {'id': 'N4-local-rules', 'category': 'C (provisional)', 'statement': 'Phase VII Thm 6.2: the FR30 frame decoration is itself a radius-1 matching rule (T_1 = Omega_FR30)',
  'evidence': 'computer-assisted proof (Phase VII s.6)', 'prior': ref('Mozes 1989, Goodman-Strauss 1998 (local rules for substitution hierarchies)', '2026 preprints on 3D chair matching rules: Tsiokos arXiv:2609.19214, Flicker arXiv:2609.23783, Kamenetsky arXiv:2610.00916 (unrefereed; priority not settled)'),
  'gap': 'priority against the 2026 3D-chair preprints not assessed in full text'},
 {'id': 'N5-class-count-insufficiency', 'category': 'B', 'statement': 'Theorem 9.1 (necessity): plaquette and two-cycle conjugacy-class counts (also owner-resolved) and spectral moments of order <= 3 do not determine the spectral bottom; rules 937/938, certified at level 3',
  'evidence': 'exact counts and moments; certified enclosures (phase9_pair.json, phase9_moments.json)', 'prior': ref('Cavaleri-Donno 2022 (cospectral but not switching-isomorphic gain graphs; closed-walk gains)', 'Procesi 1976, Giles 1981 (trace invariants determine the connection up to gauge)'),
  'gap': 'infinite-volume separation of the two hull floors not certified (finite-volume levels 3-5 only)'},
 {'id': 'N6-census-classes', 'category': 'B', 'statement': 'the 6561 proper decorations form 1125 S3-orbits and 1098 gauge classes; the level-3 spectrum separates all 1098; class counts separate all but the 937/938 pair',
  'evidence': 'phase9_state.json (tree-gauge equivalence tests)', 'prior': ref('Cavaleri-Donno 2022 (switching equivalence via closed-walk gains)'), 'gap': 'level 3 only; gauge equivalence is tested on T_3'},
 {'id': 'N7-predictive-state', 'category': 'B', 'statement': 'held-out (by gauge class) prediction of Y3/Y4 from local summaries: best CV-RMSE about 0.19-0.20 (R^2 0.87); FR30 is underpredicted by every summary',
  'evidence': 'phase9_state.json', 'prior': ref('Phase V-B flux regression (ungrouped CV; superseded)'), 'gap': 'linear and k-NN models only'},
 {'id': 'N8-null-vs-hierarchy', 'category': 'pending', 'statement': 'pre-registered matched-pair test (phase9_preregistration.json)', 'evidence': 'phase9_ladder.json', 'prior': [], 'gap': ''},
 {'id': 'N9-physical-law', 'category': 'D: none established', 'statement': 'no candidate law with a defined observable, predictive content beyond standard machinery, and survival of controls was found', 'evidence': 'report s.6-8', 'prior': [], 'gap': ''},
]
if ladder and pre:
    d1 = ladder['diff_938_minus_937']; ds = (pair['levels']['5']['Y']['938'] - pair['levels']['5']['Y']['937']) if pair else None
    d1v, d3v = d1.get('1'), d1.get('3')
    verdict = ('null supported, hierarchy model falsified for this pair' if (d1v is not None and ds is not None and d1v * ds > 0 and abs(d1v - ds) <= 0.10)
               else 'hierarchy supported, null falsified for this pair' if (d1v is not None and abs(d1v) <= 0.05 and d3v is not None and abs(d3v - ds) <= 0.10) else 'inconclusive')
    claims[7].update({'category': 'B', 'statement': f'pre-registered matched-pair test: Delta_m (938 - 937) = {d1}, Delta_star = {ds}; verdict: {verdict}', 'verdict': verdict})
out = {'commit': (sys.argv[1] if len(sys.argv) > 1 else git('rev-parse', 'HEAD')), 'branch': git('rev-parse', '--abbrev-ref', 'HEAD'), 'report': 'deliverables/PHASE9_REPORT.md',
       'bounds': bounds, 'claims': claims, 'copy_rg_runs': rg}
json.dump(out, open(os.path.join(RES, 'phase9_ledger.json'), 'w'), indent=1, default=str); print(f"ledger: {len(bounds)} bounds, {len(claims)} claims")
