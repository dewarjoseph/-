#!/usr/bin/env python3
"""Phase VII-B (H): machine-readable ledger of claims -> audit/results/phase7b_ledger.json.
Every number is read from the result files (not typed in), so the ledger is regenerated from the artifacts.
Usage: python -u -I audit/phase7b_ledger.py [commit]"""
import os, sys, json, subprocess
from fractions import Fraction
HERE = os.path.dirname(os.path.abspath(__file__)); RES = os.path.join(HERE, 'results'); ROOT = os.path.join(HERE, '..')
def J(n):
    p = os.path.join(RES, n); return json.load(open(p)) if os.path.exists(p) else None
def git(*a):
    try: return subprocess.run(['git', *a], cwd=ROOT, capture_output=True, text=True).stdout.strip()
    except Exception: return None

adv, tc, cons, lr, cen, ims, imc, ctl, sca, ab, rt, ps, loc = (J(n) for n in (
    'phase7_adversarial.json', 'phase7_twocycle_formula.json', 'phase7b_consistency.json', 'phase7b_local_rules.json', 'phase7b_census.json',
    'phase7_ims.json', 'phase7b_ims_check.json', 'phase7b_controls.json', 'phase7b_scaling.json', 'phase7_abelian_check.json',
    'phase7b_rule_table.json', 'phase7_periodic_search.json', 'phase7_local.json'))
T = 'python -m pytest -q tests/test_phase7.py tests/test_phase7b.py'
lam12 = ims['12']['L_R_certified'] if ims and '12' in ims else None
claims = [
 {'id': 'P1-forced-curvature', 'proposition': 1, 'status': 'proved',
  'statement': 'every geometry-compatible frame field (proper or improper) has >= 12 of the 21 centre-octant two-cycles non-trivial in every level-1 supertile; sharp; hence never pure gauge',
  'evidence': {'exhaustive_min_nontrivial': adv['all']['min_nontrivial_two_cycle_configs'], 'assignments': adv['all']['count'], 'pure_gauge': adv['all']['pure_gauge'],
               'two_cycle_formula_mismatches': tc['mismatches'], 'two_cycles_checked': tc['two_cycles_checked']},
  'certificates': ['certificates/Phase7Counting.lean (octant_bound, total_bound, bound_attained)', 'audit/results/phase7_adversarial.json', 'audit/results/phase7_twocycle_formula.json'],
  'tests': [T + ' -k "counting or two_cycle or lean"'], 'caveats': ['Lean certifies the finite predicate; its correspondence to the geometry is the Python test test_lean_predicate_matches_explicit_holonomy']},
 {'id': 'P1b-nine-forced', 'proposition': 1, 'status': 'proved for proper frames; refuted for improper frames',
  'statement': 'the 9 two-cycles with s_v(m) = -1 are non-trivial for every proper compatible frame field (Phase VI F\')',
  'evidence': {'proper_all_forced': adv['proper']['all_forced_nontrivial'], 'improper_failures': adv['improper']['forced_failures'], 'counterexample': adv['improper_forced_failure_example']},
  'certificates': ['certificates/Phase7Counting.lean (forced_proper, forced_fails_improper)'], 'tests': [T], 'caveats': []},
 {'id': 'P2-uniform-gap', 'proposition': 2, 'status': 'certified',
  'statement': 'H_pin >= H_U >= 41789/25000 for every compatible (O(3)) frame field on every union of level-1 supertiles, incl. infinite tilings with a level-1 composition',
  'evidence': {'proper_classes': adv['certificate_proper_sharper']['gauge_classes'], 'improper_classes': adv['certificate_improper']['gauge_classes'],
               'failures': adv['certificate_proper_sharper']['failures'] + adv['certificate_improper']['failures'], 'block_min_lambda': adv['all']['lambda_min']['min'],
               'assignments_vs_classes': cons},
  'certificates': ['exact Bareiss/Sylvester over Z[i], audit/phase7_adversarial.py'], 'tests': [T + ' -k "uniform or gauge_class"'],
  'caveats': ['constant is the level-1 block optimum to 2e-5; the true uniform floor over frame fields is not known']},
 {'id': 'P2b-lemma-K-scope', 'proposition': 2, 'status': 'proved (corrected scope)',
  'statement': 'ker D_U^dag D_U != 0 iff pure gauge holds on finite connected graphs for the free operator only; false for pinned; not transferable to infinite volume',
  'evidence': adv['zero_mode'], 'certificates': [], 'tests': [T], 'caveats': []},
 {'id': 'P3-nonabelian-vs-Z2', 'proposition': 3, 'status': 'certified',
  'statement': 'E_FR30 >= Lambda_12 > U(Z2) >= E_Z2 >= 41789/25000 on the same graph and operator',
  'evidence': {'Lambda_12': lam12, 'U_Z2_L6': sca['Z2_reflect']['rayleigh_upper_exact'] if sca and 'Z2_reflect' in sca else None,
               'U_Z2_L5': ab['reflection_only_Z2']['5']['rayleigh_upper_exact']},
  'certificates': ['audit/results/phase7_ims.json', 'audit/results/phase7b_scaling.json (exact Rayleigh)'], 'tests': [T + ' -k controls'],
  'caveats': ['upper bounds are compressions of the infinite-volume operator to a supertile of the same hull']},
 {'id': 'P3b-abelian-shadows', 'proposition': 3, 'status': 'certified',
  'statement': 'E_FR30 exceeds the floor of each Abelian shadow chi_k o U_FR30 (same geometry, hierarchy, Wilson density)',
  'evidence': {f'U_chi{k}_L5': ctl[f'FR30_chi{k}']['5']['rayleigh_upper_exact'] for k in (1, 2, 3)} | {f'U_chi{k}_L6': sca[f'FR30_chi{k}']['rayleigh_upper_exact'] for k in (1, 2) if sca and f'FR30_chi{k}' in sca} | {'Lambda_12': lam12,
               'wilson_L4': {n: ctl[n]['4']['f_trl'] + 2 * ctl[n]['4']['f_m1'] for n in ('FR30', 'FR30_chi1', 'FR30_chi2', 'Z2_reflect')}},
  'certificates': ['audit/results/phase7b_controls.json'], 'tests': [T + ' -k controls'],
  'caveats': ['does NOT show Q8 is essential: Z2 reflection vs chi_1 (equal Wilson density) differ by 4.3; iid Z2 links exceed FR30 in finite volume (but have infinite-volume floor 0 a.s.)']},
 {'id': 'P3c-rule-classes', 'proposition': 3, 'status': 'partially certified', 'statement': 'per-rule separation from Z2 via B_2 > U_Z2',
  'evidence': rt['summary'] if rt else None, 'certificates': ['deliverables/PHASE7_RULE_TABLE.md'], 'tests': [], 'caveats': ['inconclusive classes need Lambda_R per rule']},
 {'id': 'P4-local-rules', 'proposition': 4, 'status': 'proved (paper argument + finite checks)',
  'statement': 'T_1 = Omega_FR30: every tiling with proper frames and legal 1-stars is in the FR30 hull; non-periodic; E_inf(R) = E_FR30 for R >= 1',
  'evidence': lr, 'certificates': ['audit/results/phase7b_local_rules.json'], 'tests': [T + ' -k local_rules'],
  'caveats': ['check B uses a sound over-approximation (grouped branching)', 'closure lemma: paper proof (report 6.1) plus per-instance assertions']},
 {'id': 'P4b-legal-type-census', 'proposition': 4, 'status': 'certified', 'statement': '|V_R| = 72, 165, 445, 762 and the generated sets are complete',
  'evidence': cen, 'certificates': ['audit/results/phase7b_census.json'], 'tests': [T + ' -k census'], 'caveats': ['completeness proof in the report section 6.1 uses primitivity (M^2 > 0)']},
 {'id': 'P4c-periodic-search', 'proposition': 4, 'status': 'corroborating only', 'statement': 'no 1-legal tiling with period lattice m*Lambda for the exhausted m',
  'evidence': ps, 'certificates': [], 'tests': [T + ' -k periodic'], 'caveats': ['bounded search; the proof of non-periodicity is P4-local-rules']},
 {'id': 'P5-localization', 'proposition': 5, 'status': 'proved + certified',
  'statement': 'Lambda_R <= E_FR30 <= D_R, Lambda_R >= D_R - eps, D_R <= E_FR30 + eps, eps(rho) <= K(rho) S_1/rho^2; certified E_FR30 in [Lambda_12, 8.7649120247]',
  'evidence': {R: {k: ims[R][k] for k in ('distinct_balls', 'L_R_certified', 'L_R_float', 'eps_upper')} | {'D_R_certified_lower': ims[R]['plain']['certified_min_float']}
               for R in ims if R.isdigit()} | {'independent_check': {k: v for k, v in (imc or {}).items() if k in ('census_R6', 'census_R8', 'finite_patch', 'K')}},
  'certificates': ['audit/results/phase7_ims.json', 'audit/results/phase7b_ims_check.json'], 'tests': [T + ' -k ims'],
  'caveats': ['D_R certificates are lower bounds on D_R; D_R >= E_FR30 by interlacing, so they are not upper certificates']},
 {'id': 'P6-hierarchy-signature', 'proposition': 6, 'status': 'not established (negative)',
  'statement': 'no hierarchy-specific signature of the band bottom survives: the floor is a function of the legal patch set, which (P4) forces the hierarchy; the one separating scale observable (persistent r_L < 1/4) is FR30-specific against its hierarchy-preserving Abelian shadows, i.e. non-Abelian, not hierarchical',
  'evidence': {'r_L': sca.get('r_L') if sca else None}, 'certificates': [], 'tests': [], 'caveats': ['IDS gap labels (frequency-dependent) untested']},
]
out = {'commit': (sys.argv[1] if len(sys.argv) > 1 else git('rev-parse', 'HEAD')), 'branch': git('rev-parse', '--abbrev-ref', 'HEAD'),
       'working_tree_status': git('status', '--short'), 'definitions': 'deliverables/PHASE7_DEFINITIONS.md', 'report': 'deliverables/PHASE7_REPORT.md', 'claims': claims}
json.dump(out, open(os.path.join(RES, 'phase7b_ledger.json'), 'w'), indent=1, default=str)
print(f"ledger: {len(claims)} claims -> audit/results/phase7b_ledger.json")
