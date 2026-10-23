#!/usr/bin/env python3
"""Phase VIII: machine-readable ledger of claims -> audit/results/phase8_ledger.json (numbers read from the result files).
Usage: python -u -I audit/phase8_ledger.py [commit]"""
import os, sys, json, subprocess
HERE = os.path.dirname(os.path.abspath(__file__)); RES = os.path.join(HERE, 'results'); ROOT = os.path.join(HERE, '..')
def J(n):
    p = os.path.join(RES, n); return json.load(open(p)) if os.path.exists(p) else None
def git(*a):
    try: return subprocess.run(['git', *a], cwd=ROOT, capture_output=True, text=True).stdout.strip()
    except Exception: return None
ef, pb, sc, cp, lg, ch5, geo, fib, smc, slab, cl, po, dos = (J(f'phase8_{n}.json') for n in ('env_fiber', 'patch_bounds', 'selection_controls', 'classpair', 'legality',
                                                                                           'chain_m5', 'geo', 'fiber', 'seamctl', 'slab', 'chainloc', 'poles', 'dos'))
rg = [json.loads(l) for l in open(os.path.join(RES, 'phase8_copy_rg.jsonl'))] if os.path.exists(os.path.join(RES, 'phase8_copy_rg.jsonl')) else []
T = 'python -m pytest -q tests/test_phase8.py'; D = 'python -u -I audit/phase8_diagnostics.py'
U = {m: pb['U'][m]['min'] for m in pb['U']} if pb else {}
pair = next((g for g in cp['groups'] if {r['index'] for r in g['rules']} >= {937, 938}), None) if cp else None
claims = [
 {'id': 'R1-exact-recursion', 'status': 'proved (V-D D2) + re-verified', 'statement': 'R_{m+1}(E) = Schur complement of the glued eight-copy response; Loewner monotone, concave, gauge covariant; dim S_m = 8, 53, 287, 1331, 5723, 23723, 96587',
  'certificates': ['tests/test_phase8.py::test_recursion_exact_monotone_concave', '::test_surface_counts'], 'tests': [T + ' -k "recursion or surface"'], 'caveats': ['state space grows like 4^m']},
 {'id': 'R2-patch-functional', 'status': 'proved', 'statement': 'U_m(tau) = lambda_min(H|sigma^m(tau)) is a functional F_tau(R_m) of the level-m response (every copy carries T_m operator; Theorem E1)',
  'certificates': ['::test_every_patch_copy_is_the_supertile'], 'tests': [T], 'caveats': []},
 {'id': 'R3-selection-chain', 'status': 'proved (monotone convergence) + computed (selection)', 'statement': 'for every Phi-self-loop tau, U_m(tau) decreases to E_*; over all 72 types the minimiser is the self-loop pair {59, 63} at m = 1..3, and {35, 39, 59, 63} agree to 3e-10 at m = 4',
  'evidence': {'U_m': U, 'argmin': {m: pb['U'][m]['argmin'] for m in pb['U']} if pb else None, 'self_loops': pb['self_loops'] if pb else None,
               'certificate_m4': pb.get('certificate') if pb else None, 'chain_m5': ch5, 'selected_state': cl}, 'tests': [T + ' -k selection'], 'caveats': ['selection for all m not proved']},
 {'id': 'B1-upper-bound', 'status': 'certified (exact rational Rayleigh quotient on a legal patch)', 'statement': 'E_* <= 95969095435322528/10950092349041091 = 8.7642270381',
  'evidence': ch5, 'tests': [T + ' -k chain_m5'], 'caveats': ['the patch is legal by construction (inflation of a legal 1-star); legality is Phase VII 6.2']},
 {'id': 'P1-poles', 'status': 'proved (ordering, monotonicity) + computed (values)', 'statement': 'E_* <= U_k(tau) <= E_k <= lambda_II(k) = first pole of R_k; lambda_II(k) non-increasing to E_*; lambda_II(k) - E_k shrinks ~15x per level',
  'evidence': po, 'tests': [D + ' poles'], 'caveats': ['convergence of lambda_II(k) to E_* uses the exhaustion argument of Theorem 8.3(c)']},
 {'id': 'D1-near-edge-counting', 'status': 'numerical [E]; scaling form unresolved [U]', 'statement': 'near-edge counting function of the pinned supertiles at levels 3-5: clustered finite-volume spectrum, local exponents 1.3-1.6 at L5, L5/L4 ratios 9, 4.3, 6.6; neither 2D-seam (4^L delta) nor 3D-bulk (8^L delta^1.5) scaling is established',
  'evidence': dos and {L: {k: v for k, v in r.items() if k != 'eigenvalues'} for L, r in dos['levels'].items()}, 'tests': [D + ' dos'], 'caveats': ['finite volume; three levels only']},
 {'id': 'S1-seam-bound-edge', 'status': 'numerical [E]', 'statement': 'the converged edge states are bound transversally to the depth-1 seams with a level-independent profile and extended along them; scrambled controls lose this to defect-localised states',
  'evidence': {'geo': geo, 'slab': slab, 'seam_controls': smc}, 'tests': [D + ' geo slab seamctl'], 'caveats': ['finite volume only; no infinite-volume localisation claim']},
 {'id': 'F1-environment-fiber', 'status': 'numerical [E]', 'statement': 'a T3-copy fiber built from the 72 legal 1-star environments alone captures the deep edge states and predicts held-out edges',
  'evidence': {'capture': ef['capture'] if ef else None, 'level5': ef['level5'] if ef else None, 'level4': ef['level4'] if ef else None, 'copy_lattice_rg': rg, 'fiber_dimensions': fib},
  'tests': [T + ' -k fiber', D + ' fiber'], 'caveats': ['Ritz upper bounds; boundedness of the fiber for copies of T4 and beyond not verified']},
 {'id': 'C1-class-count-counterexample', 'status': 'proved by example (exact counts; float eigenvalues)', 'statement': 'identical axis-resolved level-4 plaquette class counts, different bottoms at levels 3-5 (the only such collision among the 1097 class-count values of the 6561-rule census)',
  'evidence': {'census_rules': cp['census_rules'] if cp else None, 'groups_with_distinct_bottoms': cp['groups_with_distinct_bottoms'] if cp else None,
               'pair_937_938': pair and {'rules': pair['rules'], 'identical_statistics': len(pair['identical_statistics']), 'different_statistics': pair['different_statistics']}},
  'tests': [T + ' -k counterexample', D + ' classpair'], 'caveats': []},
 {'id': 'C2-control-legality', 'status': 'computed', 'statement': 'V-B hierarchy-scrambling controls have illegal 1-stars on 68-100 % of tiles; the requested frequency-preserving control is impossible (Phase VII 6.2 + unique ergodicity)',
  'evidence': lg, 'tests': [D + ' legality'], 'caveats': ['earlier causal readings of these controls are withdrawn (report section 10)']},
 {'id': 'C3-shadow-selection', 'status': 'computed', 'statement': 'chi1/chi3 shadows are minimised by a member of FR30 selecting set (63 resp. 59) at m = 1..3 and have the same four lowest types at m = 2, 3; chi2 selects a different, unstable set: selection is connection-dependent',
  'evidence': {k: {m: v[m]['argmin'] for m in v} for k, v in sc.items()} if sc else None, 'certificates': ['certificates/Phase8Shadows.lean'], 'tests': [T + ' -k lean_shadow'], 'caveats': []},
 {'id': 'H1-hierarchy-signature', 'status': 'not established', 'statement': 'no hierarchy-specific spectral law separate from local legality; selection is local-configuration and connection dependent', 'caveats': []},
]
out = {'commit': (sys.argv[1] if len(sys.argv) > 1 else git('rev-parse', 'HEAD')), 'branch': git('rev-parse', '--abbrev-ref', 'HEAD'),
       'report': 'deliverables/PHASE8_REPORT.md', 'claims': claims}
json.dump(out, open(os.path.join(RES, 'phase8_ledger.json'), 'w'), indent=1, default=str); print(f"ledger: {len(claims)} claims")
