"""
phase5a_referee_geometry.py -- hostile-referee re-verification of the GEOMETRY claim made for
audit/phase5a_independent_enumerator.py (agent A1):

    "Geometry (levels 1..5): the 8^m tiles have pairwise-disjoint unit cubes and fill exactly
     [0,2^(m+1))^3 \\ [2^m,2^(m+1))^3; distinct cube counts 56, 448, 3584, 28672, 229376 (= 7*8^m);
     every tile frame has det +1; all seven child operators D_s(v)P(pi_v) have det +1."

Run from the repository root:
    python3 -u -I audit/phase5a_referee_geometry.py [maxlevel]
Output: audit/results/phase5a_referee_geometry.txt

What this script does (nothing is imported from A1's module or from the repository for the main computation):
  1. Implements axioms A2/A3 of deliverables/CLIFFORD_Q8_END_TO_END_AUDIT.md with 3x3 integer numpy matrices
     (A1 used signed permutations; the repository uses numpy matrices too but its own loop structure), a
     breadth-first inflation, and Python Counter/set arithmetic on unit-cube indices.
  2. For levels 1..maxlevel checks: tile count 8^m, cube multiset has multiplicity 1 everywhere, the cube set
     equals the chair  {c in [0,N)^3 : not all c_i >= N/2}, N = 2^(m+1), every frame is an integer orthogonal
     matrix of determinant +1 (exact integer determinant, no floats), and the seven D_s(v)P(pi_v) have det +1.
  3. Cross-compares the tile set {(G,T)} with (a) A1's tiles_at_level (converted to matrices) and (b) the
     repository's audit/independent_clifford_q8_audit.tiles_at_level -- to establish that all three enumerate the
     SAME object (this is the only place A1's module / the repository are imported).
  4. Negative controls (sensitivity of the check):
     (a) random permutations pi_v in place of FR30 (several seeds): shows which parts of the claim depend on FR30;
     (b) perturbed centre-child offset, perturbed octant offset, and D_s(v) replaced by the identity: the fill /
         disjointness check must FAIL, otherwise it would be vacuous.
"""
import sys, os, time, itertools, collections, random, importlib.util
import numpy as np

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))

U3 = [v for v in itertools.product((0, 1), repeat=3) if v != (1, 1, 1)]
# A3 (FR30 frames) as written in the deliverable, one-line permutations p with P[i, p[i]] = 1
FR30 = {(0, 0, 0): (0, 1, 2), (0, 0, 1): (0, 2, 1), (0, 1, 0): (2, 1, 0), (0, 1, 1): (1, 2, 0),
        (1, 0, 0): (1, 0, 2), (1, 0, 1): (0, 1, 2), (1, 1, 0): (2, 0, 1)}
PI0 = (0, 1, 2)
S3 = list(itertools.permutations(range(3)))


def perm_matrix(p):
    P = np.zeros((3, 3), dtype=np.int64)
    for i in range(3):
        P[i, p[i]] = 1
    return P


def D_s(v):
    return np.diag([1 - 2 * v[0], 1 - 2 * v[1], 1 - 2 * v[2]]).astype(np.int64)


def int_det3(M):
    """Exact integer determinant by Leibniz expansion (no floating point)."""
    M = [[int(M[i, j]) for j in range(3)] for i in range(3)]
    return (M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1])
            - M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0])
            + M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]))


def make_rule(perms=FR30, pi0=PI0, centre_offset=(1, 1, 1), octant_scale=4, use_reflection=True):
    """Return the list of eight child operators (g, t) acting as (G,T) -> (G g, 2T + G t)  [A2]."""
    ops = [(perm_matrix(pi0), np.array(centre_offset, dtype=np.int64))]
    for v in U3:
        g = (D_s(v) if use_reflection else np.eye(3, dtype=np.int64)) @ perm_matrix(perms[v])
        ops.append((g, octant_scale * np.array(v, dtype=np.int64)))
    return ops


def inflate(level, ops):
    poses = [(np.eye(3, dtype=np.int64), np.zeros(3, dtype=np.int64))]
    for _ in range(level):
        poses = [(G @ g, 2 * T + G @ t) for G, T in poses for g, t in ops]
    return poses


BASE = [np.array([2 * u[0] + 1, 2 * u[1] + 1, 2 * u[2] + 1], dtype=np.int64) for u in U3]


def cubes(G, T):
    out = []
    for bc in BASE:
        num = G @ bc + 2 * T - 1
        if (num % 2 != 0).any():
            raise ValueError("non-integral cube corner")
        out.append(tuple(int(x) for x in num // 2))
    return out


def chair_target(N):
    return {c for c in itertools.product(range(N), repeat=3) if not all(ci >= N // 2 for ci in c)}


def check_level(level, ops):
    t0 = time.time()
    poses = inflate(level, ops)
    N = 2 ** (level + 1)
    mult = collections.Counter()
    for G, T in poses:
        mult.update(cubes(G, T))
    ndistinct = len(mult)
    nslots = sum(mult.values())
    overlaps = sum(1 for c, n in mult.items() if n > 1)
    target = chair_target(N)
    cube_set = set(mult)
    res = {
        'level': level, 'N': N, 'tiles': len(poses), 'tiles_expected': 8 ** level,
        'cube_slots': nslots, 'distinct_cubes': ndistinct, 'expected_distinct': 7 * 8 ** level,
        'overlapping_cubes': overlaps, 'pairwise_disjoint': overlaps == 0,
        'target_cubes': len(target),
        'missing_from_target': len(target - cube_set), 'outside_target': len(cube_set - target),
        'fills_chair_exactly': cube_set == target,
        'all_frames_orthogonal': all((G.T @ G == np.eye(3, dtype=np.int64)).all() for G, _ in poses),
        'frame_dets': dict(collections.Counter(int_det3(G) for G, _ in poses)),
        'time_s': round(time.time() - t0, 2),
    }
    res['all_frames_det_plus1'] = (set(res['frame_dets']) == {1})
    return res, poses


def pose_key(G, T):
    return (tuple(int(x) for x in np.asarray(G).reshape(-1)), tuple(int(x) for x in T))


def main(maxlevel=5):
    out = []

    def say(s=''):
        out.append(s); print(s, flush=True)

    say("phase5a referee geometry check (3x3 integer matrices, Counter/set arithmetic)")
    ops = make_rule()
    child_dets = {str(v): int_det3(D_s(v) @ perm_matrix(FR30[v])) for v in U3}
    say(f" det(D_s(v) P(pi_v)) for v in U3 (exact integer): {child_dets}")
    say(f" det(P(pi_0)) = {int_det3(perm_matrix(PI0))}")
    all_geo_ok = True
    poses_by_level = {}
    for m in range(1, maxlevel + 1):
        r, poses = check_level(m, ops)
        poses_by_level[m] = poses
        say(f" LEVEL {m}: N={r['N']} tiles={r['tiles']} (8^m={r['tiles_expected']}) cube_slots={r['cube_slots']} "
            f"distinct={r['distinct_cubes']} (7*8^m={r['expected_distinct']}) overlapping_cubes={r['overlapping_cubes']} "
            f"disjoint={r['pairwise_disjoint']} target={r['target_cubes']} missing={r['missing_from_target']} "
            f"outside={r['outside_target']} fills_chair_exactly={r['fills_chair_exactly']} "
            f"orthogonal={r['all_frames_orthogonal']} frame_dets={r['frame_dets']} det+1={r['all_frames_det_plus1']} [{r['time_s']}s]")
        all_geo_ok &= (r['tiles'] == r['tiles_expected'] and r['distinct_cubes'] == r['expected_distinct']
                       and r['pairwise_disjoint'] and r['fills_chair_exactly'] and r['all_frames_orthogonal']
                       and r['all_frames_det_plus1'])
    say(f" GEOMETRY CLAIM REPRODUCED (levels 1..{maxlevel}): {all_geo_ok}")

    # ---- cross-comparison of the tile sets with A1's module and with the repository ----
    say("\nCROSS-COMPARISON OF TILE SETS {(G,T)}")
    spec = importlib.util.spec_from_file_location("a1_enum", os.path.join(ROOT, "audit", "phase5a_independent_enumerator.py"))
    A1 = importlib.util.module_from_spec(spec); spec.loader.exec_module(A1)
    spec2 = importlib.util.spec_from_file_location("repo_audit", os.path.join(ROOT, "audit", "independent_clifford_q8_audit.py"))
    REPO = importlib.util.module_from_spec(spec2); spec2.loader.exec_module(REPO)
    cmp_ok = True
    for m in range(1, maxlevel + 1):
        mine = [pose_key(G, T) for G, T in poses_by_level[m]]
        a1 = [pose_key(A1.sp_to_matrix(G), T) for G, T, _ in A1.tiles_at_level(m)]
        same_set_a1 = set(mine) == set(a1); same_order_a1 = mine == a1
        line = f" level {m}: referee vs A1: same set={same_set_a1} same order={same_order_a1} (|referee|={len(set(mine))}, |A1|={len(set(a1))})"
        cmp_ok &= same_set_a1
        if m <= 4:
            rp = [pose_key(G, T) for G, T, _ in REPO.tiles_at_level(REPO.FR30, m)]
            same_set_repo = set(mine) == set(rp)
            line += f"; referee vs repo tiles_at_level: same set={same_set_repo} (|repo|={len(set(rp))})"
            cmp_ok &= same_set_repo
        say(line)
    say(f" ALL TILE SETS IDENTICAL: {cmp_ok}")

    # ---- negative controls ----
    say("\nNEGATIVE CONTROLS (sensitivity of the geometric check)")
    rng = random.Random(20261021)
    n_rand = 20; geo_pass = 0; det_pass = 0
    for s in range(n_rand):
        perms = {v: rng.choice(S3) for v in U3}
        ok_geo = True; ok_det = True
        for m in (1, 2, 3):
            r, _ = check_level(m, make_rule(perms=perms))
            ok_geo &= r['pairwise_disjoint'] and r['fills_chair_exactly'] and r['distinct_cubes'] == 7 * 8 ** m
            ok_det &= r['all_frames_det_plus1']
        geo_pass += ok_geo; det_pass += ok_det
    say(f" random pi_v (uniform in S3^7, {n_rand} draws, levels 1..3): disjoint+exact-fill passed in {geo_pass}/{n_rand}; "
        f"all-frames-det+1 passed in {det_pass}/{n_rand}  (expected det pass rate 2^-7 = {n_rand/128:.2f} draws)")
    # exhaustive over all 6^7 = 279936 is too slow in Python; instead check all 2^7 parity patterns via a representative
    parity_fail_examples = 0
    for signs in itertools.product((0, 1), repeat=7):
        perms = {v: ((0, 1, 2) if sg == 0 else (1, 0, 2)) for v, sg in zip(U3, signs)}
        r, _ = check_level(1, make_rule(perms=perms))
        expect_det_ok = all(((-1) ** sum(v)) == (1 if sg == 0 else -1) for v, sg in zip(U3, signs))
        assert r['pairwise_disjoint'] and r['fills_chair_exactly']
        assert r['all_frames_det_plus1'] == expect_det_ok
        parity_fail_examples += (not expect_det_ok)
    say(f" all 128 parity patterns of pi_v at level 1: disjoint+exact fill ALWAYS hold; det+1 holds iff sgn(pi_v)=(-1)^|v| "
        f"for all v ({parity_fail_examples}/128 patterns violate det+1) -- i.e. the geometric part of the claim is "
        f"independent of the FR30 permutations, only the det+1 part tests them")
    for name, kw in [("centre offset (1,1,1)->(1,1,0)", dict(centre_offset=(1, 1, 0))),
                     ("centre offset (1,1,1)->(0,0,0)", dict(centre_offset=(0, 0, 0))),
                     ("octant offset 4Gv -> 2Gv", dict(octant_scale=2)),
                     ("octant offset 4Gv -> 3Gv", dict(octant_scale=3)),
                     ("D_s(v) -> identity (no reflection)", dict(use_reflection=False))]:
        try:
            r, _ = check_level(1, make_rule(**kw))
            say(f" perturbed rule [{name}]: level 1 distinct={r['distinct_cubes']} overlapping={r['overlapping_cubes']} "
                f"missing={r['missing_from_target']} outside={r['outside_target']} fills_chair_exactly={r['fills_chair_exactly']} -> check FAILS as it should: {not (r['fills_chair_exactly'] and r['pairwise_disjoint'])}")
        except ValueError as e:
            say(f" perturbed rule [{name}]: level 1 raised {e!r} -> check FAILS as it should: True")

    say(f"\nVERDICT: geometry claim reproduced={all_geo_ok}; tile sets identical across referee/A1/repo={cmp_ok}")
    os.makedirs(os.path.join(ROOT, 'audit', 'results'), exist_ok=True)
    with open(os.path.join(ROOT, 'audit', 'results', 'phase5a_referee_geometry.txt'), 'w', encoding='utf-8') as f:
        f.write("\n".join(out) + "\n")
    print("wrote audit/results/phase5a_referee_geometry.txt")
    return all_geo_ok and cmp_ok


if __name__ == '__main__':
    ml = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    t0 = time.time()
    ok = main(ml)
    print(f"total time {time.time() - t0:.2f} s")
    sys.exit(0 if ok else 1)
