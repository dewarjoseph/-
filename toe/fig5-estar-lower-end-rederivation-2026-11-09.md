# FIG5-ESTAR lower end: re-derivation from source (2026-11-09)

Bot: Theory of Everything. Task: PM bus #1065 item 1, due 6 PM PT Mon Nov 9, 2026.
Programme label: a unification programme (not a theory of everything).

## Verdict
**MATCH on both certificates; no gap.** [C] on re-execution of the source scripts.
- Phase XI rerun reproduces the stored lower bound exactly: Lambda_R_certified = 7.954291278163518, mu = 8340679/1048576, 2315/2315 balls certified, tiles/ball 1009..1072, bandwidth_max 606, amp_max 1.0718631550615068, entry_err 5.712034339183916e-15.
- Phase VII rerun reproduces its stored certificate exactly: L_R_certified = 601009330964533299746863/75557863725914323419136 = 7.954292264597248 (outward 7.954292), mu = 1042585/131072, max_delta 3.276603328106678e-08, eps_upper 1.5091221498821372, 294912 tiles, 2315 balls.
- Only difference from stored Phase VII JSON: two float *diagnostic* fields (lambda_tilde_float_min 7.954293448168004 vs 7.954293448167956; median differs at 2e-14), from LAPACK/threading rounding. They do not enter the certified rational. The stored "plain" key is from a different code path I did not rerun.

## Why the two lower ends differ (not a contradiction)
Both are rigorous lower bounds on the same quantity, from the same method (IMS localization, amplified ball operator 24 - A~, A~_ab = A_ab / c(|x_a-x_b|/rho), rho = R - 311/175 = 1789/175, banded Cholesky of the real form of (24-A~) - mu with Higham 2002 Thm 10.3). They differ only in the dyadic mu each run chose: Phase XI 7.954291278 vs Phase VII 7.954292264597 (gap 9.9e-7). The ledger's 7.954292 is supported by Phase VII, not by Phase XI. The paper's printed 7.954291 is below both, so it is safe and conservative.

## Labels
- Paper FIG5-ESTAR: [E] (unchanged). Source certificate: [C] (unchanged).
- Lower-end arithmetic: [C], re-executed here.
- Upper end 8.7642270382 was not re-derived in this item (separate leftover); Phase IX remains unratified.
- **claims.csv: no change. v0.6 not touched. No Phase IX ratification ask.**

## Method / provenance
Source repo /workspace/chair44-repo HEAD ee5d2906ec62547f3f90b3c1b4df5174949b7c0f (git status clean afterwards; not edited). Scratch copy at /workspace/fig5-rederive/ with a venv (numpy, scipy, sympy) and OMP/OPENBLAS/MKL threads = 1. Run with python -I:
- audit/phase11_chair.py cert 4752 12 4 <nproc> <mu> (Phase XI)
- audit/phase7_ims.py 12 (Phase VII)

Source hashes (sha256):
- audit/phase11_chair.py 0dfadade90045bca2469f4ba09cb6e780b9518a2797adb3a85c0c1167d0297ef
- audit/phase7_ims.py 92842551c3f6b1b446608aeb51d5015f6a5376fb47ad186fa5f978995d29ae7f
- results/phase11_cert.jsonl bf3d438f50cc0075e5a0fdd1653c2e122c75275dbecb1c3f985088016d510fe3
- results/phase11_ledger.json d64de8f1381c40c25e21d61b6b36434ea2117fe781d0f6c86ee8a8d0fdb582be
- results/phase7_ims.json (stored) 3fcefaab07699dbd9a1056b704af6483bba0d0be7f1b7455fcc731a9547c87f6

Rerun artifacts in fig5-rederive-logs-2026-11-09/: phase11_R12.log 89dda5f70450cf87d0231ac4b2791ad1c5c7d625328121d631000825813ef9c6; phase7_R12.log 3e8154e931c6834458c689649ac52c2da6630ff4ee86ca60f4766df65e3465c3; rerun_phase7_ims.json 3e698eb828d9d5f11d017c978c4a3ee54d84ba25117651ff5f41595a9062a840; stored_phase7_ims.json 3fcefaab07699dbd9a1056b704af6483bba0d0be7f1b7455fcc731a9547c87f6.

## Limits of this claim
This is re-execution of the same certificate code, not an independent reimplementation; the Phase XI enumeration is separate code from Phase VII, which is the only independence. The IEEE/Higham bounds are those the scripts state; I did not re-prove them. Next leftover: independent reimplementation or upper-end re-derivation; an L-uniform T7 bound stays [X].
