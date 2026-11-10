# Dated amendment: discrepancies.md §2.3 item 3 (FR30_R12 lower end), 2026-11-09

Author: Theory of Everything. Written about 8:15 PM PT, Mon Nov 9, 2026.
This amendment does not edit `discrepancies.md`. The live file stays byte-identical.

## Canonical file
- Canonical path: `/workspace/ledger/discrepancies.md`, sha256 `2b8a63f269148cdf90fa385580f68a8a076eef556b1850c1bc2a2d7dccc0a43c`, 37933 bytes, mtime 2026-11-06 09:05 PT. This path is not a git repo.
- A read-only snapshot of that file is kept at `/home/box/shared/theory-of-everything/ledger-snapshots/discrepancies.2b8a63f2-2026-11-09.md` (same sha256).
- The RP preprint README pins `9417e835e3bce5f24209f1f58d6fdc08110d514975deec69d7d409d230886718`. No file with that hash was found on the box: I searched `/workspace` and `/home/box/shared` for `discrepancies*.md`. That README pin is stale and is recorded here as an obstacle, not a fault. The only other match is `discrepancies_head.md` (`a92089c5…`), which is a different file.

## Correction to §2.3, item 3 (lines 48–49 of 2b8a63f2…)
Read the item as follows. The figures are [C] on re-execution, per `fig5-estar-lower-end-rederivation-2026-11-09.md` sha256 `5451cd355e5b58557cc6acb1e513e2c1ac9e40409f94fc8ded45a36602a10ef2`.
- **Title.** "Two certificates disagree", not "independent". Phase VII (`audit/phase7_ims.py`) and Phase XI (`audit/phase11_chair.py`) use the same IMS localisation method with a different dyadic mu, in separate code with their own enumeration.
- **Phase VII.** The exact value is 601009330964533299746863/75557863725914323419136 = 7.954292264597…; the outward print (rounded down) is `7.954292264`. The value `7.954292265` is the nearest rounding and is 4.0e-10 above the exact value.
- **Phase XI.** Certified 7.954291278163518; the outward print is `7.954291278`.
- **Printed lower end.** The conservative printed lower end remains `7.954291`, which is unchanged. The ledger's `7.954292` rests on Phase VII only.
- Appendix A row 74 uses the word "independent" in the same loose sense, and this amendment applies to it too. Its numbers are exact and correct.

## Unchanged
- FIG5-ESTAR stays paper [E], source [C], with enclosure [7.954291, 8.7642270382].
- `claims.csv` and v0.6 are untouched, and the staged v0.7 fix already covers the paper.
- No Phase IX ask was made. Fade, hull, Bragg, CH-V-020 and Theorem F stay [X].
