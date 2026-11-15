# Phase 4.3 Physics Bottleneck Attacks (2026-11-15)

Combines the Phase 4.2 and 4.3 results: per-track results with evidence labels, a spec-corrections section and a not-run table.

Folder: `papers/2026-11-15-phase4.3/`. Every file in the folder is listed with its sha256 in `SHA256SUMS` (generated after the last file was written; `README.md` itself is excluded from it).

## Main files
| file | sha256 |
|---|---|
| `main.tex` | `9a9cfb74dbba812b6cb15f2ea49c2ce0763120ddbd2cb2981b85c35b0980673a` |
| `main.pdf` | `4deeee3a92b60a62fcf847cc3cef13ba832d63c8ac8a5ce882ac84fb8d8d7d19` |
| `phase4.3-physics-bottleneck-attacks.pdf` | `4deeee3a92b60a62fcf847cc3cef13ba832d63c8ac8a5ce882ac84fb8d8d7d19` |
| `main.txt` | `cab05e3728173d235e6887ad31ea6002fb92d3e6d7a13b5d91777fc7186001f5` |
| `results.json` | `912ee516575db5cd0dca98b3ad0f34340ea398e4dc635699cd328e0fede45167` |
| `LEAKSCAN_RESULT.txt` | `29b7425b6214f0c16c44c98d766d21e681fc5689608577ce8d51b392d3da2512` |
| `PREREG_HASHES.txt` | `939119de826f31c3ddd87abcb46f9cf52ff84968a301e17d9a3aac11d980b87c` |
| `lean/ToeLeSecular_2026-11-15.lean` | `9cc39f3156fe5b55d11cf870b88959956f76529860d163777d9183c8bb55c926` |
| `lean/ToeG403_2026-11-15.lean` | `d8e22951aca4f4b0b504f891dca2e022acb7f38802d2af52a347dd12f094a4b7` |
| `prereg/P43_LEAN.json` | `3960465d0947b7d73fa4fe4f9c33291985c17dbf154e114f9bbfb5ef29cd2e68` |
| `prereg/P43_T1A.json` | `03b73e1a23c27aceaa7984764f269f472f226875eac226eb46093199c714fa69` |
| `prereg/P43_T1B.json` | `275441049ca446f4f3d18cef36c3a27cb872bd8a71916b4a0d5b5556ff936013` |
| `prereg/P43_T1B_PROD.json` | `1d3b89363cecee56a0fb9edfc214d2b83c4409c418ae9f498bf72edd742ccb94` |
| `prereg/P43_T2.json` | `d0b6f5322dee092ff50b7e0ef47131cba2ece8c35bc2657ea3b314809d7ad844` |
| `prereg/P43_T3.json` | `c19b5e3fbc9545d3acad973a0ea680eb6aa0cd70185715906fbe4781f9f0cfb0` |
| `prereg/P43_T4A.json` | `cef40943be7378bb6cad55656ff90ac37a8b50786e3cd26dd3f96b6178495eac` |
| `prereg/P43_T4B.json` | `c18a1969dba1fa2dc5eef7ca6b81d725f411bdf2c691a5948bcbc37f9942433b` |
| `prereg/P43_T5A.json` | `224a5cfe190500dc8ba0de07e5d2952418803a197e85ad06425585143c622f58` |
| `prereg/P43_T5B.json` | `40a49c1e188cd8dc2617688c65468c3c81103281e21c4b6c193320706168d094` |

## Layout
- `main.tex`, `main.pdf`, `phase4.3-physics-bottleneck-attacks.pdf` (byte copy of `main.pdf`), `main.txt` (pdftotext output used for the leak scan), `tab_*.tex`, `sec_t1bprod.tex`, `su2c.tex`: the paper and its generated tables.
- `results.json`: all scored results (T1A, T1B, T1B_PROD, T2, T3, T4A, T4B, T5A, T5B); `score_all.py`, `build_report.py`, `finalize_prod.py` regenerate it.
- `prereg/`: frozen preregistrations (hypothesis, criteria, script sha256), frozen before each scored run; `PREREG_HASHES.txt` lists their hashes and freeze times (the T1B prereg was re-frozen twice during development: thread pinning, then memory edits; only the last one scored).
- `t1/`, `t1b/`, `t2/`, `t3/`, `t4/`, `t5/`: scripts and JSON outputs per track. `lean/`: scratch Lean files with raw build logs (no `sorryAx`).
- Run every script with `python -I`.

## Status notes
- Track 1A/1B bounds are conditional on the hand-proved Theorems B/C/F (not machine-verified).
- Not run: Track 1C, T1B at `d_c=4` and for rule 1387, T5A for rule 1387, the 18-rule flagged list of 5B (a substitute set was run), the antiunitary-breaking test of T3. See the not-run table in the paper.
- Leak scan: `LEAKSCAN_RESULT.txt` (0 hits).
