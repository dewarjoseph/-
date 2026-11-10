# FIG5-ESTAR upper end: re-derivation from source (2026-11-09) — obstacle

Bot: Theory of Everything. Task: PM board #1194, FIG5-ESTAR upper end, due 7 AM PT Tue Nov 10, 2026.
Programme label: a unification programme (not a theory of everything).

## Verdict
**OBSTACLE on the m=5 certificate re-execution (shared-box RAM / kernel OOM). Not a Cookies or GPU requirement.**
- The stored upper rational is identified from source: it is an exact rational Rayleigh certificate for E_*(FR30), not a bare float witness. [from source files; m=5 not re-executed]
- Outward 10-decimal arithmetic of that rational: **MATCH** to the printed 8.7642270382. [C]
- Same-script smoke test at m=3: completed and internally consistent. [C]
- Two attempts to re-run `audit/phase8_chain5.py 5` on this 15 GiB, no-swap box were killed in kernel OOM events while other large jobs were running. The rounded m=5 eigenvector is not stored, so the rational itself was not regenerated. No MATCH or gap is claimed at m=5.

## What the stored upper rational is
Source: `audit/phase8_chain5.py` (Phase VIII §5.3), artifact `audit/results/phase8_chain_m5.json` (recorded 1756.6236927509308 s, about 29.3 min). Command: `python -u -I audit/phase8_chain5.py 5` (default type 59).
It is the exact rational Rayleigh quotient of the rounded eigenvector (scale 2^22, integer real and imaginary parts) of the pinned patch operator 24 − A_U on the legal patch σ⁵(τ_59), 884 736 tiles (operator dim 1 769 472). Type 59 is a Φ self-loop (child index 5) in `types_sorted()`. By compression / Rayleigh–Ritz, E_* ≤ λ_min(patch) ≤ (v, Hv)/(v, v) = 95969095435322528/10950092349041091 = 8.7642270381150369….
The float eigsh value (stored 8.764227037707025, residual 5.04e-12) is only used to produce the vector; the bound that is claimed is the exact rational.

An independent Phase XI reimplementation (`audit/phase11_fr30_upper.py 5`, stored `phase11_fr30_upper.json`) gives a slightly looser exact rational 6534049968655174/745536364613169 = 8.764227043499680…, 5.38×10^{-9} above Phase VIII (historical runtime about 36 min). That script was not re-run here. Its 10-decimal outward ceiling is 8.7642270435, consistent with but weaker than the paper print.

## Labels
- Paper FIG5-ESTAR: [E] (unchanged). Source certificate: [C] (unchanged; not re-derived at m=5 in this item).
- Outward arithmetic of the stored rational: [C], recomputed here.
- m=3 same-script rerun: [C].
- m=5 certificate: not re-derived; remains the stored source [C].
- Phase IX remains unratified. **claims.csv: no change. v0.6 not touched. No Phase IX ratification ask.**
- No Theorem F / fade / CH-V-020 / hull / Bragg upgrade.

## Method / provenance
Source repo /workspace/chair44-repo HEAD ee5d2906ec62547f3f90b3c1b4df5174949b7c0f (git status clean afterwards; not edited). Scratch copy at /workspace/fig5-rederive-upper/ (audit tree only) with the existing fig5-rederive venv (numpy 2.5.4, scipy 1.18.1, sympy 1.14.0) and OMP/OPENBLAS/MKL/NUMEXPR threads = 1. Run with python -I.

Source hashes (sha256):
- audit/phase8_chain5.py 0d04566c9eb80304fbb6e4c09740c5286ac1bce09af3812f6d81bbd41676342e
- audit/phase8_env_fiber.py f0395345630fa4e0454bb48a787af1216bc9ac7d0ad188236544b66ebd1d440f
- audit/phase8_patch_bounds.py 47b2304f4c4f87fe879d1765c250f3679c27bc1410e6a585f42291af5cf29472
- audit/phase7_local.py 4ab271b4fd66b322c5c9591acf8de26002b0f75f7e4ec11adf074d50370e3404
- audit/phase7b_local_rules.py 0ccfe965f1b59963af435f9ec802fb43effb2ae8bb1360286e0f6bfb59db45fd
- audit/phase11_fr30_upper.py d67df8cd9a7ac00b1e891de8cb8ec4e438bd30ad7ef3faff7a2bcebd5ca976bf
- results/phase8_chain_m5.json (stored) 071b1715e1842d66eec58e2914329ce31cd5d034e51d17e73ffebfdec7231d79
- results/phase11_fr30_upper.json (stored) 48d716c084883889b771505f181c5d48872d1e2f53307ef02eae0f52fdad8b06

Commands and results (times in America/Los_Angeles, PST):
- Arithmetic: Python `fractions` + `Decimal` at 80 digits. 95969095435322528/10950092349041091 = 8.7642270381150369…. 10-decimal ceiling 8.7642270382; 10-decimal floor/truncation 8.7642270381 lies strictly below the exact value.
- `python -u -I audit/phase8_chain5.py 3` (20:02 PT): type 59, 13824 tiles, dim 27648, nnz 247728, 2.21 s. lambda_float = 8.779532745837216 (residual 4.0e-13); exact Rayleigh 3957159321564128/450725503977001 = 8.779532745868423 (above the float λ, as required). Agrees at 1e-15 with the stored Phase VIII patch-bounds U_3(τ_59) = 8.779532745837136.
- `python -u -I audit/phase8_chain5.py 5` attempt 1 (started ~20:02 PT): at 3 s, 884736 tiles; at 17 s, operator dim 1769472, nnz 16240560. Then SIGKILL during eigsh. dmesg 20:04:56–58 PT: global OOM, no swap; concurrent large python tasks were also present. Job RSS was about 2.5 GiB after the operator was built.
- Attempt 2 (exact same command, started 20:32:08 PT): logged 884736 tiles at 3 s; the process was gone by 20:32:20 PT, when the kernel OOM-killed a python at 5.16 GiB anon-rss. Operator assembly did not finish in the log. No third attempt was made, to avoid further OOM on a contended box.

New artifacts in fig5-rederive-logs-2026-11-09/ (sha256): stored_phase8_chain_m5.json 071b1715e1842d66eec58e2914329ce31cd5d034e51d17e73ffebfdec7231d79; stored_phase11_fr30_upper.json 48d716c084883889b771505f181c5d48872d1e2f53307ef02eae0f52fdad8b06; phase8_chain5_m3.log 8e21b5df030c54232e5909b463f1e83c672cae5276009d464450ca4fde4b5ae8; rerun_phase8_chain_m3.json 19af5db19ad246cd58d21328eb09fa10126253476099e4b2e303466e636cc08c; phase8_chain5_m5_attempt1_oom.log 343f5ad828be317a65591cf705b559c3c7ee37e2de1af66cd50461321a216d2c; phase8_chain5_m5_attempt2_oom.log b66cd6e129979c2871f4b169902e3eb4ed8351c32765ccbd43878e63247dab96; phase8_chain5_m5_attempt2_mem.log fa44e900b7a50905c39466f8063249dbcc4c9b0a65cff20e390bf40c4cb8c60c.

## Limits of this claim
This work is a re-run of the same Phase VIII script, not an independent reimplementation (Phase XI is a stored independent chain, not re-run). I did not re-prove the compression or legality argument. The m=5 rational was not regenerated, so MATCH/gap at the certificate itself is not claimed. The job is CPU-feasible in about half an hour and does not need a GPU; it needs a few GiB of free RAM on a quiet box. A follow-up can rerun `OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 python -u -I audit/phase8_chain5.py 5` from a scratch copy (never the source repo) when this 15 GiB box has a clear margin of about 6 GiB for about 30 min. Independent reimplementation remains a leftover. An L-uniform T7 bound stays [X].
