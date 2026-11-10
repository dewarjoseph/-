# GHz Bragg v2 loss-convention addendum: public copy, revision 3

This is a 1D, normal-incidence, longitudinal-only transfer-matrix model of W/SiO2 tau-thickness acoustic Bragg stacks near f0 = 2.0 GHz (periodic and Fibonacci). It is not a measured specimen and not a 3D model. The addendum corrects the lossy-modulus sign to M(1 + i eta) so that it matches the e^{+i ω t} transfer matrix (see the result note), and re-runs only the lossy etas 1e-4, 1e-3, and 1e-2, each [A].

To run it: from the folder `public_copy_loss_convention_v3_2026-11-10/`, first run `sha256sum -c MANIFEST.sha256`. Then run `python3 -I ghz_bragg_v2_loss_convention_run.py`. It needs numpy only. It reads the pinned addendum and `eta0_baselines.json` (the two eta = 0 T(f0) values only) and rehashes both before use. A standalone run should write `results_ghz_bragg_v2_loss_convention.json` with sha256 39b8a8345d0b8e4156ea14158a0ffe2047d7dfd2d50a73dd16dad3736150038b. The folder's `MANIFEST.sha256` lists every file's sha256.

The labels as they stand:
- Isolator advantage at eta = 0 is FAIL [F]. This addendum adds no new overall mark. The withdrawn v2 H7/H8 PASS marks stay withdrawn.
- V_L0 and V_L passivity checks are PASS [E].
- H7 and H8 are PASS [E] at the sampled eta values 1e-3 and 1e-2 only (eta = 1e-4 is descriptive). That ranking still disfavours Fibonacci and is not isolator-advantage evidence. The marks are not evidence about measured films. Eta is labelled [A].
- Infima stay [X]. TLS stays [X] and is not modelled.

The parent v2 preregistration is not public. It is cited by its sha256 only (33338a45bea89082d89601d02ed87814273a7833d5a908eb664b25702f991e36) and is not included. The v2 runner (sha256 8e562b7167f7fa729d9e2aa79859ee73456f1592b8b50a60e4d801c956b21436) and the v2 result note (sha256 a36c34605df555f0b3aa72dae19ddb3a1bc6c8fd31051c929d69dcd408532a92) are cited by hash only and are not included.

This copy claims nothing beyond what `RESULT_GHZ_BRAGG_v2_LOSS_CONVENTION_2026-11-09.md` in the folder reports.
