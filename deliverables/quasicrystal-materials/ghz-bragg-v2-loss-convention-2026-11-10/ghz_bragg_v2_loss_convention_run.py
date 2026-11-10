# Runs the loss-convention addendum in this folder
# (PREREG_GHZ_BRAGG_v2_ADDENDUM_LOSS_CONVENTION_2026-11-09.md).
# This public-copy runner pins the redacted-and-paraphrased addendum in this folder and
# eta0_baselines.json (the two eta = 0 T(f0) values only).
# python3 -I, numpy only. CPU only. Does not edit any frozen original.
# TR copied from the v2 runner (sha256 8e562b71...) with ONE change only:
# v_c = v * sqrt(1 + i eta) (principal root), i.e. M -> M(1 + i eta) (C1).
import hashlib
import json
import os

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
PINS = {
    "addendum": (os.path.join(HERE, "PREREG_GHZ_BRAGG_v2_ADDENDUM_LOSS_CONVENTION_2026-11-09.md"),
                 "d4e473db20d57eeb33c98bcb54d89fc84713687905dfd0246793b7d4ce54f96f"),
    "eta0_baselines": (os.path.join(HERE, "eta0_baselines.json"),
                       "5e8bc5fb11246573ee897faaaa634d95e6b5461921d93fd5aac4fee462e1edd3"),
}
# Parent v2 prereg (file not reproduced in this folder):
# PREREG_GHZ_BRAGG_v2_2026-11-09.md
# sha256 33338a45bea89082d89601d02ed87814273a7833d5a908eb664b25702f991e36
# Original v2 results JSON (not reproduced in this folder; the two eta=0
# T(f0) values were copied from it into eta0_baselines.json):
# sha256 6475ff5ab93536678ec80d8408aa105c17e3c66a5972c2868f5cdbb2702da892
hashes = {}
for key, (p, want) in PINS.items():
    h = hashlib.sha256(open(p, "rb").read()).hexdigest()
    if h != want:
        raise SystemExit("REFUSE: %s hash mismatch: %s != %s" % (key, h, want))
    hashes[key] = {"path": os.path.basename(p), "sha256": h}

# Material constants [A], identical to v2. No new values.
MAT = {"Si": (2330.0, 8430.0), "W": (19300.0, 5230.0), "SiO2": (2200.0, 5970.0)}
LET = {"A": "W", "B": "SiO2"}
f0 = 2.0e9
tau = (1.0 + np.sqrt(5.0)) / 2.0
vA = MAT["W"][1]
vB = MAT["SiO2"][1]
dB = (1.0 / (2.0 * f0)) / (tau / vA + 1.0 / vB)
dA = tau * dB
D_TAU = {"A": dA, "B": dB}

def fib(n):
    s = {1: "B", 2: "A"}
    for k in range(3, n + 1):
        s[k] = s[k - 1] + s[k - 2]
    return s[n]

def per_word(n):
    return ("AB" * n)[:n]

FIB21 = fib(8)
FIB13 = fib(7)
PER21 = per_word(21)
PER13 = per_word(13)
assert len(FIB21) == 21 and FIB21.count("A") == 13 and FIB21.count("B") == 8
assert len(FIB13) == 13 and FIB13.count("A") == 8 and FIB13.count("B") == 5
assert PER21 == "AB" * 10 + "A" and len(PER21) == 21
assert PER13 == "AB" * 6 + "A" and len(PER13) == 13

def vc_z(rho, v, eta):
    # C1: v_c = v * sqrt(1 + i eta), principal branch (the ONLY change vs v2)
    vc = v * np.sqrt(np.complex128(1.0 + 1j * eta))
    return vc, rho * vc

def TR(word, f, thicknesses, eta):
    f = np.atleast_1d(np.asarray(f, dtype=float))
    M11 = np.ones_like(f, dtype=complex)
    M12 = np.zeros_like(f, dtype=complex)
    M21 = np.zeros_like(f, dtype=complex)
    M22 = np.ones_like(f, dtype=complex)
    for ch in word:
        m = LET[ch]
        rho, v = MAT[m]
        vc, z = vc_z(rho, v, eta)
        d = thicknesses[ch]
        k = 2.0 * np.pi * f / vc
        kd = k * d
        c = np.cos(kd)
        s = np.sin(kd)
        a11, a12, a21, a22 = c, 1j * z * s, 1j * s / z, c
        M11, M12, M21, M22 = (
            M11 * a11 + M12 * a21,
            M11 * a12 + M12 * a22,
            M21 * a11 + M22 * a21,
            M21 * a12 + M22 * a22,
        )
    # Si half-spaces always lossless
    rho_s, v_s = MAT["Si"]
    Zs = rho_s * v_s
    den = M11 + M12 / Zs + M21 * Zs + M22
    t = 2.0 / den
    r = (M11 + M12 / Zs - M21 * Zs - M22) / den
    R = np.abs(r) ** 2
    T = np.abs(t) ** 2
    return R, T

def bands(f, T, thr=1e-2, minw=5e6):
    out = []
    inb = T < thr
    i = 0
    n = len(f)
    while i < n:
        if inb[i]:
            j = i
            while j + 1 < n and inb[j + 1]:
                j += 1
            if f[j] - f[i] >= minw:
                out.append({
                    "lo_GHz": float(f[i] / 1e9),
                    "hi_GHz": float(f[j] / 1e9),
                    "w_GHz": float((f[j] - f[i]) / 1e9),
                    "minT_dB": float(10.0 * np.log10(max(T[i:j + 1].min(), 1e-300))),
                    "edge_open": bool(i == 0 or j == n - 1),
                })
            i = j + 1
        else:
            i += 1
    return out

def band_at(bl, x_GHz):
    return next((b for b in bl if b["lo_GHz"] <= x_GHz <= b["hi_GHz"]), None)

def t_db(T):
    T = float(T)
    if T <= 0:
        return float("-inf")
    return float(10.0 * np.log10(T))

FMIN = 0.05e9
FMAX = 6.5e9
N_MAIN = 20001
f_main = np.linspace(FMIN, FMAX, N_MAIN)
B0_LO, B0_HI = 1.6e9, 2.4e9
ETAS = [1e-4, 1e-3, 1e-2]  # [A]; eta = 0 NOT re-run
STACKS = {"PER21_tau": PER21, "FIB21_tau": FIB21, "PER13_tau": PER13, "FIB13_tau": FIB13}
SCORED = ("PER21_tau", "FIB21_tau")
FLOOR = 1e-10

res = {
    "addendum": "PREREG_GHZ_BRAGG_v2_ADDENDUM_LOSS_CONVENTION_2026-11-09.md",
    "pins": hashes,
    "cited_parent_prereg": {
        "file": "PREREG_GHZ_BRAGG_v2_2026-11-09.md",
        "sha256": "33338a45bea89082d89601d02ed87814273a7833d5a908eb664b25702f991e36",
        "reproduced_in_this_folder": False,
    },
    "convention": "C1: M -> M(1 + i eta), v_c = v*sqrt(1 + i eta) principal; W and SiO2 only; Si lossless",
    "labels": {"materials_eta": "[A]", "computed": "[E]", "failed_gates": "[F]"},
    "thicknesses_tau_m": {"A_W": float(dA), "B_SiO2": float(dB), "ratio": float(dA / dB)},
    "etas": ETAS,
    "grid": {"fmin_Hz": FMIN, "fmax_Hz": FMAX, "N_main": N_MAIN},
    "B0_Hz": [B0_LO, B0_HI],
    "floor": FLOOR,
}

# --- V_L0: single W layer d_A between lossless Si, eta = 1e-3 ---
R1, T1 = TR("A", f_main, D_TAU, 1e-3)
A1 = 1.0 - R1 - T1
R1f, T1f = TR("A", f0, D_TAU, 1e-3)
A1f = float(1.0 - R1f[0] - T1f[0])
VL0 = {
    "eta": 1e-3,
    "d_A_m": float(dA),
    "min_Aabs": float(A1.min()),
    "max_Aabs": float(A1.max()),
    "Aabs_f0": A1f,
    "max_T": float(T1.max()),
    "max_R": float(R1.max()),
}
VL0["pass"] = bool(VL0["min_Aabs"] >= -FLOOR and A1f > 0.0)
res["V_L0"] = VL0

# --- main lossy runs + V_L ---
runs = {}
VL = {}
for eta in ETAS:
    ek = "eta_%g" % eta
    runs[ek] = {"eta": eta, "stacks": {}}
    VL[ek] = {}
    for name, word in STACKS.items():
        R, T = TR(word, f_main, D_TAU, eta)
        A = 1.0 - R - T
        Rf, Tf = TR(word, f0, D_TAU, eta)
        _, T2 = TR(word, 2.0 * f0, D_TAU, eta)
        Tf0 = float(Tf[0]); Rf0 = float(Rf[0]); T2v = float(T2[0])
        mask = (f_main >= B0_LO) & (f_main <= B0_HI)
        Tpeak = float(T[mask].max())
        b = bands(f_main, T)
        bf0 = band_at(b, 2.0)
        v = {
            "min_Aabs": float(A.min()),
            "Aabs_f0": float(1.0 - Rf0 - Tf0),
            "max_Aabs": float(A.max()),
            "max_T": float(T.max()),
            "max_R": float(R.max()),
            "min_T": float(T.min()),
            "min_R": float(R.min()),
        }
        v["pass"] = bool(v["min_Aabs"] >= -FLOOR and v["min_R"] >= -FLOOR and v["min_T"] >= -FLOOR
                         and v["max_R"] <= 1.0 + FLOOR and v["max_T"] <= 1.0 + FLOOR)
        VL[ek][name] = v
        runs[ek]["stacks"][name] = {
            "word": word, "n": len(word), "nA": word.count("A"), "nB": word.count("B"),
            "T_f0": Tf0, "T_f0_dB": t_db(Tf0), "R_f0": Rf0,
            "T_2f0": T2v, "T_2f0_dB": t_db(T2v),
            "T_peak_B0": Tpeak, "S_B0_dB": -t_db(Tpeak) if Tpeak > 0 else float("inf"),
            "stop_bands": b,
            "band_containing_f0": bf0,
            "fracwidth_f0_band": ((bf0["hi_GHz"] - bf0["lo_GHz"]) / 2.0) if bf0 else None,
            "Aabs_f0": v["Aabs_f0"], "Aabs_max_grid": v["max_Aabs"],
        }
res["runs"] = runs

voiding = []
untrusted = []
for ek in VL:
    for name in VL[ek]:
        if not VL[ek][name]["pass"]:
            if name in SCORED and ek in ("eta_0.001", "eta_0.01"):
                voiding.append("%s/%s" % (ek, name))
            else:
                untrusted.append("%s/%s" % (ek, name))
res["V_L"] = {"per_eta_stack": VL, "voiding_failures": voiding, "untrusted_nonvoiding": untrusted,
              "voiding_pass": bool(len(voiding) == 0),
              "all_pass": bool(len(voiding) == 0 and len(untrusted) == 0)}

# --- eta = 0 baselines from the derived file (not recomputed; not the v2 JSON) ---
base = json.load(open(PINS["eta0_baselines"][0]))
T0_F = float(base["stacks"]["FIB21_tau"]["T_f0"])
T0_P = float(base["stacks"]["PER21_tau"]["T_f0"])

def sign_cmp(a, b):
    if a < b:
        return "FIB<PER"
    if a > b:
        return "FIB>PER"
    return "equal"

cmp0 = sign_cmp(T0_F, T0_P)
scored_ok = bool(VL0["pass"] and res["V_L"]["voiding_pass"])
hyp = {}
for hk, ek in (("H7_eta_1e-3_ranking_stable", "eta_0.001"), ("H8_eta_1e-2_ranking_stable", "eta_0.01")):
    TF = runs[ek]["stacks"]["FIB21_tau"]["T_f0"]
    TP = runs[ek]["stacks"]["PER21_tau"]["T_f0"]
    c = sign_cmp(TF, TP)
    raw = bool(cmp0 != "equal" and c == cmp0)
    if not scored_ok:
        mark = "VOID"
    else:
        mark = "PASS [E]" if raw else "FAIL [F]"
    hyp[hk] = {"mark": mark, "cmp_eta0": cmp0, "cmp_eta": c,
               "T_FIB_eta0_baseline": T0_F, "T_PER_eta0_baseline": T0_P,
               "T_FIB": TF, "T_PER": TP, "ratio_FIB_over_PER": TF / TP if TP > 0 else None}
res["hypotheses"] = hyp
res["verdict"] = {
    "V_L0": VL0["pass"], "V_L_voiding_pass": res["V_L"]["voiding_pass"], "V_L_all_pass": res["V_L"]["all_pass"],
    "H7": hyp["H7_eta_1e-3_ranking_stable"]["mark"], "H8": hyp["H8_eta_1e-2_ranking_stable"]["mark"],
    "isolator_advantage": "FAIL [F] (from eta=0, v2; unchanged by this addendum)",
    "overall_mark": None,
}

def default(o):
    if isinstance(o, np.bool_):
        return bool(o)
    if isinstance(o, np.integer):
        return int(o)
    if isinstance(o, np.floating):
        return float(o)
    return str(o)

outp = os.path.join(HERE, "results_ghz_bragg_v2_loss_convention.json")
json.dump(res, open(outp, "w"), indent=1, default=default)
print(json.dumps({"V_L0": VL0, "V_L": {ek: {n: VL[ek][n] for n in VL[ek]} for ek in VL},
                  "voiding": voiding, "untrusted": untrusted, "hyp": hyp, "verdict": res["verdict"],
                  "desc": {ek: {n: {k: runs[ek]["stacks"][n][k] for k in
                           ("T_f0", "T_2f0", "T_peak_B0", "S_B0_dB", "band_containing_f0", "Aabs_f0", "Aabs_max_grid")}
                           for n in SCORED} for ek in runs}}, indent=1, default=default))
