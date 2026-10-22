#!/usr/bin/env python3
"""Phase V-E analysis: frozen criteria C1-C8 (deliverables/PHASE5E_PROTOCOL.md) on the level-4 / level-3 / level-sweep / adaptive
/ gauge / closure outputs of audit/phase5e_run.py.  Writes audit/results/phase5e_results.{json,csv,txt}.

Held-out regressions reuse V-D's ridge/CV machinery (audit/phase5d_analyze.py) unchanged: rule-level 10-fold CV, 20 repetitions,
fold permutation = default_rng(20261024 + r).permutation(264) exactly as in V-D; ridge alpha by inner 5-fold CV.  The new models
M7:<family> = flux (f_trl, f_m1) + E_W(primary configuration of the family) and the V-D baselines M0, M2, M4, M6 are refitted in the
same loop (so they share folds); V-D's frozen numbers are reported alongside.
"""
import os, sys, json, glob, csv
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); RES = os.path.join(HERE, 'results')
import types
try:
    import resource  # noqa: F401
except ImportError:
    sys.modules['resource'] = types.SimpleNamespace(getrusage=lambda *a: types.SimpleNamespace(ru_maxrss=0), RUSAGE_SELF=0)
import numpy as np
import phase5d_analyze as va

PRIMARY = {'child': 16, 'face': 4, 'iface2': 8, 'fec': 2, 'patch2': 4, 'adaptive': 229}
DIM_S = 4592; CAP = 459
VD_FROZEN = {'M0': (0.7986, 0.0011, 0.2727), 'M2': (0.8900, 0.0008, 0.2015), 'M4': (0.9174, 0.0018, 0.1747), 'M6': (0.9714, 0.0013, 0.1027)}

def jl(pattern, kind=None):
    """records keyed by name; FR30 occurs both as a rule class and as the reference control, so `kind` selects which."""
    out = {}
    for fn in sorted(glob.glob(os.path.join(RES, pattern))):
        for l in open(fn):
            try: r = json.loads(l)
            except json.JSONDecodeError: continue
            if kind is None or r.get('kind') == kind: out[str(r['name'])] = r
    return out

def merge_adaptive(L4, AD):
    for nm, r in AD.items():
        if nm in L4:
            for k, v in r['bases'].items(): L4[nm]['bases'][k] = v
    return L4

def cfg_key(fam, k): return f'{fam}:{k}'
def pct(vals, v): return float((np.asarray(vals) < v).mean() * 100)

def folds_rep0(n):
    rng = np.random.default_rng(va.SEED0); perm = rng.permutation(n); return np.array_split(perm, 10)

def main():
    L4 = merge_adaptive(jl('phase5e_L4_shard*.jsonl', 'rule'), jl('phase5e_adaptive_L4_shard*.jsonl', 'rule'))
    L4C = merge_adaptive(jl('phase5e_L4_shard*.jsonl', 'control'), jl('phase5e_adaptive_L4_shard*.jsonl', 'control'))
    L4D = jl('phase5e_L4_shard*.jsonl', 'dev')
    L3 = jl('phase5e_L3_shard*.jsonl'); LV = [json.loads(l) for fn in sorted(glob.glob(os.path.join(RES, 'phase5e_levels_*.jsonl'))) for l in open(fn)]
    vd_recs, pred = va.load(); vd_recs = sorted(vd_recs, key=lambda r: r['index'])
    rules = [r for r in vd_recs]; names = ['fr30' if r['is_fr30'] else str(r['index']) for r in rules]; n = len(rules)
    have = [nm in L4 for nm in names]
    lines = []; P = lambda s='': (print(s), lines.append(s))
    P("PHASE V-E: COMPRESSIONS OF THE EXACT BOUNDARY RESPONSE -- FROZEN EVALUATION (deliverables/PHASE5E_PROTOCOL.md)")
    P(f" level-4 records: rules {sum(have)}/{n}, controls {len(L4C)}/18, dev {len(L4D)}/4; level-3 records {len(L3)}; level-sweep records {len(LV)}")
    if not all(have): P(" WARNING: incomplete level-4 rule set; criteria below are provisional");
    idx = [i for i in range(n) if have[i]]; nm_ok = [names[i] for i in idx]
    Y = np.array([rules[i]['Y4'] for i in idx]); E0 = np.array([L4[nm]['E0'] for nm in nm_ok])
    P(f" re-derived bottoms vs stored Y4: max |E0 - Y4| = {np.abs(E0 - Y).max():.2e}")
    # ---------------------------------------------------------------- per-configuration table
    keys = sorted({k for nm in nm_ok for k in L4[nm]['bases']}, key=lambda k: (k.split(':')[0], float(k.split(':')[1]) if k.split(':')[1] not in ('None',) else 1e9))
    folds = folds_rep0(len(idx)); table = {}
    for k in keys:
        rows = [L4[nm]['bases'].get(k) for nm in nm_ok]
        if any(r is None or r.get('E_W') is None for r in rows): continue
        Ew = np.array([r['E_W'] if r['E_W'] == r['E_W'] else np.nan for r in rows]); err = Ew - E0
        D = int(np.median([r['D'] for r in rows])); cap = np.array([r.get('capture', np.nan) for r in rows])
        cal = np.full(len(idx), np.nan)
        for te in folds:
            tr = np.setdiff1d(np.arange(len(idx)), te); cal[te] = err[te] - np.nanmean(err[tr])
        sec = np.array([r.get('seconds', np.nan) for r in rows]); nev = np.array([r.get('nev', r.get('it', np.nan)) for r in rows])
        table[k] = {'family': k.split(':')[0], 'param': k.split(':')[1], 'D': D, 'D_frac': D / DIM_S, 'n': int(np.isfinite(err).sum()), 'no_root': int(np.isnan(err).sum()),
                    'raw_mean': float(np.nanmean(err)), 'raw_rmse': float(np.sqrt(np.nanmean(err ** 2))), 'raw_max': float(np.nanmax(err)), 'raw_min': float(np.nanmin(err)),
                    'cal_rmse': float(np.sqrt(np.nanmean(cal ** 2))), 'cal_max': float(np.nanmax(np.abs(cal))), 'cal_p95': float(np.nanpercentile(np.abs(cal), 95)),
                    'capture_median': float(np.nanmedian(cap)), 'capture_min': float(np.nanmin(cap)), 'seconds_mean': float(np.nanmean(sec)), 'evals_mean': float(np.nanmean(nev)),
                    'spearman_EW_Y4': float(spearman(Ew, Y)), 'pearson_EW_Y4': float(np.corrcoef(np.nan_to_num(Ew, nan=np.nanmax(Ew)), Y)[0, 1])}
    P(); P(f" {'configuration':<16} {'D':>5} {'D/dimS':>7} | {'raw mean':>8} {'raw RMSE':>8} {'raw max':>8} | {'cal RMSE':>8} {'cal max':>8} {'p95':>6} | {'capture':>7} | {'rho(E_W,Y4)':>11} | {'s':>5}")
    for k, t in table.items():
        P(f" {k:<16} {t['D']:>5} {t['D_frac']:7.3f} | {t['raw_mean']:8.4f} {t['raw_rmse']:8.4f} {t['raw_max']:8.4f} | {t['cal_rmse']:8.4f} {t['cal_max']:8.4f} {t['cal_p95']:6.3f} | {t['capture_median']:7.4f} | {t['spearman_EW_Y4']:11.3f} | {t['seconds_mean']:5.1f}")
    # matched dimensions (log-interpolated raw and calibrated RMSE per family)
    matched = {}
    for fam in sorted({t['family'] for t in table.values()}):
        pts = sorted((t['D'], t['raw_rmse'], t['cal_rmse']) for t in table.values() if t['family'] == fam)
        if len(pts) < 2: continue
        Ds = np.log([p[0] for p in pts])
        matched[fam] = {str(Dm): {'raw_rmse': float(np.interp(np.log(Dm), Ds, [p[1] for p in pts], left=np.nan, right=np.nan)),
                                  'cal_rmse': float(np.interp(np.log(Dm), Ds, [p[2] for p in pts], left=np.nan, right=np.nan))} for Dm in (64, 128, 256, 459, 512)}
    P(); P(" matched retained dimension (log-linear interpolation in D; nan = outside the family's grid): raw RMSE / calibrated RMSE")
    for fam, m in matched.items(): P(f"   {fam:<10} " + "  ".join(f"D={k}: {v['raw_rmse']:.3f}/{v['cal_rmse']:.3f}" for k, v in m.items()))
    # ---------------------------------------------------------------- held-out regressions (V-D machinery)
    recs_ok = [rules[i] for i in idx]; y = Y
    def X_of(model, rec_list, ew=None):
        if model.startswith('M7'):
            return np.array([[pred[r['index']]['f_trl'], pred[r['index']]['f_m1'], e] for r, e in zip(rec_list, ew)], float)
        return np.array([va.design(r, model, pred[r['index']], r['feat']) for r in rec_list], float)
    fams = [f for f in PRIMARY if cfg_key(f, PRIMARY[f]) in table] + (['interface'] if 'interface:None' in table else [])
    ewcol = {f: np.array([L4[nm]['bases'][cfg_key(f, PRIMARY.get(f))]['E_W'] for nm in nm_ok]) for f in fams}
    for f in fams:                                                     # no root in the window -> lambda_II (E3 convention)
        lam = np.array([L4[nm]['lam_II'] for nm in nm_ok]); ewcol[f] = np.where(np.isnan(ewcol[f]), lam, ewcol[f])
    models = ['M0', 'M2', 'M4', 'M6'] + [f'M7:{f}' for f in fams]
    Xs = {m: (X_of(m, recs_ok, ewcol[m[3:]]) if m.startswith('M7') else X_of(m, recs_ok)) for m in models}
    res = {m: {'r2': [], 'rmse': [], 'frac': []} for m in models}
    for rep in range(va.NREP):
        rng = np.random.default_rng(va.SEED0 + rep); perm = rng.permutation(len(y)); fl = np.array_split(perm, 10); preds = {m: np.empty(len(y)) for m in models}
        for te in fl:
            tr = np.setdiff1d(perm, te)
            for m in models: f_, _ = va.fit_cv(Xs[m][tr], y[tr], rng); preds[m][te] = f_(Xs[m][te])
        ss0 = ((y - preds['M0']) ** 2).sum(); sst = ((y - y.mean()) ** 2).sum()
        for m in models:
            ss = ((y - preds[m]) ** 2).sum(); res[m]['r2'].append(1 - ss / sst); res[m]['rmse'].append(np.sqrt(ss / len(y))); res[m]['frac'].append(1 - ss / ss0)
    summ = {m: {k: (float(np.mean(v)), float(np.std(v))) for k, v in res[m].items()} for m in models}
    P(); P(" HELD-OUT (V-D CV: 20 x 10-fold, seeds 20261024+r): CV-R2, CV-RMSE, flux-residual variance explained")
    for m in models: P(f"   {m:<16} {summ[m]['r2'][0]:.4f} +- {summ[m]['r2'][1]:.4f}   {summ[m]['rmse'][0]:.4f}   {summ[m]['frac'][0]:+.4f} +- {summ[m]['frac'][1]:.4f}")
    P(f"   V-D frozen: M0 {VD_FROZEN['M0'][0]}, M2 {VD_FROZEN['M2'][0]}, M4 {VD_FROZEN['M4'][0]}, M6 {VD_FROZEN['M6'][0]}")
    # leave-FR30-out and interventions
    fr = [j for j, nm in enumerate(nm_ok) if nm == 'fr30']; out_fr = {}
    if fr:
        i = fr[0]; tr = np.setdiff1d(np.arange(len(y)), [i]); rng = np.random.default_rng(va.SEED0)
        f0, _ = va.fit_cv(Xs['M0'][tr], y[tr], rng); base = float(f0(Xs['M0'][[i]])[0])
        P(); P(f" leave-FR30-out: Y4 {y[i]:.5f}, flux-only {base:.5f} (residual {y[i]-base:+.4f})")
        for m in models[1:]:
            fm, a = va.fit_cv(Xs[m][tr], y[tr], rng); p = float(fm(Xs[m][[i]])[0]); out_fr[m] = (p - base) / (y[i] - base)
            P(f"   {m:<16} predicted {p:.5f}; fraction of FR30's flux residual explained {out_fr[m]:+.3f}")
    ctl = L4C; out_ctl = {}
    cpred = {json.loads(l)['system']: json.loads(l)['pred'] for l in open(os.path.join(RES, 'phase5b_controls.jsonl')) if json.loads(l)['level'] == 4}
    vdc = {json.loads(l)['system']: json.loads(l) for l in open(os.path.join(RES, 'phase5d_controls.jsonl'))}
    cnames = [c for c in vdc if c in ctl]
    if cnames and fr:
        rng = np.random.default_rng(va.SEED0); fits = {m: va.fit_cv(Xs[m], y, rng)[0] for m in models}
        yc = np.array([vdc[c]['Y4'] for c in cnames])
        Xc0 = np.array([[cpred[c]['f_trl'], cpred[c]['f_m1']] for c in cnames]); base = fits['M0'](Xc0); r_act = yc - base
        y_fr = vdc['fr30']['Y4']; P(); P(" INTERVENTIONS (18 controls; never in training)")
        for f in fams:
            k = cfg_key(f, PRIMARY.get(f)); ew = np.array([ctl[c]['bases'][k]['E_W'] if ctl[c]['bases'].get(k) else np.nan for c in cnames])
            lamc = np.array([ctl[c]['lam_II'] for c in cnames]); ew = np.where(np.isnan(ew), lamc, ew)
            pm = fits[f'M7:{f}'](np.c_[Xc0, ew]); r_pred = pm - base
            ifr = cnames.index('fr30'); dEW = ew - ew[ifr]; dY = yc - y_fr; oth = [j for j in range(len(cnames)) if j != ifr]
            sign_raw = int(sum(np.sign(dEW[j]) == np.sign(dY[j]) for j in oth)); big = [j for j in range(len(cnames)) if abs(r_act[j]) >= 0.05]
            sign_res = int(sum(np.sign(r_pred[j]) == np.sign(r_act[j]) for j in big)); cc = float(np.corrcoef(r_pred, r_act)[0, 1])
            out_ctl[f] = {'sign_raw_correct': sign_raw, 'n_raw': len(oth), 'sign_res_correct': sign_res, 'n_res': len(big), 'corr': cc,
                          'mean_abs_err': float(np.abs(r_pred - r_act).mean()), 'per_control': {c: {'r_act': float(r_act[j]), 'r_pred': float(r_pred[j]), 'dY': float(dY[j]), 'dEW': float(dEW[j]), 'EW': float(ew[j])} for j, c in enumerate(cnames)}}
            P(f"   M7:{f:<10} raw-direction {sign_raw}/{len(oth)}  residual-sign {sign_res}/{len(big)}  corr {cc:+.3f}  mean|err| {out_ctl[f]['mean_abs_err']:.3f}")
    # ---------------------------------------------------------------- theorem checks (E3, E4) on every level-4 record
    viol3 = viol4u = viol4l = 0; tot = 0; slack = []
    for nm, r in list(L4.items()) + [('c:' + k_, v_) for k_, v_ in L4C.items()] + [('d:' + k_, v_) for k_, v_ in L4D.items()]:
        for k, b in r['bases'].items():
            if b.get('E_W') is None or b['E_W'] != b['E_W'] or b.get('ritz_defect') is None: continue
            tot += 1; e = b['E_W'] - r['E0']; gd = b['ritz_defect']; c = b.get('capture', np.nan)
            if e < -1e-9 or e > gd + 1e-9: viol3 += 1
            if c > 0 and gd > (48 - r['E0']) * (1 - c) / c + 1e-9: viol4u += 1
            mu2lb = min(r['gap'], r['lam_II'] - r['E0']) if r['gap'] == r['gap'] else 0.0
            if gd < mu2lb * (1 - c) - 1e-9: viol4l += 1
            if gd > 0: slack.append(e / gd)
    P(); P(f" THEOREM CHECKS over {tot} (system, basis) pairs: E3 (0 <= E_W-E0 <= g_W(E0)) violations {viol3}; E4 upper ((48-E0)(1-c)/c) violations {viol4u}; "
          f"E4 lower (min(gap, lam_II-E0)(1-c)) violations {viol4l}; median (E_W-E0)/g_W(E0) = {np.median(slack):.3f}")
    # ---------------------------------------------------------------- gauge, levels, closure
    gauge = json.load(open(os.path.join(RES, 'phase5e_gauge.json'))) if os.path.exists(os.path.join(RES, 'phase5e_gauge.json')) else []
    gmax = max((g['max_dev'] for g in gauge), default=float('nan')); P(f" GAUGE: max |dE_W| over {len(gauge)} systems and all families = {gmax:.2e}")
    lev = {}
    for r in LV:
        for k, b in r['bases'].items():
            if b.get('E_W') is None or b['E_W'] != b['E_W']: continue
            lev.setdefault(k, {}).setdefault(r['level'], []).append((b['E_W'] - r['E0']) / r['E0'])
    stab = {}
    P(); P(" LEVEL SWEEP (8 systems): mean relative edge error at fixed family parameter, L = 2, 3, 4, 5")
    for k in sorted(lev, key=lambda k: (k.split(':')[0], k)):
        m = {L: float(np.mean(v)) for L, v in sorted(lev[k].items())}; stab[k] = m
        P(f"   {k:<14} " + "  ".join(f"L{L}: {v:.4f} (n={len(lev[k][L])})" for L, v in m.items()))
    supp = {}
    for r in LV:
        supp.setdefault(str(r['name']), {})[r['level']] = {k: r['support'][k] for k in ('tiles_0.5', 'tiles_0.9', 'tiles_0.99', 'tiles_0.999', 'S_tiles', 'interface_tiles')} | {'outer_weight': r['support']['class_weight'].get('outer', 0.0), 'S_weight': r['support']['S_weight'], 'gap': r['gap'], 'E0': r['E0']}
    if supp:
        P(); P(" TILE SUPPORT of psi_S (tiles holding 99% / 99.9%; interface tiles; outer-boundary weight) across levels")
        for nm, d_ in supp.items(): P(f"   {nm:<6} " + "  ".join(f"L{L}: {v['tiles_0.99']}/{v['tiles_0.999']} of {v['interface_tiles']} (outer {v['outer_weight']:.1e})" for L, v in sorted(d_.items())))
    clo = json.load(open(os.path.join(RES, 'phase5e_closure.json'))) if os.path.exists(os.path.join(RES, 'phase5e_closure.json')) else None
    # ---------------------------------------------------------------- criteria
    crit = {}
    P(); P(" FROZEN CRITERIA (primary configuration per family)")
    for f in [ff for ff in PRIMARY if cfg_key(ff, PRIMARY[ff]) in table]:
        k = cfg_key(f, PRIMARY[f]); t = table[k]; c = {}
        c['C1'] = t['D'] <= CAP
        c['C2'] = t['cal_rmse'] <= 0.05 and t['cal_max'] <= 0.15
        gd = [g['dev'].get(k) for g in gauge if g['dev'].get(k) is not None] if f != 'adaptive' else [0.0]
        c['C3'] = bool(gd) and max(gd) <= 1e-8
        m7 = summ.get(f'M7:{f}'); sd = max(summ['M4']['r2'][1], summ['M2']['r2'][1], VD_FROZEN['M4'][1])
        c['C4'] = bool(m7) and m7['r2'][0] > max(summ['M4']['r2'][0], VD_FROZEN['M4'][0], summ['M2']['r2'][0]) + 2 * sd and t['cal_rmse'] < 0.1747
        oc = out_ctl.get(f); c['C5'] = bool(oc) and oc['sign_raw_correct'] == oc['n_raw'] and oc['sign_res_correct'] == oc['n_res'] and oc['corr'] >= 0.8
        frc = (L4['fr30']['bases'][k]['E_W'] - L4['fr30']['E0'] - t['raw_mean']) if 'fr30' in L4 else float('nan')
        c['C6'] = out_fr.get(f'M7:{f}', 0) >= 0.5 and abs(frc) <= 0.10
        st = stab.get(k, {}); c7a = all(st.get(L + 1, np.inf) <= 1.5 * st[L] for L in (3, 4) if L in st) and len(st) >= 3
        c['C7'] = bool(c7a) and t['cal_p95'] <= 0.10
        c['C8'] = t['D'] <= CAP
        crit[f] = {'config': k, 'D': t['D'], **{kk: bool(v) for kk, v in c.items()}, 'pass': all(c.values()), 'fr30_cal_err': float(frc)}
        P(f"   {k:<14} D={t['D']:<4} " + " ".join(f"{kk}:{'Y' if v else 'n'}" for kk, v in c.items()) + f"  => {'PASS' if all(c.values()) else 'FAIL'}")
    P(f" families passing all criteria: {[f for f, v in crit.items() if v['pass']] or 'NONE'}")
    # ---------------------------------------------------------------- FR30 placement and exploratory energy budget
    fr_place = {}
    for f in (fams if 'fr30' in L4 else []):
        k = cfg_key(f, PRIMARY.get(f)); errs = [L4[nm]['bases'][k]['E_W'] - L4[nm]['E0'] for nm in nm_ok if L4[nm]['bases'][k]['E_W'] == L4[nm]['bases'][k]['E_W']]
        fr_place[f] = {'fr30_err': L4['fr30']['bases'][k]['E_W'] - L4['fr30']['E0'], 'percentile_of_err': pct(errs, L4['fr30']['bases'][k]['E_W'] - L4['fr30']['E0'])}
    bud = {nm: L4[nm]['budget'] for nm in L4}; bud.update({c: L4C[c]['budget'] for c in L4C if c != 'fr30'})
    if 'fr30' not in bud: bud['fr30'] = bud[nm_ok[0]]   # provisional runs only
    se = np.array([bud[nm]['seam_eff'] for nm in nm_ok]); ie = np.array([bud[nm]['intra_eff'] for nm in nm_ok]); sw = np.array([L4[nm]['support']['class_weight'].get('hinge', 0) + L4[nm]['support']['class_weight'].get('corner', 0) for nm in nm_ok])
    flux_res = y - np.array([np.polyval([0], 0) for _ in y])
    out_budget = {'fr30': bud.get('fr30'), 'seam_eff_percentile_fr30': pct(se, bud['fr30']['seam_eff']), 'intra_eff_percentile_fr30': pct(ie, bud['fr30']['intra_eff']),
                  'corr_seam_eff_Y4': float(np.corrcoef(se, y)[0, 1]), 'corr_intra_eff_Y4': float(np.corrcoef(ie, y)[0, 1]),
                  'controls': {c: bud[c] for c in cnames}}
    P(); P(f" EXPLORATORY energy budget: FR30 seam efficiency {bud['fr30']['seam_eff']:.4f} ({out_budget['seam_eff_percentile_fr30']:.0f}th pct), intra efficiency {bud['fr30']['intra_eff']:.4f} "
          f"({out_budget['intra_eff_percentile_fr30']:.0f}th pct); corr(seam_eff, Y4) {out_budget['corr_seam_eff_Y4']:+.3f}, corr(intra_eff, Y4) {out_budget['corr_intra_eff_Y4']:+.3f}")
    # EXPLORATORY: exact depth-resolved energy budget (adaptive-stage records) and the split of the flux residual by hierarchy depth.
    # E_0 = 24 + sum_d B_d exactly, and OLS on the same regressors is linear, so resid(Y) = sum_d resid(B_d) exactly.
    depth = {}
    AD = jl('phase5e_adaptive_L4_shard*.jsonl', 'rule'); ADC = jl('phase5e_adaptive_L4_shard*.jsonl', 'control')
    if all(nm in AD and 'bonds' in AD[nm] for nm in nm_ok):
        Xf = np.c_[np.ones(len(idx)), [[pred[r['index']]['f_trl'], pred[r['index']]['f_m1']] for r in recs_ok]]
        Ls = sorted(int(k) for k in AD[nm_ok[0]]['bonds'] if k != 'diag')
        B = np.array([[AD[nm]['bonds'][str(dd)]['B'] for dd in Ls] for nm in nm_ok]); Mg = np.array([[AD[nm]['bonds'][str(dd)]['M'] for dd in Ls] for nm in nm_ok])
        beta, *_ = np.linalg.lstsq(Xf, B, rcond=None); RB = B - Xf @ beta
        by, *_ = np.linalg.lstsq(Xf, y, rcond=None); ry = y - Xf @ by
        i_fr = nm_ok.index('fr30'); eta = -B / Mg
        depth = {'depths': Ls, 'check_sum_resid': float(np.abs(RB.sum(1) - ry).max()), 'fr30_resid_total': float(ry[i_fr]),
                 'fr30_resid_by_depth': {str(dd): float(RB[i_fr, j]) for j, dd in enumerate(Ls)},
                 'var_share_by_depth': {str(dd): float(np.cov(RB[:, j], ry)[0, 1] / ry.var(ddof=1)) for j, dd in enumerate(Ls)},
                 'fr30_eta_by_depth': {str(dd): float(eta[i_fr, j]) for j, dd in enumerate(Ls)},
                 'eta_percentile_fr30': {str(dd): pct(eta[:, j], eta[i_fr, j]) for j, dd in enumerate(Ls)},
                 'corr_eta_resid': {str(dd): float(np.corrcoef(eta[:, j], ry)[0, 1]) for j, dd in enumerate(Ls)}}
        ctl_ad = {c: ADC[c] for c in cnames if c in ADC and 'bonds' in ADC[c]}
        if ctl_ad:
            Xc = np.c_[np.ones(len(ctl_ad)), [[cpred[c]['f_trl'], cpred[c]['f_m1']] for c in ctl_ad]]
            Bc = np.array([[ctl_ad[c]['bonds'][str(dd)]['B'] for dd in Ls] for c in ctl_ad]); RBc = Bc - Xc @ beta
            yc_ = np.array([vdc[c]['Y4'] for c in ctl_ad]); ryc = yc_ - Xc @ by
            depth['controls'] = {c: {'resid': float(ryc[j]), 'by_depth': {str(dd): float(RBc[j, q]) for q, dd in enumerate(Ls)},
                                     'eta': {str(dd): float(-ctl_ad[c]['bonds'][str(dd)]['B'] / ctl_ad[c]['bonds'][str(dd)]['M']) for dd in Ls}} for j, c in enumerate(ctl_ad)}
        P(); P(" EXPLORATORY depth-resolved budget: flux residual of Y4 split exactly by the depth of the panels' common ancestor (0 = top seams)")
        P(f"   FR30 residual {ry[i_fr]:+.4f} = " + " + ".join(f"d{dd}: {RB[i_fr, j]:+.4f}" for j, dd in enumerate(Ls)) + f"   (sum check {depth['check_sum_resid']:.1e})")
        P("   share of residual variance (cov with total / var):  " + "  ".join(f"d{dd}: {depth['var_share_by_depth'][str(dd)]:+.3f}" for dd in Ls))
        P("   FR30 bond efficiency eta_d (percentile among 264):   " + "  ".join(f"d{dd}: {eta[i_fr, j]:.4f} ({depth['eta_percentile_fr30'][str(dd)]:.0f})" for j, dd in enumerate(Ls)))
        for c, v in depth.get('controls', {}).items(): P(f"   {c:<12} resid {v['resid']:+.3f} = " + " + ".join(f"d{dd} {v['by_depth'][str(dd)]:+.3f}" for dd in Ls))
    out = {'n_rules': len(idx), 'table': table, 'depth_budget_exploratory': depth, 'matched': matched, 'heldout': summ, 'vd_frozen': VD_FROZEN, 'fr30_leaveout': out_fr, 'interventions': out_ctl,
           'theorem_checks': {'pairs': tot, 'E3_violations': viol3, 'E4_upper_violations': viol4u, 'E4_lower_violations': viol4l, 'median_err_over_defect': float(np.median(slack))},
           'gauge_max_dev': gmax, 'level_sweep': stab, 'support': supp, 'closure': clo, 'criteria': crit, 'fr30_placement': fr_place, 'energy_budget_exploratory': out_budget}
    json.dump(out, open(os.path.join(RES, 'phase5e_results.json'), 'w'), indent=1, default=float)
    with open(os.path.join(RES, 'phase5e_results.csv'), 'w', newline='') as fh:
        w = csv.writer(fh); cols = ['family', 'param', 'D', 'D_frac', 'n', 'no_root', 'raw_mean', 'raw_rmse', 'raw_max', 'cal_rmse', 'cal_max', 'cal_p95', 'capture_median', 'capture_min', 'spearman_EW_Y4', 'seconds_mean', 'evals_mean']
        w.writerow(['configuration'] + cols)
        for k, t in table.items(): w.writerow([k] + [t[c] for c in cols])
        for m, v in VD_FROZEN.items(): w.writerow([f'V-D frozen {m} (regression; CV-R2, sd, CV-RMSE)'] + [''] * 7 + [v[2]] + [''] * 8)
    open(os.path.join(RES, 'phase5e_results.txt'), 'w').write('\n'.join(lines) + '\n')

def spearman(a, b):
    a = np.asarray(a, float); ok = np.isfinite(a); ra = np.argsort(np.argsort(a[ok])); rb = np.argsort(np.argsort(np.asarray(b)[ok]))
    return np.corrcoef(ra, rb)[0, 1]

if __name__ == '__main__': main()
