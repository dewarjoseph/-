#!/usr/bin/env python3
"""Phase V-E figures (deliverables/figures/phase5e_*.png|pdf) from the result files of audit/phase5e_run.py / _analyze.py.
  1 error_vs_dimension   edge error E_W - E_0 vs retained dimension D, level 4, 264 rule classes: median and interquartile band
  2 uncaptured_vs_dimension   uncaptured boundary weight 1 - c vs D (the quantity that bounds the error, Theorem E4)
  3 error_vs_level       relative edge error at fixed family parameter (fixed D) vs level, 8 sweep systems: mean and range
  4 fr30_scaling         FR30 pinned edge E_m vs m with the frozen level-7 predictions and the level-7 result
  5 closure              universal T3-surface subspace: captured weight vs d per level and out-of-level transfer
Colours: reference categorical palette (validated: adjacent CVD dE >= 9.1, normal-vision >= 19.6); every series also has its own
marker and a legend entry, so identity is never colour-alone; the numbers are in audit/results/phase5e_results.csv.
"""
import os, sys, json, glob
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); RES = os.path.join(HERE, 'results')
OUT = os.path.join(os.path.dirname(HERE), 'deliverables', 'figures'); os.makedirs(OUT, exist_ok=True)
import numpy as np
import matplotlib; matplotlib.use('Agg')
import matplotlib.pyplot as plt

SURF = '#fcfcfb'; INK = '#0b0b0b'; INK2 = '#52514e'; GRID = '#e4e3df'
SLOTS = ['#2a78d6', '#eb6834', '#1baf7a', '#eda100', '#e87ba4', '#008300', '#6250d6', '#e34948']
FAM = [('child', 'child modes'), ('face', 'face modes'), ('iface2', 'two-sided seam modes'), ('fec', 'face+hinge+corner'),
       ('patch2', 'depth-2 patches'), ('patch3', 'depth-3 patches'), ('adaptive', 'adaptive tiles (trained)'), ('oracle', 'oracle tiles (uses target)')]
COL = {f: SLOTS[i] for i, (f, _) in enumerate(FAM)}; MARK = dict(zip([f for f, _ in FAM], 'osD^vPXx'))
plt.rcParams.update({'font.size': 9, 'axes.edgecolor': INK2, 'axes.labelcolor': INK, 'xtick.color': INK2, 'ytick.color': INK2,
                     'axes.facecolor': SURF, 'figure.facecolor': SURF, 'axes.grid': True, 'grid.color': GRID, 'grid.linewidth': 0.6,
                     'axes.spines.top': False, 'axes.spines.right': False, 'legend.frameon': False, 'lines.linewidth': 2})

def jl(pattern):
    out = {}
    for fn in sorted(glob.glob(os.path.join(RES, pattern))):
        for l in open(fn):
            try: r = json.loads(l); out[f"{r['name']}|{r.get('kind', '')}"] = r
            except json.JSONDecodeError: pass
    return out

def save(fig, name):
    for ext in ('png', 'pdf'): fig.savefig(os.path.join(OUT, f'phase5e_{name}.{ext}'), dpi=170, bbox_inches='tight')
    plt.close(fig)

def level4_curves():
    L4 = jl('phase5e_L4_shard*.jsonl'); AD = jl('phase5e_adaptive_L4_shard*.jsonl')
    for nm, r in AD.items():
        if nm in L4: L4[nm]['bases'].update(r['bases'])
    rules = [r for r in L4.values() if r['kind'] == 'rule']
    cur = {}
    for r in rules:
        for k, b in r['bases'].items():
            fam = k.split(':')[0]
            if b.get('E_W') is None or b['E_W'] != b['E_W']: continue
            cur.setdefault(fam, {}).setdefault(k, []).append((b['D'], b['E_W'] - r['E0'], 1 - b.get('capture', np.nan)))
    return rules, cur, L4

def fig_dimension():
    rules, cur, L4 = level4_curves()
    if not rules: return
    res = json.load(open(os.path.join(RES, 'phase5e_results.json'))) if os.path.exists(os.path.join(RES, 'phase5e_results.json')) else None
    for which, ylabel, name in ((1, 'edge error  $E_W - E_0$  (parameter-free)', 'error_vs_dimension'), (2, 'uncaptured boundary weight  $1 - c$', 'uncaptured_vs_dimension')):
        fig, axs = plt.subplots(1, 2 if (which == 1 and res) else 1, figsize=(11.5 if (which == 1 and res) else 6.6, 4.3), squeeze=False); ax = axs[0, 0]
        for fam, lab in FAM:
            if fam not in cur: continue
            pts = []
            for k, v in cur[fam].items():
                a = np.array(v); pts.append((np.median(a[:, 0]), np.percentile(a[:, which], 25), np.median(a[:, which]), np.percentile(a[:, which], 75)))
            pts = np.array(sorted(pts))
            ax.fill_between(pts[:, 0], pts[:, 1], pts[:, 3], color=COL[fam], alpha=0.15, lw=0)
            ax.plot(pts[:, 0], pts[:, 2], color=COL[fam], marker=MARK[fam], ms=6, label=lab, mec=SURF, mew=1)
        sel = [r for r in rules if r['bases'].get('interface:None')]
        if sel:
            a = np.array([(r['bases']['interface:None']['D'], r['bases']['interface:None']['E_W'] - r['E0'], 1 - r['bases']['interface:None']['capture']) for r in sel])
            med = np.median(a[:, which]); ax.errorbar([np.median(a[:, 0])], [med], yerr=[[med - np.percentile(a[:, which], 25)], [np.percentile(a[:, which], 75) - med]],
                                                     fmt='*', ms=11, color=SLOTS[7], label='all interface tiles (not a compression)', mec=SURF)
        ax.axvline(459, color=INK2, ls='--', lw=1)
        ax.set_xscale('log'); ax.set_yscale('log'); ax.set_xlabel('retained complex dimension $D$  (dim $S$ = 4592)'); ax.set_ylabel(ylabel)
        ax.text(470, ax.get_ylim()[0] * 1.15, '10 % of dim S', color=INK2, fontsize=8)
        ax.set_title(f'Level 4, {len(rules)} rule classes: median and interquartile band', color=INK, fontsize=10, loc='left')
        ax.legend(fontsize=7.5, loc='upper center', bbox_to_anchor=(0.5, -0.16), ncol=3)
        if which == 1 and res:
            ax2 = axs[0, 1]
            for fam, lab in FAM:
                pts = sorted((t['D'], t['cal_rmse']) for k, t in res['table'].items() if t['family'] == fam)
                if pts: ax2.plot([p[0] for p in pts], [p[1] for p in pts], color=COL[fam], marker=MARK[fam], ms=6, label=lab, mec=SURF, mew=1)
            t = res['table'].get('interface:None')
            if t: ax2.plot([t['D']], [t['cal_rmse']], marker='*', ms=11, color=SLOTS[7], ls='none', label='all interface tiles', mec=SURF)
            ax2.axhline(0.05, color=INK2, ls=':', lw=1); ax2.text(20, 0.053, 'criterion C2: 0.05', color=INK2, fontsize=8)
            ax2.axvline(459, color=INK2, ls='--', lw=1)
            ax2.set_xscale('log'); ax2.set_yscale('log'); ax2.set_xlabel('retained complex dimension $D$')
            ax2.set_ylabel('calibrated out-of-fold RMSE (offset from training folds)')
            ax2.set_title('the criterion quantity (C2)', color=INK, fontsize=10, loc='left')
        save(fig, name)

def fig_level():
    LV = [json.loads(l) for fn in sorted(glob.glob(os.path.join(RES, 'phase5e_levels_*.jsonl'))) for l in open(fn)]
    if not LV: return
    prim = {'child': 16, 'face': 4, 'iface2': 8, 'fec': 2, 'patch2': 4, 'patch3': 1}
    fig, ax = plt.subplots(figsize=(6.0, 4.0))
    for fam, lab in FAM:
        if fam not in prim: continue
        k = f'{fam}:{prim[fam]}'; byL = {}
        for r in LV:
            b = r['bases'].get(k)
            if b and b.get('E_W') == b.get('E_W') and b.get('E_W') is not None: byL.setdefault(r['level'], []).append((b['E_W'] - r['E0']) / r['E0'])
        if not byL: continue
        Ls = sorted(byL); m = [np.mean(byL[L]) for L in Ls]; lo = [np.min(byL[L]) for L in Ls]; hi = [np.max(byL[L]) for L in Ls]
        ax.fill_between(Ls, lo, hi, color=COL[fam], alpha=0.12, lw=0)
        ax.plot(Ls, m, color=COL[fam], marker=MARK[fam], ms=6, label=f'{lab} ({k})', mec=SURF, mew=1)
    ax.set_xlabel('substitution level $L$ (fixed family parameter: fixed $D$)'); ax.set_ylabel('relative edge error  $(E_W - E_0)/E_0$')
    ax.set_xticks([2, 3, 4, 5]); ax.set_yscale('log'); ax.legend(fontsize=7.5)
    ax.set_title('Level sweep: 8 systems, mean and range', color=INK, fontsize=10, loc='left'); save(fig, 'error_vs_level')

def fig_scaling():
    P = json.load(open(os.path.join(RES, 'phase5e_level7_prediction.json'))); E = {int(k): v for k, v in P['data_E_m'].items()}
    ev = os.path.join(RES, 'phase5e_level7_evaluation.json'); E7 = json.load(open(ev))['E7'] if os.path.exists(ev) else None
    fig, axs = plt.subplots(1, 2, figsize=(9.6, 3.8))
    ax = axs[0]; ms = sorted(E); ax.plot(ms, [E[m] for m in ms], color=SLOTS[0], marker='o', ms=6, label='$E_m$ (stored, levels 1-6)', mec=SURF)
    if E7: ax.plot([7], [E7], marker='*', ms=13, color=SLOTS[7], ls='none', label=f'level 7 (this phase): {E7:.7f}', mec=SURF)
    ax.axhspan(8.7605, 8.7655, color=SLOTS[3], alpha=0.12, lw=0, label='frozen level-7 envelope')
    ax.set_xlabel('level $m$'); ax.set_ylabel('pinned edge $E_m$'); ax.legend(fontsize=7.5); ax.set_title('FR30 pinned edge', color=INK, fontsize=10, loc='left')
    ax = axs[1]; d = {m: E[m - 1] - E[m] for m in range(2, 7)}
    if E7: d[7] = E[6] - E7
    mm = sorted(d); ax.plot(mm, [d[m] for m in mm], color=SLOTS[0], marker='o', ms=6, mec=SURF, label='decrement $d_m = E_{m-1} - E_m$')
    ref = d[6]; ax.plot([6, 7, 8], [ref, ref / 4, ref / 16], color=INK2, ls='--', lw=1, label='ratio 1/4 ($L^{-2}$)')
    ax.set_yscale('log'); ax.set_xlabel('level $m$'); ax.set_ylabel('decrement'); ax.legend(fontsize=7.5)
    for m in mm[1:]: ax.annotate(f"{d[m]/d[m-1]:.3f}", (m, d[m]), textcoords='offset points', xytext=(4, 6), fontsize=7.5, color=INK2)
    ax.set_title('decrements and ratios $r_m$', color=INK, fontsize=10, loc='left'); save(fig, 'fr30_scaling')

def fig_closure():
    p = os.path.join(RES, 'phase5e_closure.json')
    if not os.path.exists(p): return
    C = json.load(open(p)); fig, ax = plt.subplots(figsize=(6.0, 4.0))
    ds = [2, 8, 16, 32, 57, 114, 287, 400, 500]
    for i, (L, v) in enumerate(sorted(C['per_level'].items(), key=lambda t: int(t[0]))):
        ax.plot(ds, [1 - v['tau_d'][str(dd)] for dd in ds], color=SLOTS[i], marker='osD^'[i], ms=6, mec=SURF, label=f"level {L}: best subspace for its own contexts ({v['copies']} copies)")
    for i, (k, row) in enumerate(C['transfer'].items()):
        dd = [int(x) for x in row]; ax.plot(dd, [row[str(x)] for x in dd], color=SLOTS[4 + i % 4], ls='--', marker='vPXx'[i % 4], ms=6, mec=SURF, label=k.replace('_', ' '))
    ax.axvline(57, color=INK2, ls=':', lw=1); ax.axhline(0.99, color=INK2, ls=':', lw=1)
    ax.set_xscale('log'); ax.set_xlabel('dimension $d$ of the universal $T_3$-surface subspace (of 574)'); ax.set_ylabel('captured weight')
    ax.legend(fontsize=7); ax.set_title('H2 closure test (FR30)', color=INK, fontsize=10, loc='left'); save(fig, 'closure')

if __name__ == '__main__':
    fig_dimension(); fig_level(); fig_scaling(); fig_closure(); print('figures written to', OUT)
