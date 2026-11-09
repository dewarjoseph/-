#!/usr/bin/env python3
"""Build the PDFs of the Zenodo package from the repository's Markdown (markdown-it -> LaTeX -> tectonic/XeLaTeX, DejaVu Sans).
Usage: python -u -I zenodo/build_pdfs.py   (needs markdown-it-py and tectonic on PATH; writes zenodo/<NAME>.pdf)"""
import os, re, subprocess, sys, tempfile
from markdown_it import MarkdownIt
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__))); OUT = os.path.join(ROOT, 'zenodo')
DOCS = ['deliverables/PHASE12_DECISION_MEMO.md', 'deliverables/PHASE12_STRONGEST_THEOREM.md', 'deliverables/PHASE11_STRONGEST_THEOREM.md']
PRE = r"""\documentclass[10pt]{article}
\usepackage[a4paper,margin=2cm]{geometry}
\usepackage{fontspec,newunicodechar,longtable,array,booktabs,hyperref,amsmath,amssymb,enumitem}
\setmainfont{DejaVu Sans}\setmonofont{DejaVu Sans Mono}[Scale=0.9]
\newunicodechar{𝓔}{\ensuremath{\mathcal{E}}}\newunicodechar{𝓕}{\ensuremath{\mathcal{F}}}
\setlength{\parindent}{0pt}\setlength{\parskip}{4pt}\setlist{nosep,leftmargin=1.4em}
\hypersetup{colorlinks=true,linkcolor=black,urlcolor=blue}
\begin{document}
"""
ESC = {'\\': r'\textbackslash{}', '{': r'\{', '}': r'\}', '$': r'\$', '&': r'\&', '#': r'\#', '%': r'\%', '_': r'\_',
       '^': r'\textasciicircum{}', '~': r'\textasciitilde{}'}
def esc(s): return ''.join(ESC.get(c, c) for c in s)

def inline(tok):
    out = []
    for t in tok.children or []:
        if t.type == 'text': out.append(esc(t.content))
        elif t.type == 'code_inline': out.append(r'\texttt{' + esc(t.content) + '}')
        elif t.type == 'strong_open': out.append(r'\textbf{')
        elif t.type == 'em_open': out.append(r'\emph{')
        elif t.type in ('strong_close', 'em_close', 'link_close'): out.append('}')
        elif t.type == 'link_open': out.append(r'\href{' + esc(t.attrs.get('href', '')).replace(r'\#', r'\#') + '}{')
        elif t.type == 'softbreak': out.append(' ')
        elif t.type == 'hardbreak': out.append(r'\\' + '\n')
        elif t.type == 'html_inline': pass
        else: out.append(esc(t.content or ''))
    return ''.join(out)

def convert(md):
    toks = MarkdownIt('commonmark').enable('table').parse(md); out = []; i = 0; cells = []; row = []; ncol = 0
    while i < len(toks):
        t = toks[i]; ty = t.type
        if ty == 'heading_open':
            lev = int(t.tag[1]); cmd = {1: 'section*', 2: 'subsection*', 3: 'subsubsection*'}.get(lev, 'paragraph*')
            out.append('\\%s{%s}\n' % (cmd, inline(toks[i + 1]))); i += 3; continue
        if ty == 'paragraph_open':
            out.append(inline(toks[i + 1]) + ('\n\n' if not t.hidden else '\n')); i += 3; continue
        if ty == 'bullet_list_open': out.append('\\begin{itemize}\n')
        elif ty == 'bullet_list_close': out.append('\\end{itemize}\n')
        elif ty == 'ordered_list_open': out.append('\\begin{enumerate}\n')
        elif ty == 'ordered_list_close': out.append('\\end{enumerate}\n')
        elif ty == 'list_item_open': out.append('\\item ')
        elif ty == 'blockquote_open': out.append('\\begin{quote}\n')
        elif ty == 'blockquote_close': out.append('\\end{quote}\n')
        elif ty == 'hr': out.append('\\par\\noindent\\rule{\\linewidth}{0.4pt}\n')
        elif ty in ('fence', 'code_block'): out.append('\\begin{verbatim}\n' + t.content + '\\end{verbatim}\n')
        elif ty == 'table_open':
            j = i; ncol = 0
            while toks[j].type != 'tr_close':
                ncol += toks[j].type in ('th_open', 'td_open'); j += 1
            w = 0.98 / ncol
            out.append('{\\small\\begin{longtable}{' + ''.join('>{\\raggedright\\arraybackslash}p{%.3f\\linewidth}' % (w - 0.012) for _ in range(ncol)) + '}\\toprule\n')
        elif ty == 'table_close': out.append('\\bottomrule\\end{longtable}}\n')
        elif ty == 'thead_close': out.append('\\midrule\\endhead\n')
        elif ty == 'tr_open': row = []
        elif ty == 'tr_close': out.append(' & '.join(row) + ' \\\\\n')
        elif ty in ('th_open', 'td_open'):
            c = inline(toks[i + 1]); row.append('\\textbf{' + c + '}' if ty == 'th_open' else c); i += 3; continue
        i += 1
    return ''.join(out)

def build(rel):
    md = open(os.path.join(ROOT, rel), encoding='utf8').read(); name = os.path.splitext(os.path.basename(rel))[0]
    tex = PRE + '{\\footnotesize Source: \\texttt{' + esc(rel) + '} (repository dewarjoseph/-)}\n\n' + convert(md) + '\\end{document}\n'
    with tempfile.TemporaryDirectory() as d:
        p = os.path.join(d, name + '.tex'); open(p, 'w', encoding='utf8').write(tex)
        subprocess.run(['tectonic', '--keep-logs', '--outdir', d, p], check=True)
        os.replace(os.path.join(d, name + '.pdf'), os.path.join(OUT, name + '.pdf'))
    print('wrote', os.path.join('zenodo', name + '.pdf'))

if __name__ == '__main__':
    for rel in (sys.argv[1:] or DOCS): build(rel)
