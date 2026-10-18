"""MIG-1 name screen. Read-only; standard library only.

Usage: python3 -I namescreen.py <worktree> <gate-public.txt> <moved-names.json> <out.txt>

1. A namespace-aware index of every declaration of every `TCSlib` module (comment-stripped;
   `namespace`/`section`/`end` tracked; `_root_.` honoured; public and private).
2. For every proposed public name of the gate (the unit's public declarations, `MIG1Gate.*`
   excluded) with its home module: an exact full-name clash is any declaration with the same
   full name in the home module (other than the private declaration that the in-place rename
   makes public), in the home's import closure, or in any module that imports the home
   (Lean rejects a later private declaration whose name is already public). The H2 draft's
   proposed names (`audits/evidence/h2/StepBlockDraft.lean.txt`) are screened as a further
   module, since H2-M and MIG-1 land in the same window.
3. Short-name exposure: occurrences, as an identifier (bare or `FinTM.`-qualified), of every
   proposed short name in the colleague-owned files that open `Turing.FinTM` or sit in it
   (`TimeHierarchy/Separation.lean`, `CircuitComplexity/*`), and in every Catalog importer that
   does not import Primitives (it newly sees Primitives and TimeConstructible).
4. The same exact-clash test for the proposed private names of moved declarations
   (moved-names.json: {new name: home module}), against the home and its closure.
Mathlib and the other packages are screened by text: a proposed full name is reported if its
last component occurs in a package source file inside a `namespace Turing` block.
"""
import glob
import json
import os
import re
import sys

KW = r'(theorem|lemma|def|abbrev|structure|inductive|instance|class|opaque|axiom)'
DPAT = re.compile(r'^(?:@\[[^\]]*\]\s*)?((?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*'
                  + KW + r'\s+([^\s:({\[]+)')


def strip(src):
    out, i, depth, n = [], 0, 0, len(src)
    while i < n:
        if src.startswith('/-', i):
            depth += 1; i += 2; continue
        if depth and src.startswith('-/', i):
            depth -= 1; i += 2; continue
        if depth:
            out.append('\n' if src[i] == '\n' else ' '); i += 1; continue
        if src.startswith('--', i):
            j = src.find('\n', i); j = n if j < 0 else j
            out.append(' ' * (j - i)); i = j; continue
        out.append(src[i]); i += 1
    return ''.join(out)


def index_file(path, mod):
    res = []
    stack = []
    for ln, l in enumerate(strip(open(path, encoding='utf-8').read()).split('\n'), 1):
        m = re.match(r'^namespace\s+(\S+)', l)
        if m:
            stack.append(('ns', m.group(1))); continue
        m = re.match(r'^(?:noncomputable\s+)?section\b\s*(\S*)', l)
        if m:
            stack.append(('sec', m.group(1))); continue
        m = re.match(r'^end\b\s*(\S*)', l)
        if m:
            if stack:
                stack.pop()
            continue
        m = DPAT.match(l)
        if m:
            name = m.group(3)
            if m.group(2) == 'instance' and (name.startswith('[') or name.startswith(':')):
                continue
            ns = '.'.join(n for k, n in stack if k == 'ns')
            full = name[len('_root_.'):] if name.startswith('_root_.') else (
                ns + '.' + name if ns else name)
            res.append(dict(mod=mod, line=ln, full=full, short=full.split('.')[-1],
                            private='private' in (m.group(1) or ''), kind=m.group(2)))
    return res


def main():
    wt, gate_list, moved_json, out = sys.argv[1:5]
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    from importgraph import graph, clos
    G = graph(wt)
    idx = []
    for f in sorted(glob.glob(os.path.join(wt, 'TCSlib', '**', '*.lean'), recursive=True)):
        mod = os.path.relpath(f, wt)[:-5].replace(os.sep, '.')
        idx.extend(index_file(f, mod))
    h2 = index_file(os.path.join(wt, 'audits/evidence/h2/StepBlockDraft.lean.txt'), 'H2-draft')
    for d in h2:
        if d['full'].startswith('Turing.Draft.StepBlock.'):
            short = d['full'][len('Turing.Draft.StepBlock.'):]
            generic = {'abs_workTapePos_runFrom_sub_le', 'inputPos_runFrom_of_inputTape_eq_zero',
                       'visitedByTapeHead_add_subset', 'visitedByTapeHead_step_subset'}
            keep = {'workReadsK', 'tableBitsK'}
            if short in generic:
                d['full'] = 'Turing.MultiTapeTM.' + short
            elif short in keep:
                d['full'] = 'Turing.' + short
            else:
                d['full'] = 'Turing.StepBlock.' + short
    lines = []
    w = lines.append
    w(f'index: {len(idx)} declarations in {len(set(d["mod"] for d in idx))} TCSlib modules; '
      f'H2 draft: {len(h2)} declarations')
    homes = {
        'Simulation': 'TCSlib.Complexity.TuringMachine.Simulation',
        'Composition': 'TCSlib.Complexity.TuringMachine.Composition',
        'Wrappers': 'TCSlib.Complexity.TuringMachine.Build.Wrappers',
        'Encoding': 'TCSlib.Complexity.TuringMachine.Encoding',
        'TimeConstructible': 'TCSlib.Complexity.ClassP.TimeConstructible',
        'Loop': 'TCSlib.Complexity.TuringMachine.Build.Loop',
        'Primitives': 'TCSlib.Complexity.TuringMachine.Build.Primitives',
        'Catalog': 'TCSlib.Complexity.TuringMachine.Build.Catalog',
    }
    # gate-public.txt: "line kind visibility fullname"; homes by unit line ranges
    part_starts = json.load(open(os.path.join(os.path.dirname(gate_list), 'part-lines.json')))
    prop = []
    for l in open(gate_list, encoding='utf-8'):
        ln, kind, vis, full = l.split()
        if '.MIG1Gate.' in full:
            continue
        ln = int(ln)
        home = max((s, h) for h, s in part_starts.items() if s <= ln)[1]
        prop.append((full, homes[home]))
    # in-place renames: the private source that becomes the public name
    renamed = json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                          'inplace.json')))
    mods = [m for m in G if m != 'TCSlib']
    imp_by = {m: set(x for x in mods if m in clos(G, x)) for m in homes.values()}
    clash_total = 0
    w('')
    w('## 1. Exact full-name clashes of the proposed public names')
    for full, home in prop:
        scope = {home} | clos(G, home) | imp_by[home]
        hits = []
        for d in idx:
            if d['full'] != full or d['mod'] not in scope:
                continue
            src = renamed.get(full)
            if src and d['mod'] == home and d['private'] and src == d['full']:
                continue
            hits.append(d)
        for d in h2:
            if d['full'] == full and full != 'Turing.MultiTapeTM.abs_workTapePos_runFrom_sub_le':
                hits.append(d)
        if hits:
            clash_total += len(hits)
            w(f'CLASH {full} (home {home.split(".")[-1]}): ' + '; '.join(
                f"{d['mod']}:{d['line']} {'private' if d['private'] else 'public'} {d['kind']}"
                for d in hits))
    w(f'proposed public names: {len(prop)}; clashes: {clash_total}')
    w('in-place renames (the private source made public, not a clash): ' +
      ', '.join(f'{k} <- private {v}' for k, v in renamed.items()))
    w('shared with H2 by design: Turing.MultiTapeTM.abs_workTapePos_runFrom_sub_le')
    # 2. same short names elsewhere (information)
    w('')
    w('## 2. The same last component elsewhere in TCSlib (information; other namespaces)')
    shorts = {}
    for full, home in prop:
        shorts.setdefault(full.split('.')[-1], []).append(full)
    for s, fulls in sorted(shorts.items()):
        others = sorted({d['full'] for d in idx if d['short'] == s and d['full'] not in fulls
                         and d['full'] not in renamed.values()})
        if others:
            w(f'{s}: ' + ', '.join(others[:8]) + (' …' if len(others) > 8 else ''))
    # 3. exposure in colleague files and the eight new Catalog importers
    w('')
    w('## 3. Identifier occurrences of the proposed short names (bare or `FinTM.`-qualified)')
    files = [os.path.join(wt, 'TCSlib/Complexity/TimeHierarchy/Separation.lean')] + sorted(
        glob.glob(os.path.join(wt, 'TCSlib/Complexity/CircuitComplexity/**/*.lean'), recursive=True))
    newimp = sorted(m for m in imp_by[homes['Catalog']] if homes['Primitives'] not in clos(G, m))
    w('Catalog importers that newly see Primitives and TimeConstructible: ' +
      ', '.join(m.split('.')[-1] for m in newimp))
    for m in newimp:
        files.append(os.path.join(wt, *m.split('.')) + '.lean')
    occ = 0
    for f in files:
        s = strip(open(f, encoding='utf-8').read())
        for short in sorted(shorts):
            for pref in ['', 'FinTM.']:
                pat = re.compile(r'(?<![\w.\'])' + re.escape(pref + short) + r'(?![\w\'])')
                n = len(pat.findall(s))
                if n:
                    occ += n
                    w(f'{os.path.relpath(f, wt)}: {pref + short} x{n}')
    w(f'files screened: {len(files)}; occurrences: {occ}')
    # 4. moved private names
    w('')
    w('## 4. Proposed private names of moved declarations')
    moved = json.load(open(moved_json, encoding='utf-8'))
    mclash = 0
    for name, home in moved.items():
        scope = {homes[home]} | clos(G, homes[home]) | imp_by[homes[home]]
        hits = [d for d in idx if d['full'] == name and d['mod'] in scope
                and (not d['private'] or d['mod'] == homes[home])]
        hits += [d for d in idx if d['full'] == name and d['private'] and d['mod'] in scope
                 and d['mod'] != homes[home] and d['mod'] != homes['Catalog']]
        if hits:
            mclash += len(hits)
            w(f'CLASH {name} (home {home}): ' + '; '.join(
                f"{d['mod']}:{d['line']} {'private' if d['private'] else 'public'}" for d in hits))
    w(f'moved names: {len(moved)}; clashes: {mclash}')
    # 5. package sources
    w('')
    w('## 5. Package sources (text): proposed last components inside `namespace Turing` blocks')
    pk = 0
    for f in glob.glob(os.path.join(wt, '.lake', 'packages', '*', '**', '*.lean'), recursive=True):
        txt = open(f, encoding='utf-8', errors='replace').read()
        if 'namespace Turing' not in txt:
            continue
        for short in shorts:
            if re.search(r'(?<![\w.])' + re.escape(short) + r'(?![\w\'])', txt):
                pk += 1
                w(f'{os.path.relpath(f, wt)}: {short}')
    w(f'package hits: {pk}')
    open(out, 'w', encoding='utf-8').write('\n'.join(lines) + '\n')
    print('\n'.join(lines[:3]))
    print(f'clashes {clash_total}, exposure occurrences {occ}, moved clashes {mclash}, '
          f'package hits {pk}')


if __name__ == '__main__':
    main()
