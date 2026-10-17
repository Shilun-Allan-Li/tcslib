"""MIG-1 deletion plan: classify every declaration of the `Build/Catalog.lean` region.

Usage: python3 -I region_r2.py <worktree> <outdir> <fates json>

Round 2 (MIG-1 statement gate): `region.py` of round 1 with two changes only, both asserted
edits: the fate manifest is an argument (round 2: `fates_r2.json`), and its `overrides`
section assigns a fate to a named declaration before the generic classification (round 2:
`f2_loopHost_prepare`, finding 1). Output and counts are otherwise computed as in round 1.

Read-only on the worktree; standard library only. Writes <outdir>/deletion-plan.json and
<outdir>/deletion-plan.tsv and prints the counts.

Method.
* Declarations: `decls.scan` (comment-aware scanner) of Catalog; the region is the
  `namespace Turing.FinTM` block between the first `f2_` docstring and its `end`.
* Code of a declaration: its lines from the keyword to the line before the next top-level
  command, comments and docstrings removed, trailing blanks dropped, each line right-stripped.
  "With docstrings" line counts add the immediately preceding docstring block.
* A copy's source: the declaration of the same name, after removing the prefix (`f2_`, or
  `catalog_redirect` -> `redirect`), in one of the seven home files.
* Code-identical: the copy's code with every region-local prefixed identifier renamed to its
  unprefixed form equals the source's code. Statement-identical: the same on the statement
  (the code up to the first top-level `:=` or `where`).
* Dependencies: identifier occurrences in code; closures run over region declarations.
* Fates follow the MIG-1 statement-gate plan (the pack, section "Deletion plan"): see FATE below.
"""
import json
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from decls import scan  # noqa: E402

HOMES = {
    'Composition': 'TCSlib/Complexity/TuringMachine/Composition.lean',
    'Primitives': 'TCSlib/Complexity/TuringMachine/Build/Primitives.lean',
    'Loop': 'TCSlib/Complexity/TuringMachine/Build/Loop.lean',
    'Wrappers': 'TCSlib/Complexity/TuringMachine/Build/Wrappers.lean',
    'TimeConstructible': 'TCSlib/Complexity/ClassP/TimeConstructible.lean',
    'Encoding': 'TCSlib/Complexity/TuringMachine/Encoding.lean',
    'Simulation': 'TCSlib/Complexity/TuringMachine/Simulation.lean',
}
CATALOG = 'TCSlib/Complexity/TuringMachine/Build/Catalog.lean'
IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_'!?]*(?:\.[A-Za-z_][A-Za-z0-9_'!?]*)*")


def strip_comments(lines):
    out, depth = [], 0
    for s in lines:
        o, j = '', 0
        while j < len(s):
            if depth > 0:
                if s.startswith('/-', j):
                    depth += 1; j += 2; continue
                if s.startswith('-/', j):
                    depth -= 1; j += 2; continue
                j += 1; continue
            if s.startswith('/-', j):
                depth += 1; j += 2; continue
            if s.startswith('--', j):
                break
            o += s[j]; j += 1
        out.append(o.rstrip())
    return out


def doc_start(lines, line):
    s = line - 1
    j = s - 1
    while j >= 0 and lines[j].startswith('@['):
        j -= 1
    if j >= 0 and lines[j].rstrip().endswith('-/'):
        k = j
        while k >= 0 and not lines[k].lstrip().startswith('/--') and not lines[k].lstrip().startswith('/-'):
            k -= 1
        if k >= 0 and lines[k].lstrip().startswith('/--'):
            return k + 1
    return line


def code_of(code, d):
    c = code[d['line'] - 1:d['end']]
    while c and c[-1] == '':
        c.pop()
    return [l for l in c]


def statement(c):
    """Code up to the first top-level `:=` / ` where` (joined, whitespace-normalized)."""
    text = '\n'.join(c)
    depth = 0
    for i, ch in enumerate(text):
        if ch in '([{⟨':
            depth += 1
        elif ch in ')]}⟩':
            depth -= 1
        elif depth == 0 and text.startswith(':=', i):
            return ' '.join(text[:i].split())
        elif depth == 0 and text.startswith(' where', i) and (i + 6 == len(text) or text[i + 6] in ' \n'):
            return ' '.join(text[:i].split())
    return ' '.join(text.split())


def unprefix(name):
    if name.startswith('f2_'):
        return name[3:]
    if name.startswith('catalog_redirect'):
        return 'redirect' + name[len('catalog_redirect'):]
    return None


def rename(lines, mapping):
    def sub(m):
        tok = m.group(0)
        parts = tok.split('.')
        return '.'.join(mapping.get(p, p) for p in parts)
    return [IDENT.sub(sub, l) for l in lines]


def main():
    wt, out, fates_path = sys.argv[1], sys.argv[2], sys.argv[3]
    os.makedirs(out, exist_ok=True)
    cat_lines = open(os.path.join(wt, CATALOG), encoding='utf-8').read().split('\n')
    cat_code = strip_comments(cat_lines)
    D, _ = scan(os.path.join(wt, CATALOG))
    first = min(d['line'] for d in D if d['name'].startswith('f2_'))
    start = max(i + 1 for i, l in enumerate(cat_lines[:first]) if l.startswith('namespace Turing.FinTM'))
    end = min(i + 1 for i, l in enumerate(cat_lines) if i + 1 > first and l.startswith('end Turing.FinTM'))
    region = [d for d in D if start < d['line'] < end]
    homes = {}
    for k, rel in HOMES.items():
        hl = open(os.path.join(wt, rel), encoding='utf-8').read().split('\n')
        hd, _ = scan(os.path.join(wt, rel))
        homes[k] = (hl, strip_comments(hl), hd)
    index = {}
    for k in HOMES:
        for d in homes[k][2]:
            index.setdefault(d['name'], (k, d))
    names = {d['name'] for d in region}
    rmap = {n: unprefix(n) for n in names if unprefix(n)}
    rows = []
    code = {}
    for d in region:
        c = code_of(cat_code, d)
        code[d['name']] = c
        ds = doc_start(cat_lines, d['line'])
        r = dict(name=d['name'], line=d['line'], end=d['end'], kind=d['kind'],
                 private=d['private'], lines=d['end'] - d['line'] + 1,
                 lines_doc=d['end'] - ds + 1)
        base = unprefix(d['name'])
        if d['name'].startswith('f2_'):
            r['family'] = 'f2'
        elif d['name'].startswith('a2_'):
            r['family'] = 'a2'
        elif d['name'].startswith('catalog_redirect'):
            r['family'] = 'catalog_redirect'
        elif not d['private']:
            r['family'] = 'public'
        else:
            r['family'] = 'other-private'
        r['source'] = None
        if base and base in index:
            k, sd = index[base]
            hc = code_of(homes[k][1], sd)
            mine = rename(c, rmap)
            r['source'] = f"{k}:{sd['line']}:{base}"
            r['code_identical'] = [l.strip() for l in mine if l.strip()] == [l.strip() for l in hc if l.strip()]
            r['statement_identical'] = statement(mine) == statement(hc)
        rows.append(r)
    # dependencies inside the region
    uses = {}
    for r in rows:
        toks = set()
        for l in code[r['name']]:
            for t in IDENT.findall(l):
                toks.update(t.split('.'))
        uses[r['name']] = sorted(t for t in toks if t in names and t != r['name'])
    # instances are used implicitly: attach each instance to the inductive it is about
    for r in rows:
        if r['kind'] == 'instance':
            for t in uses[r['name']]:
                if t in names:
                    uses.setdefault(t, [])
                    if r['name'] not in uses[t]:
                        uses[t] = sorted(uses[t] + [r['name']])
    for r in rows:
        r['uses'] = uses[r['name']]
    by = {r['name']: r for r in rows}

    def leaf(n):
        r = by[n]
        return r['source'] is not None  # a copy: the home original is used instead

    def closure(roots, through_copies=False):
        seen, todo = set(), list(roots)
        while todo:
            n = todo.pop()
            if n in seen:
                continue
            seen.add(n)
            if leaf(n) and n not in roots and not through_copies:
                continue
            todo.extend(uses[n])
        return seen

    plan = json.load(open(fates_path, encoding='utf-8'))
    overrides = plan.get('overrides', {})
    families = plan['moved_families']
    absorbed = plan['absorbed']
    duplicates = plan['duplicates']
    replaces = plan['replaces']
    publics = plan['publics']
    reach = {}
    for fam, spec in families.items():
        for n in closure(spec['roots']):
            reach.setdefault(n, []).append(fam)
    # reach from every public row through everything (to find dead declarations)
    pub_names = [r['name'] for r in rows if r['family'] == 'public']
    live_all = closure(pub_names, through_copies=True)
    sform = set(closure(plan['sform_roots'], through_copies=True))
    others = set()
    for p in pub_names:
        if p in plan['sform_roots']:
            continue
        others |= closure([p], through_copies=True)
    for r in rows:
        n = r['name']
        fams = reach.get(n, [])
        if n in overrides:
            r['fate'] = overrides[n]['fate']
            r['detail'] = overrides[n]['detail']
        elif r['family'] == 'public':
            r['fate'] = publics[n]['fate']
            r['detail'] = publics[n]['detail']
        elif n in absorbed:
            r['fate'] = 'absorbed into a gated public statement'
            r['detail'] = absorbed[n]
        elif n in replaces:
            r['fate'] = 'move: replaces the original (extended statement)'
            r['detail'] = replaces[n]
        elif n in duplicates:
            r['fate'] = 'delete: duplicates an existing public declaration'
            r['detail'] = duplicates[n]
        elif r['source'] is not None and r.get('code_identical'):
            r['fate'] = 'delete: copy, original used'
            r['detail'] = r['source']
        elif r['source'] is not None and r.get('statement_identical'):
            r['fate'] = 'delete: statement-identical copy (proof differs), original used'
            r['detail'] = r['source']
        elif r['source'] is not None:
            r['fate'] = 'delete: modified copy, citations re-targeted at the original'
            r['detail'] = r['source']
        elif fams:
            fam = fams[0]
            r['fate'] = 'move'
            r['detail'] = f"{families[fam]['home']} ({fam})"
        elif n not in live_all:
            r['fate'] = 'delete: dead (reached from no public declaration)'
            r['detail'] = ''
        elif n in sform and n not in others:
            r['fate'] = 'delete: reached only from the decision-loop S-form proof (dropped)'
            r['detail'] = ''
        else:
            r['fate'] = 'UNASSIGNED'
            r['detail'] = ''
        r['families'] = fams
    # declarations whose every user is deleted (and that no kept family reaches)
    users = {r['name']: [q['name'] for q in rows if r['name'] in q['uses']] for r in rows}
    changed = True
    while changed:
        changed = False
        for r in rows:
            if r['fate'] != 'UNASSIGNED':
                continue
            us = users[r['name']]
            if us and all(by[u]['fate'].startswith('delete') for u in us):
                r['fate'] = 'delete: used only by deleted declarations'
                r['detail'] = ', '.join(us)
                changed = True
    # proposed private names of the moved declarations (prefix dropped, `a2_map` -> `fwdMap`)
    ns_of = {'ClassP/TimeConstructible.lean': 'Complexity.'}
    special = plan.get('new_names', {})
    moved = {}
    for r in rows:
        if not r['fate'].startswith('move') or r['family'] == 'public':
            continue
        n = r['name']
        if n in special:
            new = special[n]
        elif n.startswith('a2_map'):
            new = 'fwdMap' + n[len('a2_map'):]
        elif n.startswith('a2_Map'):
            new = 'FwdMap' + n[len('a2_Map'):]
        else:
            new = n[3:] if n.startswith('f2_') else n
        home = families[r['families'][0]]['home'] if r['families'] else 'Build/Loop.lean'
        full = ns_of.get(home, 'Turing.FinTM.') + new
        r['new_name'] = full
        moved[full] = home.split('/')[-1][:-5]
    json.dump(moved, open(os.path.join(out, 'moved-names.json'), 'w'), indent=1)
    json.dump(dict(region=[start, end], rows=rows), open(os.path.join(out, 'deletion-plan.json'), 'w'),
              indent=1, ensure_ascii=False)
    with open(os.path.join(out, 'deletion-plan.tsv'), 'w', encoding='utf-8') as f:
        f.write('line\tend\tname\tkind\tfamily\tlines\tlines_doc\tsource\tcode_identical\t'
                'statement_identical\tfate\tdetail\tnew_name\n')
        for r in rows:
            f.write('\t'.join(str(x) for x in [r['line'], r['end'], r['name'], r['kind'], r['family'],
                                              r['lines'], r['lines_doc'], r['source'] or '',
                                              r.get('code_identical', ''),
                                              r.get('statement_identical', ''), r['fate'],
                                              r['detail'], r.get('new_name', '')]) + '\n')
    # summary
    from collections import Counter, defaultdict
    print(f'region: lines {start}-{end} ({end - start + 1} lines); declarations {len(rows)}')
    c = Counter(r['family'] for r in rows)
    print('families:', dict(c))
    f2 = [r for r in rows if r['family'] == 'f2']
    print('f2 with same-named source:', sum(1 for r in f2 if r['source']),
          '; code-identical:', sum(1 for r in f2 if r.get('code_identical')),
          '(lines with docstrings', sum(r['lines_doc'] for r in f2 if r.get('code_identical')), ')',
          '; statement-identical only:', sum(1 for r in f2 if r['source'] and not r.get('code_identical')
                                              and r.get('statement_identical')),
          '; differing:', sum(1 for r in f2 if r['source'] and not r.get('statement_identical')),
          '; no source:', sum(1 for r in f2 if not r['source']))
    cr = [r for r in rows if r['family'] == 'catalog_redirect']
    print('catalog_redirect code-identical:', sum(1 for r in cr if r.get('code_identical')), 'of', len(cr))
    fc = defaultdict(lambda: [0, 0])
    for r in rows:
        k = r['fate'] if r['fate'] != 'move' else 'move: ' + r['detail']
        fc[(r['family'], k)][0] += 1
        fc[(r['family'], k)][1] += r['lines_doc']
    for (fam, k), (n, l) in sorted(fc.items()):
        print(f'  {fam:17s} {k}: {n} decls, {l} lines with docstrings')
    print('UNASSIGNED:', [r['name'] for r in rows if r['fate'] == 'UNASSIGNED'])


if __name__ == '__main__':
    main()
