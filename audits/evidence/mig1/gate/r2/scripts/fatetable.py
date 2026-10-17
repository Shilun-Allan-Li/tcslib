"""The deletion plan's fate-count table (the pack's table), from deletion-plan.json. Read-only.

Usage: python3 -I fatetable.py <deletion-plan.json>

Groups the 378 region declarations by fate (moves by their family) and prints, per group, the
number of declarations and of docstring-inclusive lines, then the total. The last line is
`total: <declarations> declarations, <lines> lines`.
"""
import json
import sys
from collections import OrderedDict

rows = json.load(open(sys.argv[1], encoding='utf-8'))['rows']
ORDER = [
    ('delete: copy, original used', 'f2', 'Delete: `f2_` copy code-identical to its home source'),
    ('delete: copy, original used', 'catalog_redirect',
     'Delete: `catalog_redirect*` copies of Wrappers\' redirect family'),
    ('delete: statement-identical copy (proof differs), original used', None,
     'Delete: statement-identical copy, different proof'),
    ('delete: modified copy, citations re-targeted at the original', None,
     'Delete: modified copy, citations re-targeted at the original'),
    ("delete: its fuel-head clause is added to Loop's loopHost_prepare (strengthened in place)",
     None, 'Delete: `f2_loopHost_prepare`; its fuel-head clause is added to Loop\'s original'),
    ('delete: duplicates an existing public declaration', None,
     'Delete: duplicates a public declaration'),
    ('delete: dead (reached from no public declaration)', None, 'Delete: dead'),
    ('delete: used only by deleted declarations', None, 'Delete: used only by deleted'),
    ('delete: reached only from the decision-loop S-form proof (dropped)', None,
     'Delete: decision-loop S-form only (the `a2_` ledger)'),
    ('absorbed into a gated public statement', None, 'Absorbed into a gated statement'),
    ('move:Build/Primitives.lean (forwarding map)', None, 'Move: forwarding map -> Primitives'),
    ('move:Build/Primitives.lean (polynomial space)', None, 'Move: polynomial space -> Primitives'),
    ('move:ClassP/TimeConstructible.lean (counter space)', None,
     'Move: counter space -> TimeConstructible'),
    ('move:Build/Wrappers.lean (conditional ledger)', None, 'Move: conditional ledger -> Wrappers'),
    ('move:Build/Loop.lean (loop budget)', None, 'Move: loop budget -> Loop'),
    ('move: replaces the original (extended statement)', None,
     'Move, replacing the original: the extended `loopHost_contracts`'),
    ('move:Build/Primitives.lean (pair length)', None, 'Move: pair length -> Primitives'),
    ('corollary in place (statement and name unchanged; proof from the gated specs)', None,
     'Public: space rows, corollaries in place'),
    ('move (statement, name and proof unchanged)', None, 'Public: two rewind lemmas -> Simulation'),
]
groups = OrderedDict((label, [0, 0, []]) for _, _, label in ORDER)
seen = set()
for r in rows:
    key = r['fate'] if r['fate'] != 'move' else 'move:' + r['detail']
    for fate, fam, label in ORDER:
        if key == fate and (fam is None or r['family'] == fam):
            g = groups[label]
            g[0] += 1
            g[1] += r['lines_doc']
            g[2].append(r['name'])
            seen.add(r['name'])
            break
missing = [r['name'] for r in rows if r['name'] not in seen]
assert not missing, missing
for label, (n, l, ns) in groups.items():
    extra = f'  [{", ".join(ns)}]' if n <= 2 else ''
    print(f'{label} | {n} | {l:,}{extra}')
print(f'total: {sum(g[0] for g in groups.values())} declarations, '
      f'{sum(g[1] for g in groups.values()):,} lines')
