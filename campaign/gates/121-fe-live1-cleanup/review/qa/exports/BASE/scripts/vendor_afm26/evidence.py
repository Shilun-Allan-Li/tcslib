import sys, difflib
# usage: evidence.py <upstream root> <worktree> <vendor-map.tsv> <upstream module list> <evidence dir>
up, wt, mapf, modf, ev = sys.argv[1:6]
ups = [l.strip() for l in open(modf) if l.strip()]
rows = [l.rstrip('\n').split('\t') for l in open(mapf) if l.strip()]
assert len(ups) == len(rows)
out, table = [], ['| Upstream file | Vendored file | Lines (upstream → vendored) | Changed lines outside the header and imports |', '|---|---|---|---|']
def mech(x):
    s = x[1:].strip()
    return (s.startswith(('import ', 'public import ')) or s in ('module', '@[expose] public section', 'public section', 'section')
            or s.startswith(('set_option maxHeartbeats', 'set_option relaxedAutoImplicit', 'set_option autoImplicit'))
            or s == '' or s.startswith(('Vendored from', '`3sum-apsp`', 'Local modifications', '* ', '  for compat', 'The remaining content')))
for m, (nm, rel, notes) in zip(ups, rows):
    upath = 'EndStatement.lean' if m == 'EndStatement' else m.replace('.', '/') + '.lean'
    a = open(f'{up}/{upath}', encoding='utf-8').read().split('\n'); b = open(f'{wt}/{rel}', encoding='utf-8').read().split('\n')
    d = list(difflib.unified_diff(a, b, f'upstream/{upath}', f'tcslib/{rel}', lineterm='', n=1))
    out += d
    sub = [x for x in d if x[:1] in '+-' and not x.startswith(('+++', '---')) and not mech(x)]
    table.append(f'| `{upath}` | `{rel}` | {len(open(f"{up}/{upath}", encoding="utf-8").read().splitlines())} → {len(open(f"{wt}/{rel}", encoding="utf-8").read().splitlines())} | {len(sub)} |')
open(f'{ev}/upstream-to-vendored.diff', 'w', encoding='utf-8').write('\n'.join(out) + '\n')
open(f'{ev}/file-map.md', 'w', encoding='utf-8').write(
  '# Vendored files: upstream → tcslib\n\nUpstream: anthropics/formal-math, folder `3sum-apsp`, commit '
  'e1a4e6508154ea59f030480661590a9fe3018011. "Changed lines" counts diff lines other than the module-system lines, '
  'imports, the standard options and the vendoring header; they are the renames, the `## References` sections, the '
  'proof repairs and the word-RAM trim, each listed in the file\'s header.\n\n' + '\n'.join(table) + '\n')
print(len(rows), 'files;', len(out), 'diff lines')
