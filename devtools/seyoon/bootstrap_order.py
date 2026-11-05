"""bootstrap_order.py <worktree> [<skipped list>]: every module the root `TCSlib.lean` imports,
transitively (what CI builds), without the root itself, as paths without `.lean`, in dependency
order (imports first). Replay lists reach outside `TCSlib/Complexity` (its importers in other
folders), so a snapshot needs them all. A missing import or a cycle stops it (exit 2).

A module that imports a package with no compiled oleans in the worktree's `.lake/packages` (on
the cloud machine, `PFR`: the Mathlib cache does not cover it, and it is not built) cannot be
compiled; it and every module importing it are left out of the order. If a second argument is
given, the left-out modules are written there, in order, each with the packages it lacks."""
import glob
import os
import re
import sys

wt = sys.argv[1]
skipped_out = sys.argv[2] if len(sys.argv) > 2 else None
CORE = {'Init', 'Std', 'Lean', 'Lake'}
LIBS = glob.glob(os.path.join(wt, '.lake/packages/*/.lake/build/lib/lean'))
avail = {}


def available(prefix):
    if prefix not in avail:
        avail[prefix] = prefix in CORE or any(
            os.path.isdir(os.path.join(d, prefix)) or os.path.exists(os.path.join(d, prefix + '.olean'))
            for d in LIBS)
    return avail[prefix]


src = {}


def text(m):
    if m not in src:
        p = os.path.join(wt, m + '.lean')
        if not os.path.exists(p):
            sys.exit(f'missing module {m}')
        src[m] = open(p, encoding='utf-8').read()
    return src[m]


def imports(m):
    return [i.replace('.', '/') for i in re.findall(r'^import\s+(TCSlib\S*)', text(m), re.M)]


def header_imports(m):
    """The `import` lines of the file's header: before the first line that is not blank, a
    comment, or an import (a docstring line that begins with "import" is not an import)."""
    out, in_block = [], False
    for line in text(m).split('\n'):
        s = line.strip()
        if in_block:
            in_block = '-/' not in s
            continue
        if s.startswith('/-'):
            in_block = '-/' not in s[2:]
            continue
        if s == '' or s.startswith('--'):
            continue
        mm = re.match(r'import\s+(\S+)', s)
        if not mm:
            break
        out.append(mm.group(1))
    return out


def lacking(m):
    return sorted({i.split('.')[0] for i in header_imports(m)
                   if not i.startswith('TCSlib') and not available(i.split('.')[0])})


roots = imports('TCSlib')
order, state = [], {}


def visit(m):
    if state.get(m) == 2:
        return
    if state.get(m) == 1:
        sys.exit(f'import cycle at {m}')
    state[m] = 1
    for i in imports(m):
        if i != 'TCSlib':
            visit(i)
    state[m] = 2
    order.append(m)


sys.setrecursionlimit(20000)
for m in sorted(roots):
    visit(m)
skip, why = set(), {}
for m in order:                       # imports come first, so one pass propagates
    own = lacking(m)
    via = [i for i in imports(m) if i in skip]
    if own or via:
        skip.add(m)
        why[m] = ('lacks ' + ', '.join(own)) if own else ('imports ' + via[0])
print('\n'.join(m for m in order if m not in skip))
if skipped_out is not None:
    with open(skipped_out, 'w', encoding='utf-8') as f:
        for m in order:
            if m in skip:
                f.write(f'{m}\t{why[m]}\n')
