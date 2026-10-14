"""Full names of the declarations of a Lean file (namespace-aware). Read-only.
Usage: python3 -I gatenames.py <file.lean> [--public]
Prints `line kind visibility fullname` for every declaration; with --public only non-private
ones. Tracks `namespace`/`end` lines and `_root_.` prefixes; `example`s are skipped."""
import os
import sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from decls import scan  # noqa: E402
from region import strip_comments  # noqa: E402


def names(path):
    ds, lines = scan(path)
    lines = strip_comments(lines)
    starts = {d['line']: d for d in ds}
    stack, out = [], []
    for i, l in enumerate(lines, 1):
        if l.startswith('namespace '):
            stack.append(l.split()[1])
        elif l.startswith('end ') and stack and l.split()[1] == stack[-1]:
            stack.pop()
        if i in starts:
            d = starts[i]
            n = d['name']
            if not n:
                continue
            full = n[len('_root_.'):] if n.startswith('_root_.') else '.'.join(stack + [n])
            out.append((i, d['kind'], 'private' if d['private'] else 'public', full))
    return out


if __name__ == '__main__':
    pub = '--public' in sys.argv
    for i, k, v, f in names(sys.argv[1]):
        if pub and v == 'private':
            continue
        print(i, k, v, f)
