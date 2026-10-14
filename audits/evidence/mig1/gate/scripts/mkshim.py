"""Emit verbatim copies of declarations of one Lean file, in file order, with an identifier
rename applied (token level, dotted components renamed one by one). Read-only on the source.

Usage: python3 -I mkshim.py <file.lean> <rename.json|-> [--stmt] [--public] [--nodoc] <name> ...

With --stmt, every theorem/lemma body is replaced by `sorry` (statement shims; with --nodoc and
without --public a one-line shim docstring naming the source is added); with --public the
leading `private` is removed (and `lemma` becomes `theorem`); with --nodoc the preceding docstring is not copied (by default it
is).
"""
import json
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from decls import scan  # noqa: E402

IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_'!?]*(?:\.[A-Za-z_][A-Za-z0-9_'!?]*)*")


def rename_line(l, mapping):
    def sub(m):
        return '.'.join(mapping.get(p, p) for p in m.group(0).split('.'))
    # do not rename inside string literals or comments: the files have no string literals in
    # these declarations; comments are renamed too (docstrings name the declarations).
    return IDENT.sub(sub, l)


def stmt_cut(lines):
    """Index (line, col) of the `:=` that opens a theorem's proof: the first top-level `:= by`
    that ends a line, else the first top-level `:=` (a statement may contain `let x := e`)."""
    depth = 0
    for i, l in enumerate(lines):
        for j in range(len(l)):
            ch = l[j]
            if ch in '([{⟨':
                depth += 1
            elif ch in ')]}⟩':
                depth -= 1
            elif depth == 0 and l.startswith(':= by', j) and l[j + 5:].strip() == '':
                return i, j
    depth = 0
    for i, l in enumerate(lines):
        j = 0
        while j < len(l):
            ch = l[j]
            if ch in '([{⟨':
                depth += 1
            elif ch in ')]}⟩':
                depth -= 1
            elif depth == 0 and l.startswith(':=', j):
                return i, j
            j += 1
    raise ValueError('no :=')


def main():
    path, rmap = sys.argv[1], sys.argv[2]
    args = sys.argv[3:]
    stmt = public = nodoc = False
    while args and args[0].startswith('--'):
        flag = args.pop(0)
        if flag == '--stmt':
            stmt = True
        elif flag == '--public':
            public = True
        elif flag == '--nodoc':
            nodoc = True
        else:
            raise SystemExit(f'unknown flag {flag}')
    mapping = {} if rmap == '-' else json.load(open(rmap, encoding='utf-8'))
    ds, lines = scan(path)
    want = set(args)
    found = set()
    out = []
    for d in sorted(ds, key=lambda d: d['line']):
        if d['name'] not in want:
            continue
        found.add(d['name'])
        s = d['line'] - 1
        j = s - 1
        if j >= 0 and lines[j].rstrip().endswith('-/') and not nodoc:
            k = j
            while k >= 0 and not lines[k].lstrip().startswith('/--'):
                k -= 1
            if k >= 0:
                s = k
        body = lines[s:d['end']]
        while body and body[-1].strip() == '':
            body.pop()
        if public:
            off = d['line'] - 1 - s
            if body[off].startswith('private '):
                body[off] = body[off][len('private '):]
            if body[off].startswith('lemma '):
                body[off] = 'theorem ' + body[off][len('lemma '):]
        if stmt and d['kind'] in ('theorem', 'lemma'):
            off = d['line'] - 1 - s
            i, c = stmt_cut(body[off:])
            i += off
            body = body[:i] + [body[i][:c] + ':= by', '  sorry']
            if nodoc and not public:
                body = [f"/-- Statement shim of `{d['name']}` (`{os.path.basename(path)}:"
                        f"{d['line']}`), proved in the tree.", "**Proof sketch.** See the source. -/"] + body
        out.append('\n'.join(rename_line(l, mapping) for l in body))
    missing = want - found
    if missing:
        raise SystemExit(f'not found: {sorted(missing)}')
    print('\n\n'.join(out))


if __name__ == '__main__':
    main()
