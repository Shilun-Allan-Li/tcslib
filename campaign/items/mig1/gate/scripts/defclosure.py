"""Private definition closure of root declarations inside one Lean file. Read-only.
Usage: python3 -I defclosure.py <file.lean> <root> [<root> ...]
Prints, in file order, every private declaration that the roots reach through identifier
occurrences in comment-stripped code (a definition's proof fields may cite private lemmas), plus
the private instances of every reached private inductive."""
import sys, os, re
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from decls import scan

TYPES = ('def', 'abbrev', 'inductive', 'structure', 'instance', 'class')


def strip(lines):
    out, depth = [], 0
    for s in lines:
        o, j = '', 0
        while j < len(s):
            if depth > 0:
                if s.startswith('/-', j): depth += 1; j += 2; continue
                if s.startswith('-/', j): depth -= 1; j += 2; continue
                j += 1; continue
            if s.startswith('/-', j): depth += 1; j += 2; continue
            if s.startswith('--', j): break
            o += s[j]; j += 1
        out.append(o)
    return out


def closure(path, roots):
    ds, lines = scan(path)
    code = strip(lines)
    byname = {}
    for d in ds:
        byname.setdefault(d['name'], []).append(d)
    text = {d['name']: '\n'.join(code[d['line'] - 1:d['end']]) for d in ds}
    privs = {d['name'] for d in ds if d['private']}
    ident = re.compile(r"[A-Za-z_][A-Za-z0-9_'.!?]*")
    seen, todo = set(), list(roots)
    while todo:
        n = todo.pop()
        if n in seen:
            continue
        seen.add(n)
        for tok in ident.findall(text.get(n, '')):
            for part in {tok, tok.split('.')[0], tok.split('.')[-1]}:
                if part in privs and part not in seen:
                    todo.append(part)
        # instances of reached inductives
        if any(d['kind'] == 'inductive' for d in byname.get(n, [])):
            for d in ds:
                if d['private'] and d['kind'] == 'instance' and d['name'] not in seen:
                    if re.search(r'\b' + re.escape(n) + r'\b', text[d['name']]):
                        todo.append(d['name'])
    res = [d for d in ds if d['name'] in seen]
    res.sort(key=lambda d: d['line'])
    return res


if __name__ == '__main__':
    path = sys.argv[1]
    res = closure(path, sys.argv[2:])
    tot = 0
    for d in res:
        n = d['end'] - d['line'] + 1
        tot += n
        print(f"{d['line']}-{d['end']} {d['kind']} {'P' if d['private'] else ' '} {d['name']} ({n})")
    print('code lines:', tot)
