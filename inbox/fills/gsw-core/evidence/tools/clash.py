"""Name-clash scan for the gsw-core fill (python3 -I).

Lists every declaration (public or private) of every `TCSlib/**/*.lean` file at the issue base,
resolving its full name through the `namespace … end` stack (and `_root_`), then lists the
declarations of the owned files at the final that are not declared in them at the base, and
reports any new name that is already declared anywhere in `TCSlib/` at the base. Also lists, as
information, base declarations elsewhere with the same last component.

usage: clash.py BASE_REV ROOT FILE...
"""
import re, subprocess, sys
from pathlib import Path

KW = r'(?:theorem|lemma|def|abbrev|structure|instance|inductive|class|opaque|axiom)'
DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)*((?:(?:private|protected|noncomputable|partial|unsafe)\s+)*)'
                  + KW + r'\s+([^\s(\[{:]+)')


def decls(src):
    out, stack = [], []
    for ln, line in enumerate(src.splitlines(), 1):
        m = re.match(r'^namespace\s+(\S+)', line)
        if m:
            stack.append(('ns', m.group(1)))
            continue
        m = re.match(r'^(?:noncomputable\s+)?section\b\s*(\S*)', line)
        if m:
            stack.append(('sec', m.group(1)))
            continue
        m = re.match(r'^end\b\s*(\S*)', line)
        if m and stack:
            stack.pop()
            continue
        m = DECL.match(line)
        if m:
            name = m.group(2)
            ns = '.'.join(x for k, x in stack if k == 'ns')
            full = name[len('_root_.'):] if name.startswith('_root_.') else \
                (ns + '.' + name if ns else name)
            out.append(dict(name=full, private='private' in m.group(1), line=ln))
    return out


def main(argv):
    base, root, files = argv[0], argv[1], argv[2:]
    listing = subprocess.check_output(['git', '-C', root, 'ls-tree', '-r', '--name-only', base,
                                       'TCSlib'], text=True).split()
    base_all = {}
    for path in listing:
        if not path.endswith('.lean'):
            continue
        src = subprocess.check_output(['git', '-C', root, 'show', f'{base}:{path}'], text=True)
        for d in decls(src):
            base_all.setdefault(d['name'], []).append(f'{path}:{d["line"]}')
    print(f'base: {len(listing)} paths, {sum(len(v) for v in base_all.values())} declarations '
          f'({len(base_all)} distinct full names) under TCSlib/')
    clashes = 0
    for path in files:
        try:
            bsrc = subprocess.check_output(['git', '-C', root, 'show', f'{base}:{path}'], text=True,
                                           stderr=subprocess.DEVNULL)
        except subprocess.CalledProcessError:
            bsrc = ''
        bnames = {d['name'] for d in decls(bsrc)}
        for d in decls((Path(root) / path).read_text()):
            if d['name'] in bnames:
                continue
            hits = base_all.get(d['name'], [])
            short = d['name'].rsplit('.', 1)[-1]
            same_short = sorted(f'{n} ({", ".join(v)})' for n, v in base_all.items()
                                if n.rsplit('.', 1)[-1] == short)
            status = 'CLASH' if hits else 'new'
            clashes += bool(hits)
            print(f'{status} {path}:{d["line"]} {"private " if d["private"] else ""}{d["name"]}'
                  + (f' already at {hits}' if hits else ''))
            if same_short:
                print(f'   info: same last component at base: {"; ".join(same_short)}')
    print(f'NAME CLASH SCAN {"PASS" if clashes == 0 else "FAIL"}: {clashes} clash(es)')
    return 1 if clashes else 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
