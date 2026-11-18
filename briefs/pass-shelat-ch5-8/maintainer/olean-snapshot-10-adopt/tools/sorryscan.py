"""sorryscan.py <repo> <rev> <order.txt>: syntactic admission census (maintainer, gsw-6a-fills review).
Comments (nested block, line) and string literals are stripped; each `sorry`/`admit` token is
attributed to the enclosing column-0 declaration.  Also counts `native_decide`, `axiom` declarations.
Prints `module: n: names` per module with admissions and a TOTAL line."""
import sys, re, subprocess
repo, rev, order = sys.argv[1:4]


def strip(s):
    out, i, n, depth = [], 0, len(s), 0
    while i < n:
        if s.startswith('/-', i):
            depth += 1; i += 2; continue
        if depth:
            if s.startswith('-/', i):
                depth -= 1; i += 2; continue
            out.append('\n' if s[i] == '\n' else ' '); i += 1; continue
        if s.startswith('--', i):
            while i < n and s[i] != '\n':
                i += 1
            continue
        if s[i] == '"':
            out.append(' '); i += 1
            while i < n and s[i] != '"':
                if s[i] == '\\':
                    i += 1
                out.append('\n' if i < n and s[i] == '\n' else ' '); i += 1
            i += 1; continue
        if s[i] == "'" and i + 2 < n and (s[i + 2] == "'" or (s[i + 1] == '\\' and s.find("'", i + 2) - i < 6)):
            j = s.find("'", i + 2 if s[i + 1] != '\\' else i + 3)
            out.append(' ' * (j - i + 1)); i = j + 1; continue
        out.append(s[i]); i += 1
    return ''.join(out)


DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*'
                  r'(theorem|lemma|def|abbrev|instance|example|structure|inductive|axiom|opaque)\s*(\S*)')
tot, mods, nat, ax = 0, 0, 0, 0
for m in [l.strip() for l in open(order) if l.strip()]:
    src = subprocess.run(['git', '-C', repo, 'show', f'{rev}:{m}.lean'], capture_output=True,
                         check=True).stdout.decode('utf-8')
    L = strip(src).split('\n')
    cur, ns, hits = None, [], []
    for l in L:
        mm = re.match(r'^namespace\s+(\S+)', l)
        if mm:
            ns.append(mm.group(1))
        me = re.match(r'^end\s+(\S+)\s*$', l)
        if me and ns and ns[-1] == me.group(1):
            ns.pop()
        d = DECL.match(l)
        if d:
            cur = d.group(2) or d.group(1)
            if d.group(1) == 'axiom':
                ax += 1; print(f'AXIOM {m}: {cur}')
        if re.search(r'(?<![\w.])(sorry|admit)(?![\w.])', l) and cur and (not hits or hits[-1] != cur):
            hits.append(cur)
        if re.search(r'(?<![\w.])native_decide(?![\w.])', l):
            nat += 1; print(f'NATIVE_DECIDE {m}: {cur}')
    if hits:
        mods += 1; tot += len(hits)
        print(f'{m}: {len(hits)}: {", ".join(hits)}')
print(f'TOTAL {tot} in {mods} modules; native_decide {nat}; axiom {ax}')
