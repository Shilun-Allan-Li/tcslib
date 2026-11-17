#!/usr/bin/env python3
"""clashshadow.py <base-checkout> <head-checkout> <targets.tsv> <closures.txt> <outdir>   (cleanup-stage1)

Check 11 of the brief.
(a) EXACT clashes: no new full name (targets.tsv) already names a declaration (public or private) in any
    .lean file under TCSlib/ or audits/ of <base-checkout> (the check base, tree 01cc6259...).
(b) SAME SHORT NAME: for every new full name, every declaration of the check base with the same last
    component (namespaces resolved from `namespace`/`end` lines; `_root_.` honoured; private included),
    and whether the new declaration is `protected` in <head-checkout> (read from its declaration line).
    A new name whose short name exists elsewhere and that is not protected is a FAIL.
(c) SHADOW: for every new full name N.x, every unqualified token `x` (comments and strings stripped,
    not preceded by `.` or followed by a name character) in a module of DOWN (closures.txt) plus the two
    new modules, whose enclosing namespace is N's namespace or lies under it, or whose file opens that
    namespace (an `open` item O with ns == O or ns ending in '.' + O).  Each hit is listed with the
    verdict: protected (never found by its short name: resolution unchanged) or fresh (no declaration
    with this short name existed, so the token could only name a local, which still takes precedence).
Writes clash.tsv, shortname.tsv, shadow.tsv and summary.txt in <outdir>.
"""
import os, re, sys

base, head, tsv, clos, outdir = sys.argv[1:6]
os.makedirs(outdir, exist_ok=True)
T = [l.rstrip('\n').split('\t') for l in open(tsv) if l.strip()]
KW = re.compile(r'^(?:@\[[^\]]*\]\s*)*((?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*)'
                r'(?:theorem|lemma|def|abbrev|structure|inductive|instance|class|opaque|axiom)\s+'
                r'([^\s(:{\[]+)')


def strip(src):
    src = re.sub(r'/-.*?-/', lambda m: '\n' * m.group(0).count('\n'), src, flags=re.S)
    src = re.sub(r'--[^\n]*', '', src)
    return re.sub(r'"(?:[^"\\\n]|\\.)*"', '""', src)


def scan_decls(root):
    idx = {}
    for top in ('TCSlib', 'audits'):
        for r, _, fs in os.walk(os.path.join(root, top)):
            for fn in fs:
                if not fn.endswith('.lean'):
                    continue
                p = os.path.relpath(os.path.join(r, fn), root)
                ns = []
                for i, l in enumerate(strip(open(os.path.join(root, p), encoding='utf-8').read())
                                      .split('\n')):
                    m = re.match(r'^namespace\s+(\S+)', l)
                    if m:
                        ns.append(m.group(1)); continue
                    m = re.match(r'^end\s+(\S+)\s*$', l)
                    if m and ns and ns[-1] == m.group(1):
                        ns.pop(); continue
                    m = KW.match(l)
                    if m:
                        n = m.group(2)
                        full = n[7:] if n.startswith('_root_.') else '.'.join(ns + [n])
                        idx.setdefault(full.split('.')[-1], []).append(
                            (full, p, i + 1, 'private' in m.group(1)))
    return idx


def protected_in_head(full, path):
    short = full.split('.')[-1]
    for l in open(os.path.join(head, path), encoding='utf-8'):
        m = KW.match(l)
        if m and m.group(2).split('.')[-1] == short and (
                m.group(2) == short or full.endswith(m.group(2).replace('_root_.', ''))):
            return 'protected' in m.group(1)
    return None


idx = scan_decls(base)
clash = open(os.path.join(outdir, 'clash.tsv'), 'w')
short = open(os.path.join(outdir, 'shortname.tsv'), 'w')
nexact = nfail = nprot = 0
info = {}
for tid, full, kind, P, path in T:
    s = full.split('.')[-1]
    hits = [h for h in idx.get(s, []) if h[0] != full or True]
    exact = [h for h in hits if h[0] == full]
    nexact += len(exact)
    prot = protected_in_head(full, path)
    nprot += bool(prot)
    others = [h for h in hits if h[0] != full]
    verdict = 'OK'
    if others and not prot:
        verdict = 'FAIL(unprotected)'; nfail += 1
    if (P == 'P') != bool(prot):
        verdict += ' MISMATCH(brief P=%s, head protected=%s)' % (P, prot)
    clash.write(f'{tid}\t{full}\tEXACT {len(exact)}\n')
    for h in exact:
        clash.write(f'    {h[0]}\t{h[1]}:{h[2]}\t{"private" if h[3] else "public"}\n')
    short.write(f'{tid}\t{full}\tprotected={prot}\tbrief={P}\tsame-short-name={len(others)}\t{verdict}\n')
    for h in others:
        short.write(f'    {h[0]}\t{h[1]}:{h[2]}\t{"private" if h[3] else "public"}\n')
    info[full] = (prot, len(others), path)
clash.write(f'RESULT exact full-name clashes: {nexact}\n')
short.write(f'RESULT protected {nprot}; unprotected with same short name: {nfail}\n')
clash.close(); short.close()

down = [l.split('\t')[3].strip() for l in open(clos) if l.startswith('DOWN\t')]
down += ['TCSlib/Cryptography/Games/Tapes', 'TCSlib/Cryptography/ZeroKnowledge/InteractionWords']
sh = open(os.path.join(outdir, 'shadow.tsv'), 'w')
nhits = nbad = 0
for m in down:
    p = os.path.join(head, m + '.lean')
    if not os.path.exists(p):
        continue
    lines = strip(open(p, encoding='utf-8').read()).split('\n')
    ns, opens = [], []
    for i, l in enumerate(lines):
        mm = re.match(r'^\s*namespace\s+(\S+)', l)
        if mm:
            ns.append(mm.group(1))
        mm = re.match(r'^\s*end\s+(\S+)\s*$', l)
        if mm and ns and ns[-1] == mm.group(1):
            ns.pop()
        mm = re.match(r'^\s*open\s+(.*)$', l)
        if mm:
            opens += [o for o in re.split(r'\s+', mm.group(1).split(' in ')[0]) if o and o[0].isalpha()]
        cur = '.'.join(ns)
        for full, (prot, nother, path) in info.items():
            parts = full.split('.')
            x, N = parts[-1], '.'.join(parts[:-1])
            if not re.search(r'(?<![\w.\'])' + re.escape(x) + r'(?![\w\'!?₀-₉])', l):
                continue
            inside = cur == N or cur.startswith(N + '.')
            opened = any(N == o or N.endswith('.' + o) for o in opens)
            if not (inside or opened):
                continue
            if m + '.lean' == path and re.match(r'^\s*(?:@\[[^\]]*\]\s*)*(?:\w+\s+)*'
                                                 r'(?:theorem|def|lemma)\s', l):
                where = 'its own declaration line'
            else:
                where = 'use'
            if prot:
                v = 'unchanged: the new name is protected (not found by its short name)'
            elif nother == 0:
                v = 'unchanged: fresh short name (no declaration had it; only a local could)'
            else:
                v = 'CHECK: unprotected new name with an existing short name'; nbad += 1
            nhits += 1
            sh.write(f'{m}.lean:{i + 1}\t{full}\tns={cur or "-"}\t'
                     f'{"inside" if inside else "opens"}\t{where}\t{v}\n')
sh.write(f'RESULT shadow hits {nhits}; needing attention {nbad}\n')
sh.close()
open(os.path.join(outdir, 'summary.txt'), 'w').write(
    f'targets {len(T)}\nexact clashes {nexact}\nprotected {nprot}\n'
    f'unprotected with same short name {nfail}\nshadow hits {nhits}\nshadow needing attention {nbad}\n')
print(open(os.path.join(outdir, 'summary.txt')).read())
