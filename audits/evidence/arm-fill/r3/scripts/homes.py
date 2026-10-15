"""R2-5: the lower homes named for the I032, I040 and I064 factorings, checked on one tree's import
graph (scripts/imports.py output) and sources. For each factoring: why "cite" fails as round 2
wrote it (the source imports the consumer), and that the named home is imported, directly or
transitively, by every user, with the definitions the moved text needs defined at or below it.
Text-level (ESTIMATE that the moved proof elaborates there; no Lean is run).
usage: python3 -I homes.py <tree-root> <graph.json>"""
import json, os, re, sys
root, gj = sys.argv[1:3]
g = json.load(open(gj, encoding='utf-8'))
P = 'TCSlib/Complexity/SpaceComplexity/'
def clo(m):
    seen, st = set(), [m]
    while st:
        for y in g.get(st.pop(), []):
            if y not in seen: seen.add(y); st.append(y)
    return seen
def imp(a, b): return b in clo(a)
def where(name):
    pat = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*(?:theorem|lemma|def|abbrev)\s+(?:\S+\.)?' + re.escape(name) + r'\b')
    out = []
    for dp, _, fn in os.walk(os.path.join(root, 'TCSlib')):
        for f in fn:
            if f.endswith('.lean'):
                p = os.path.join(dp, f)
                for i, l in enumerate(open(p, encoding='utf-8'), 1):
                    if pat.match(l): out.append((os.path.relpath(p, root)[:-5], i))
    return out
ok = True
def check(label, cond):
    global ok
    ok &= bool(cond); print(('OK   ' if cond else 'FAIL ') + label)
print('# I032 (K9): Bridge.mem_iff_codeChain repeats ExpBFS/Radius.inWin_runWith_of_decides')
check('ExpBFS/Radius imports Codec/Bridge (so Bridge cannot cite Radius)', imp(P + 'ExpBFS/Radius', P + 'Codec/Bridge'))
check('Codec/Bridge imports ConfigGraph (the named home)', imp(P + 'Codec/Bridge', P + 'ConfigGraph'))
check('ExpBFS/Radius imports ConfigGraph', imp(P + 'ExpBFS/Radius', P + 'ConfigGraph'))
for n in ['runWith_take_inWindow', 'runWith_append', 'runWith_of_halt']:
    w = [m for m, _ in where(n) if m == P + 'ConfigGraph' or imp(P + 'ConfigGraph', m)]
    check(f'`{n}` (cited by the window lemma) is defined at or below ConfigGraph: {w}', w)
print('# I040 (K20): Parse.bitsVal_le_of_width contains Codec/Layout.two_pow_bits_le')
check('Codec/Layout imports Codec/Parse (so Parse cannot cite Layout)', imp(P + 'Codec/Layout', P + 'Codec/Parse'))
print('  the named home is Codec/Parse itself: the bound moves there and Layout keeps it through its import')
print('# I064 (K20): ExpBFS/Relax.stp and SavitchARM/Recursion.Rel build the same encoded step query')
users = [P + 'ExpBFS/Relax', P + 'SavitchARM/Recursion', P + 'Logspace/PathHardRegs']
check('no Codec module is imported by ExpBFS/Relax (so a Codec home is not below it)', not any(m.startswith(P + 'Codec/') for m in clo(P + 'ExpBFS/Relax')))
check('Logspace/InputAccess (the named home) is imported by all three query builders (Relax, Recursion, PathHardRegs)', all(imp(u, P + 'Logspace/InputAccess') for u in users))
w = [(m, i) for m, i in where('pairEncode') if imp(P + 'Logspace/InputAccess', m)]
check(f'a `pairEncode` definition is at or below InputAccess (module, line): {w}', w)
print('  the slot (2 or 3; 4 in PathHardRegs) and the result view (Bool, or `= true`) stay at the use sites')
print('all checks pass' if ok else 'SOME CHECK FAILED')
