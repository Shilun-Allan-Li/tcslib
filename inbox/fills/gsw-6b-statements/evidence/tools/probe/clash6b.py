"""clash6b.py <newnames.tsv> <base-names.tsv> <pr355-names.tsv> (gsw-6b-statements, sub-agent probe; new; check 11
(a)-(b)). <newnames.tsv> is the Lean dump of every non-internal constant declared by the new/changed modules at the
final head (NameDump.lean: full name, kind, module), private names demangled. The other two are declnames.py's
textual inventories of TCSlib/, TCSlib.lean and audits/ at the base and at #355's head.
(a) CLASH: a new full name that is declared at the base or at #355's head (outside the new files), or that equals
    or ends with a GF-W1 reserved name. (b) SHORT: every new short name (last component) declared elsewhere, with
    the full names and locations there (excluding the new files themselves)."""
import sys, collections
newf, basef, prf = sys.argv[1:4]
RESERVED = ['TreeCircuit.maxDepth_le_of_forall', 'TreeCircuit.maxFaninL_le_of_forall', 'prefixVal_eq_of_false',
            'prefixVal_testBit', 'depth_getD_le', 'maxFanin_getD_le']
NEWFILES = ('GSW/Branching.lean', 'GSW/DecryptFormula.lean', 'GSW/Bootstrap.lean', 'GSW/Circular.lean',
            'GSW/Leveled.lean', 'GSW/LeveledSecurity.lean', 'GSW/PolyRatio.lean', 'GSW/Asymptotic.lean',
            'LWE/Ratio.lean')
def load(p):
    full, short = collections.defaultdict(list), collections.defaultdict(list)
    for l in open(p):
        if l.startswith('#'): continue
        n, s, kind, priv, loc = l.rstrip('\n').split('\t')
        if loc.split(':')[0].endswith(NEWFILES): continue
        full[n].append(f'{loc} ({kind}, {priv})'); short[s].append(f'{n} @ {loc}')
    return full, short
bfull, bshort = load(basef); pfull, pshort = load(prf)
new = [l.rstrip('\n').split('\t') for l in open(newf) if not l.startswith('#') and l.strip()]
bad = 0
print('# (a) full-name clashes against the base, #355 head and the GF-W1 reserved names')
for n, kind, mod in new:
    hits = []
    if n in bfull: hits.append(f'base: {bfull[n]}')
    if n in pfull: hits.append(f'#355: {pfull[n]}')
    for r in RESERVED:
        if n == r or n.endswith('.' + r): hits.append(f'GF-W1 reserved {r}')
    if hits: bad += 1; print(f'CLASH\t{n}\t{kind}\t{mod}\t' + '; '.join(hits))
    else: print(f'ok\t{n}\t{kind}\t{mod}')
print(f'RESULT-a new_names={len(new)} clashes={bad}')
print('# (b) new short names declared elsewhere (base; #355 head additions marked)')
shorts = collections.OrderedDict()
for n, kind, mod in new: shorts.setdefault(n.split('.')[-1], []).append(n)
k = 0
for s, ns in shorts.items():
    el = sorted(set(bshort.get(s, [])))
    el355 = sorted(set(pshort.get(s, [])) - set(el))
    if el or el355:
        k += 1
        print(f'SHORT\t{s}\tnew: {", ".join(ns)}\t{len(el)} elsewhere at base' +
              (f', {len(el355)} more at #355' if el355 else ''))
        for e in el[:12]: print(f'\t\t{e}')
        if len(el) > 12: print(f'\t\t... {len(el) - 12} more')
        for e in el355[:5]: print(f'\t\t#355: {e}')
print(f'RESULT-b short_names={len(shorts)} shared_elsewhere={k}')
sys.exit(1 if bad else 0)
