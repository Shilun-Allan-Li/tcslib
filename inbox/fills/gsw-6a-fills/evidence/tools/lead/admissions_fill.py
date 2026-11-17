"""admissions_fill.py <base-sorries.txt> <targets.txt> <summary.tsv>... (gsw-6a-fills, new; check 2): the `sorry`
declarations per module from pbuild summaries (the last record of a module wins, so pass the bootstrap first and
the head sweep after it), compared with base-sorries.txt minus the proved targets. <targets.txt> is the pack's;
pass `--proved <unit,...>` to say which units are proved at this head (default: all six). Exit 1 on mismatch."""
import sys, re, collections
args = sys.argv[1:]
proved = None
if '--proved' in args:
    i = args.index('--proved'); proved = set(args[i + 1].split(',')); del args[i:i + 2]
bs, tg = args[:2]; sums = args[2:]
base = {}
for l in open(bs):
    m = re.match(r'^(\S+): (\d+): (.*)$', l.strip())
    if m: base[m.group(1)] = [x.strip() for x in m.group(3).split(',')]
gone = collections.defaultdict(set)
for l in open(tg):
    if l[0] == 'U':
        u, row, fl, name = l.rstrip('\n').split('\t')
        if proved is None or u in proved:
            gone[fl.split(':')[0][:-5]].add(name)
built = {}
for s in sums:
    for l in open(s):
        f = l.rstrip('\n').split('\t')
        if len(f) > 5 and f[1].startswith('rc='):
            built[f[0]] = [x for x in f[5][len('decls='):].split(',') if x]
bad = 0; total = 0; mods = 0
for m in sorted(set(base) | {k for k, v in built.items() if v}):
    want = sorted(n for n in base.get(m, []) if not any(full.endswith('.' + n.replace('_root_.', '')) or full == n for full in gone.get(m, ())))
    got = sorted(built.get(m, []))
    ok = want == got
    bad += not ok
    if got: total += len(got); mods += 1
    print(f'{"OK" if ok else "MISMATCH"}\t{m}\tsorry_decls={len(got)}\texpected={len(want)}' + ('' if ok else f'\tgot={got}\twant={want}'))
print(f'RESULT declarations={total} modules={mods} mismatches={bad}')
sys.exit(1 if bad else 0)
