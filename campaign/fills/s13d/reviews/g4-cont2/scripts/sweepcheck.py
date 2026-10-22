import re, sys, os
# usage: sweepcheck.py <order list> <base sorries> <final-sweep.log> <bootstrap.log> <base tree> <head tree>
order_p, sorr_p, sweep_p, boot_p, base, head = sys.argv[1:7]
order = [l.strip() for l in open(order_p) if l.strip()]
def runs(p, stop=None):
    t = open(p, encoding='utf-8').read()
    if stop and stop in t: t = t[:t.index(stop)]
    seq, cur, warns, status = [], None, {}, {}
    for l in t.split('\n'):
        m = re.match(r'^START (\S+) ', l)
        if m: cur = m.group(1); seq.append(cur); warns.setdefault(cur, []); continue
        m = re.match(r'^END (\S+) .* status=(\d+)', l)
        if m: status.setdefault(m.group(1), []).append(int(m.group(2))); continue
        m = re.match(r"^(\S+\.lean):(\d+):(\d+): (warning|error): (.*)", l)
        if m and cur: warns[cur].append((m.group(1), int(m.group(2)), m.group(4), m.group(5)))
    return seq, warns, status, t
seq, warns, status, text = runs(sweep_p, '===== ADDITIONAL')
print(f'final sweep: {len(seq)} module runs; equal to the order list in order: {seq == order}')
print(f'every END status 0: {all(all(s == 0 for s in v) for v in status.values()) and len(status) == len(seq)}')
errs = [(m, w) for m in warns for w in warns[m] if w[2] == 'error']
print(f'error lines in the sweep: {len(errs)}; lines with "error:" anywhere before the additional sections: {len(re.findall(r": error:", text))}')
bseq, bw, bst, _ = runs(boot_p, '===== ENVIRONMENT')
print(f'bootstrap: {len(bseq)} runs, {len(set(bseq))} distinct; set equal to the order list: {set(bseq) == set(order)}; all status 0: {all(all(s == 0 for s in v) for v in bst.values())}')
# bootstrap order: two sublists, each in the order list's relative order
idx = {m: i for i, m in enumerate(order)}
k = next((i for i in range(1, len(bseq)) if idx[bseq[i]] < idx[bseq[i-1]]), None)
if k is not None:
    a, b = bseq[:k], bseq[k:]
    print(f'bootstrap split at run {k}: first sublist {len(a)} increasing {all(idx[a[i]] < idx[a[i+1]] for i in range(len(a)-1))}, second {len(b)} increasing {all(idx[b[i]] < idx[b[i+1]] for i in range(len(b)-1))}; first ends with {a[-1]}')
# map sorry warnings to declaration names
DECL = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*(?:theorem|lemma|def|abbrev|instance|structure)\s+(\S+)')
def declname(tree, f, ln):
    L = open(os.path.join(tree, f), encoding='utf-8').read().split('\n')
    m = DECL.match(L[ln - 1])
    return m.group(1) if m else f'?line{ln}'
got = {}
for m in seq:
    for f, ln, kind, msg in warns[m]:
        if kind == 'warning' and "declaration uses 'sorry'" in msg:
            tree = head if m.endswith('Build/ZoneRebalance') else base
            got.setdefault(m.replace('TCSlib/Complexity/', ''), []).append(declname(tree, f, ln))
exp = {}
for l in open(sorr_p, encoding='utf-8'):
    mm = re.match(r'^(\S+): (\d+): (.*)$', l.strip())
    if mm: exp[mm.group(1)] = [x.strip() for x in mm.group(3).split(',')]
def norm(n): return n.replace('_root_.', '').split('.')[-1]
tot = sum(len(v) for v in got.values())
print(f'sorry warnings in the sweep: {tot} in {len(got)} modules; base set: {sum(len(v) for v in exp.values())} in {len(exp)} modules')
ok = True
for mod in sorted(set(got) | set(exp)):
    g = sorted(norm(x) for x in got.get(mod, [])); e = sorted(norm(x.replace(' [private]', '')) for x in exp.get(mod, []))
    if g != e: ok = False; print('  DIFF', mod, 'sweep', g, 'base', e)
print('name-for-name equal to the base set:', ok)
print('ZoneRebalance sorry warnings:', [(f, ln) for f, ln, k, msg in warns.get('TCSlib/Complexity/TuringMachine/Build/ZoneRebalance', []) if 'sorry' in msg])
