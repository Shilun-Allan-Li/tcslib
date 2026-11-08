"""Issue C1 wave 1's five briefs (maintainer tool; standard library only).

Usage:
  python3 -I issue.py plan
      check every source exists and every draft has only the issue-time placeholders left
  python3 -I issue.py apply <base-lean-short>
      write the briefs and copy their inputs into the campaign worktree (wt-hk); no commit
  python3 -I issue.py dispatch <inputs-commit-full>
      write exchange/outbox/fills/<brief>.md with @ANCESTOR@ filled; print SHA-256s
"""
import hashlib, os, re, shutil, sys

S = os.environ.get('TCSLIB_SCRATCH', os.path.expanduser('~/.tcslib-scratch'))
WT = f'{S}/wt-hk'
DR = f'{WT}/campaign/fills'  # wave 1's drafts were under audits/evidence/drafts before 2026-10-18
II = f'{DR}/issue-inputs'
PS = f'{S}/issue2/preship'
DISPATCH = os.path.join(os.environ.get('TCSLIB_REPO', os.path.expanduser('~/tcslib')), 'exchange/outbox/fills')

def pre_(b, names):
    return [f'{PS}/{b}/{n}.out' for n in names]

BRIEFS = []
for name, short, owned, files in [
    ('c1-fill-writer', 'w', None, ['C1WriterImportProbe.lean.txt', 'screen-population.txt']),
    ('c1-fill-window', 'wc', None, ['C1WindowImportProbe.lean.txt', 'screen-population.txt']),
    ('c1-fill-exhaustive', 'e', 'ExhaustiveReplayOverlay', ['ExhaustiveReplayOverlay.lean.txt', 'C1ExhaustiveImportProbe.lean.txt', 'screen-population.txt']),
    ('c1-fill-core', 'r', 'NDCodeSimulatorOverlay', ['NDCodeSimulatorOverlay.lean.txt', 'C1CoreImportProbe.lean.txt', 'screen-population.txt']),
    ('c1-fill-universal', 'un', 'NTimeHierarchyOverlay', ['NTimeHierarchyOverlay.lean.txt', 'C1UniversalImportProbe.lean.txt', 'screen-population.txt'])]:
    src = f'{DR}/{name}'
    probe = [f for f in files if f.endswith('ImportProbe.lean.txt')][0].replace('.lean.txt', '')
    pre = [probe] + ([owned] if owned else ['OwnedFile'])
    BRIEFS.append(dict(name=name, draft=name, logs=name, ev=f'audits/evidence/{name}',
        files={f: f'{src}/{f}' for f in files},
        order=f'{src}/{name}-order.txt', sorries=f'{src}/{name}-base-sorries.txt',
        screen=f'{src}/{name}-screen-base.txt', preship=pre_(short, pre)))

ALLOWED = {'⟨BASE-LEAN⟩'}

def sources(b):
    return list(b['files'].values()) + [b['order'], b['sorries'], b['screen']] + b['preship'] + [f"{DR}/{b['draft']}.DRAFT.md"]

def strip_banner(t):
    # drop a leading "> **DRAFT …" block quote, if any
    return re.sub(r'\n> \*\*DRAFT[^\n]*\n(?:>[^\n]*\n)*\n', '\n', t, count=1)

def plan():
    bad = 0
    for b in BRIEFS:
        miss = [p for p in sources(b) if not os.path.isfile(p)]
        t = open(f"{DR}/{b['draft']}.DRAFT.md", encoding='utf-8').read()
        ph = set(re.findall(r'⟨[A-Z][^⟩]*⟩', t)) - ALLOWED
        anc = t.count('@ANCESTOR@')
        print(f"{b['name']}: sources {len(sources(b)) - len(miss)}/{len(sources(b))}; "
              f"other placeholders {sorted(ph)}; @ANCESTOR@ x{anc}" + (f"; MISSING {miss}" if miss else ''))
        bad += len(miss) + len(ph) + (anc == 0)
    print('plan:', 'OK' if bad == 0 else f'{bad} problems')
    return bad

def apply(base):
    assert plan() == 0
    for b in BRIEFS:
        t = strip_banner(open(f"{DR}/{b['draft']}.DRAFT.md", encoding='utf-8').read())
        assert t.count('⟨BASE-LEAN⟩') <= 1
        t = t.replace('⟨BASE-LEAN⟩', f'`{base}`')
        assert not re.search(r'⟨[A-Z][^⟩]*⟩', t)
        open(f"{WT}/briefs/{b['name']}.md", 'w', encoding='utf-8').write(t)
        for dst, src in b['files'].items():
            d = f"{WT}/{b['ev']}/{dst}"; os.makedirs(os.path.dirname(d), exist_ok=True); shutil.copyfile(src, d)
        shutil.copyfile(b['order'], f"{WT}/briefs/orders/{b.get('order_name', b['name'])}.txt")
        shutil.copyfile(b['sorries'], f"{WT}/audits/logs/{b['logs']}-base-sorries.txt")
        shutil.copyfile(b['screen'], f"{WT}/audits/logs/{b['logs']}-screen-base.txt")
        with open(f"{WT}/audits/logs/{b['logs']}-preship.log", 'w', encoding='utf-8') as f:
            f.write(f"# {b['name']}: pre-ship elaborations against the post-#120 snapshot (oleans-lndnf), maintainer\n")
            for p in b['preship']:
                f.write(f"\n## {os.path.basename(p)}\n"); f.write(open(p, encoding='utf-8').read())
        print('applied', b['name'])

def dispatch(anc):
    assert re.fullmatch(r'[0-9a-f]{40}', anc)
    for b in BRIEFS:
        t = open(f"{WT}/briefs/{b['name']}.md", encoding='utf-8').read()
        assert '@ANCESTOR@' in t and not re.search(r'⟨[A-Z][^⟩]*⟩', t)
        out = f"{DISPATCH}/{b['name']}.md"
        open(out, 'w', encoding='utf-8').write(t.replace('@ANCESTOR@', anc))
        print(hashlib.sha256(open(out, 'rb').read()).hexdigest(), b['name'])

if __name__ == '__main__':
    cmd = sys.argv[1]
    if cmd == 'plan': sys.exit(1 if plan() else 0)
    elif cmd == 'apply': apply(sys.argv[2])
    elif cmd == 'dispatch': dispatch(sys.argv[2])
