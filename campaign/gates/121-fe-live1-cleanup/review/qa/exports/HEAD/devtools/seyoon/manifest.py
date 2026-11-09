"""Dry-run manifest for the campaign restructure (maintainer tool; standard library only).
Usage: python3 -I manifest.py <records worktree> <gate-dispatches dir> <out dir>
Writes manifest.tsv (old<TAB>new), unplaced.txt, and prints a summary. Moves nothing."""
import os, re, subprocess, sys, collections
wt, gd, out = sys.argv[1:4]
files = subprocess.run(['git', '-C', wt, 'ls-files'], capture_output=True, text=True, check=True).stdout.split('\n')
files = [f for f in files if f]
R = re.compile(r'-r\d+$')
def base(slug): return R.sub('', slug)

# gate keys and numbers from the dispatch folders' bundle names
gnum = {}
for d in sorted(os.listdir(gd)):
    m = re.match(r'(\d+)-', d)
    p = os.path.join(gd, d)
    if not (m and os.path.isdir(p)): continue
    for f in os.listdir(p):
        if f.endswith('-bundle.md'):
            k = base(f[:-len('-bundle.md')])
            gnum.setdefault(k, int(m.group(1)))
def gdir(k):
    return f'campaign/gates/{gnum[k]:02d}-{k}' if k in gnum else f'campaign/gates/{k}'

# fills: the brief names, grouped by their item prefix
briefs = sorted(f[len('briefs/'):-3] for f in files if re.fullmatch(r'briefs/[^/]+\.md', f))
def group(b):
    m = re.match(r'(.+?)-fill-', b)
    if m: return m.group(1)
    m = re.match(r'(zone-f1|routine-f[12]|retrofit|epoch\d|lib|s13d|s12)', b)
    return m.group(1) if m else b.split('-')[0]
STANDARDS = {'briefs/fill-environment-addendum.md', 'audits/TEMPLATE.md'}
mapping, unplaced = {}, []
GATEKEYS = set(gnum) | {re.sub(r'-r\d+$', '', m.group(1)) for f in files for m in [re.fullmatch(r'audits/([^/]+?)(?:-r\d+)?-(?:pack|findings|resolutions)(?:-addendum[^/]*)?\.md', f)] if m}
gate_keys = set()
TOPDOCS = {'backlog.md': 'campaign/backlog.md', 'arm-extensions-proposal.md': 'campaign/design/arm-extensions-proposal.md',
           'nomenclature-findings.md': 'campaign/gates/nomenclature/findings.md'}
for f in files:
    if f in STANDARDS:
        mapping[f] = 'campaign/standards/' + os.path.basename(f); continue
    if f in TOPDOCS:
        mapping[f] = TOPDOCS[f]; continue
    m = re.fullmatch(r'AroraBarakChapter[^/]*Plan\.md', f)
    if m:
        mapping[f] = 'campaign/design/plans/' + f; continue
    m = re.fullmatch(r'audits/([^/]+?)(-r\d+)?-(pack|findings|resolutions)(-addendum[^/]*)?\.md', f)
    if m:
        k = m.group(1); gate_keys.add(k)
        kind = m.group(3) + (m.group(2) or '') + (m.group(4) or '')
        mapping[f] = f'{gdir(k)}/{kind}.md'; continue
    m = re.fullmatch(r'audits/([^/]+?)(-r\d+)?-bundle\.md', f)
    if m:
        k = m.group(1); gate_keys.add(k)
        mapping[f] = f'{gdir(k)}/bundle{m.group(2) or ""}.md'; continue
    m = re.fullmatch(r'audits/([^/]+)-agent-reports/(.+)', f)
    if m:
        mapping[f] = f'campaign/fills/{m.group(1).replace("-fill", "")}/reports/{m.group(2)}'; continue
    m = re.fullmatch(r'briefs/orders/([^/]+)\.txt', f)
    if m:
        b = m.group(1); mapping[f] = f'campaign/fills/{group(b)}/orders/{b}.txt'; continue
    m = re.fullmatch(r'briefs/([^/]+)\.md', f)
    if m:
        b = m.group(1); mapping[f] = f'campaign/fills/{group(b)}/briefs/{b}.md'; continue
    m = re.fullmatch(r'briefs/(.+)', f)
    if m:
        unplaced.append(f); continue
    m = re.fullmatch(r'audits/logs/(.+)', f)
    if m:
        name = m.group(1)
        hit = max((b for b in briefs if name.startswith(b + '-') or name.startswith(b + '/')), key=len, default=None)
        if hit: mapping[f] = f'campaign/fills/{group(hit)}/logs/{name}'; continue
        gk = max((k for k in GATEKEYS if name.startswith(k + '-') or name.startswith(k + '/') or name.startswith(k + '.')), key=len, default=None)
        if gk: mapping[f] = f'{gdir(gk)}/logs/{name}'; continue
        fm = re.match(r'([^/]+?)-fill', name)
        if fm: mapping[f] = f'campaign/fills/{fm.group(1)}/logs/{name}'; continue
        mapping[f] = f'campaign/logs/{name}'; continue
    if f == 'audits/evidence/retrofit/copy-text-screen-v3.py':
        mapping[f] = 'scripts/copy-text-screen-v3.py'; continue
    m = re.fullmatch(r'audits/evidence/c1/fills/(.+)', f)
    if m:
        mapping[f] = f'campaign/fills/c1/reviews/{m.group(1)}'; continue
    m = re.fullmatch(r'audits/evidence/maintainer-tools/(.+)', f)
    if m:
        mapping[f] = f'devtools/seyoon/lean/{m.group(1)}'; continue
    m = re.fullmatch(r'audits/evidence/([^/]+)/(.+)', f)
    if m:
        t, rest = m.groups()
        if t == 'drafts' and rest.startswith(('issue-inputs/', 'issue-tools/')):
            mapping[f] = f'campaign/fills/_issue/{rest}'; continue
        if t == 'drafts' and rest.startswith(('mig12-fill/', 'mig12-api/')):
            mapping[f] = f'campaign/fills/mig12/drafts/{rest}'; continue
        if t == 'drafts':
            dm = re.match(r'([^/]+?)(\.DRAFT\.md|/.*)$', rest)
            if dm and dm.group(1) in briefs or (dm and re.match(r'.+-fill-', dm.group(1))):
                b = dm.group(1); mapping[f] = f'campaign/fills/{group(b)}/drafts/{rest}'; continue
            mapping[f] = f'campaign/fills/_drafts/{rest}'; continue
        if t in briefs or re.match(r'.+-fill-', t):
            mapping[f] = f'campaign/fills/{group(t)}/inputs/{t}/{rest}'; continue
        k = base(t[:-5] if t.endswith('-gate') else t)
        if k in gnum or k in GATEKEYS:
            mapping[f] = f'{gdir(k)}/evidence/{rest}'; continue
        fm = re.match(r'(.+?)-(fill|canon-cont\d+|cont\d+)', t)
        if fm:
            mapping[f] = f'campaign/fills/{fm.group(1)}/evidence/{t}/{rest}'; continue
        mapping[f] = f'campaign/items/{t}/{rest}'; continue
    m = re.fullmatch(r'audits/evidence/([^/]+)', f)
    if m:
        name = m.group(1); stem = re.sub(r'\.(patch|diff|txt|md)$', '', name)
        fm = re.match(r'(zone-f1|routine-f[12]|routine-infra|retrofit|s12-counter|s12-framed|s13d-g1|vhost-f1|12\.2c-t1|b1|ch[0-9]-p[0-9]+|d7)', stem)
        mapping[f] = f'campaign/fills/{fm.group(1)}/evidence/{name}' if fm else f'campaign/evidence/{name}'; continue
    m = re.fullmatch(r'audits/(programs|retrofit-inventory|epoch3-split-reports)/(.+)', f)
    if m:
        d = {'programs': 'campaign/programs', 'retrofit-inventory': 'campaign/items/retrofit/inventory',
             'epoch3-split-reports': 'campaign/fills/epoch3/reports/split'}[m.group(1)]
        mapping[f] = f'{d}/{m.group(2)}'; continue
    m = re.fullmatch(r'audits/(BUNDLES|duplication-ledger)\.md', f)
    if m:
        mapping[f] = f'campaign/{m.group(1)}.md'; continue
    m = re.fullmatch(r'audits/(.+?)-(record|kickoff|source-review|fill-kickoff|phase1-kickoff)\.md', f)
    if m:
        mapping[f] = f'campaign/items/{m.group(1).split("-")[0]}/{f[len("audits/"):]}'; continue
    m = re.fullmatch(r'audits/([^/]+)', f)
    if m:
        name = m.group(1)
        im = re.fullmatch(r'(.+?)-integration(-\d+)?\.md', name)
        if im: mapping[f] = f'campaign/fills/{group(im.group(1) + "-fill-x")}/integration/{name}'; continue
        unplaced.append(f); continue
    if f.startswith('audits/'):
        unplaced.append(f)
os.makedirs(out, exist_ok=True)
with open(f'{out}/manifest.tsv', 'w') as fh:
    for k in sorted(mapping): fh.write(f'{k}\t{mapping[k]}\n')
open(f'{out}/unplaced.txt', 'w').write('\n'.join(unplaced) + '\n')
c = collections.Counter(v.split('/')[1] + '/' + (v.split('/')[2] if v.count('/') > 2 else '') for v in mapping.values())
print('mapped', len(mapping), 'unplaced', len(unplaced))
for k, n in c.most_common(25): print(f'  {n:5d} {k}')
dst = collections.Counter(mapping.values()); dup = [d for d, n in dst.items() if n > 1]
print('destination collisions:', len(dup), dup[:5])
print('gate folders:', len({v.split('/')[2] for v in mapping.values() if v.startswith('campaign/gates/')}),
      'numbered:', len({v.split('/')[2] for v in mapping.values() if re.match(r'campaign/gates/\d', v)}))
print('evidence topics left generic:', sorted({v.split('/')[2] for v in mapping.values() if v.startswith('campaign/evidence/')}))
