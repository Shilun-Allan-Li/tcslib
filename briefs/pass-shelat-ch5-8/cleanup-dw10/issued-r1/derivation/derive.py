"""derive.py <repo> <base> <work> <outdir>: the DW-10 owner set and the reconciliation inputs.

Inputs (all read-only): origins.tsv (origins.py), idx/ (graph.py), the #248 ledger
(deferred-read-ledger-final-r1.json from the records' 11-final-read-ledger.zip), the efficiency
PROOF-DEPENDENCIES.json and the Levin provider-comparison.json. Writes owners.txt, list-only.txt,
facades.txt, ledger-historical.tsv, ledger-current.tsv, provider-pairs.tsv, order.txt, roots.txt,
base-sorries.txt, closures.txt, estimate.json."""
import sys, os, csv, json, re, collections
repo, base, work, out = sys.argv[1:5]
os.makedirs(out, exist_ok=True)
REC = f'{repo}/briefs/pass-shelat-ch5-8'

# ---------- static index at the base
decl_rows = [l.rstrip('\n').split('\t') for l in open(f'{work}/idx/decls.tsv')]
by_full = collections.defaultdict(set)          # full name -> {path}
defs_in = collections.Counter()                 # path -> number of `def`s (seal-request estimate)
ndecl = collections.Counter()
for path, line, kind, priv, full in decl_rows:
    by_full[full].add(path); ndecl[path] += 1
    if kind == 'def':
        defs_in[path] += 1
imps = {}
for l in open(f'{work}/idx/imports.tsv'):
    m, _, rest = l.rstrip('\n').partition('\t'); imps[m] = rest.split()
full_order = [l.strip() for l in open(f'{work}/idx/full-order.txt') if l.strip()]
pos = {m: i + 1 for i, m in enumerate(full_order)}
mod2path = lambda m: m.replace('.', '/') + '.lean'
path2mod = lambda p: p[:-5]
all_paths = {mod2path(m) for m in imps}

# ---------- origins and tiers
orig = {r['path']: r for r in csv.DictReader(open(f'{work}/origins.tsv'), delimiter='\t')}


def ps_label(lbl):
    if lbl.startswith('direct: Pass-shelat'):
        return True
    m = re.match(r'#(\d+) (\S+)', lbl)
    return bool(m) and 'pass-shelat' in m.group(2) and m.group(1) not in ('186', '280')


P0 = {'TCSlib/InformationTheory/Entropy.lean', 'TCSlib/InformationTheory/Extractors.lean'}
GARG = re.compile(r"^direct: (Garg Ch\. 1-3|Merge branch 'garg/)")
BGW_IT = re.compile(r'^direct: Add information theory and BGW')
EXCL_LABEL = re.compile(r'#(333|338|339) |#331 |#280 ')   # GSW statements/core/security, pairings, LWE/SIS


def ps_touches(p):
    t = orig[p]['touching_first_parent_commits']
    return [x for x in t.split(' | ') if x and ps_label(x.replace(' (M)', '').replace(' (R)', ''))]


# ---------- the #248 ledger, flattened
L = json.load(open(f'{work}/ledger/deferred-read-ledger-final-r1.json'))


def unpriv(name):
    m = re.match(r'_private\.(.+?)\.0\.(.+)$', name or '')
    return (m.group(2), m.group(1)) if m else (name, None)


def locate(name, hint_path):
    """base path(s) of a declaration full name; hint used when several files declare it."""
    n, privmod = unpriv(name)
    hits = set(by_full.get(n, ()))
    if not hits and n and n.startswith('TCSlib.'):
        hits = set(by_full.get(n, ()))
    if privmod:
        hp = mod2path(privmod)
        if hp in hits:
            return [hp], 'private-home'
    if hint_path in hits:
        return [hint_path], 'same-path'
    if len(hits) == 1:
        return sorted(hits), 'moved'
    if hits:
        return sorted(hits), 'ambiguous'
    return [], 'not-found'


hist = L['historical_delivery']['historical_rows']
key_status = {}
for k in L['issued_historical_keys']:
    for o in k['issued']['observations']:
        key_status[o['id']] = (k['current_status'], ','.join(k['current_observation_ids']))
with open(f'{out}/ledger-historical.tsv', 'w') as f:
    f.write('row\tchannel\tledger_path\tcanonical\tdetail\tdisposition_248\tkey_status_248\t'
            'linked_current_ids\tbase_path\tbase_match\n')
    for r in hist:
        paths, how = locate(r['canonical'], r['path'])
        ks = key_status.get(f"H:{r['row']}", ('', ''))
        f.write('\t'.join(map(str, [r['row'], r['channel'], r['path'], r['canonical'],
                                    r.get('detail', '').replace('\t', ' '), r['disposition'], ks[0], ks[1],
                                    ';'.join(paths), how])) + '\n')
cur = L['current_observations']
cur_rows = []
for o in cur:
    ch = o['channel']
    if ch == 'whole-file-seal':
        decl = (o.get('head_span') or {}).get('name') or ''
        line, what = o.get('head_line'), (o.get('head_error') or '').split('\n')[0][:160]
        provs = ','.join(sorted({p['head']['spelling'] for p in o.get('provider_pairs', []) if p.get('head')}))
    elif ch == 'explicit-source':
        h = o['head']; decl = h['owner']['name']; line = h['line']
        what = f"{h['tactic']} {h['item']} ({h['kind']})"; provs = h.get('provider') or ''
    else:
        decl, line, what, provs = o['name'], '', o['reference'], o['provider']
    # whole-file seal rows name the declaration relative to the file's namespaces: resolve by suffix
    paths, how = locate(decl, o['path'])
    if not paths and decl:
        cands = [fn for fn in by_full if fn.endswith('.' + decl) or fn == decl]
        cands = [c for c in cands if o['path'] in by_full[c]] or cands
        if len(cands) == 1:
            paths, how = sorted(by_full[cands[0]]), 'suffix'
    cur_rows.append((o['id'], ch, o['path'], decl, line, what, provs, o['disposition'],
                     ';'.join(paths), how))
with open(f'{out}/ledger-current.tsv', 'w') as f:
    f.write('id\tchannel\tpath_248\tdeclaration\tline_248\terror_or_item\tproviders\tdisposition_248\t'
            'base_path\tbase_match\n')
    for r in cur_rows:
        f.write('\t'.join(str(x).replace('\t', ' ').replace('\n', ' ') for x in r) + '\n')
cur_by_id = {r[0]: r for r in cur_rows}

# ---------- provider pairs (2026-11-10 rulings)
eff = json.load(open(f'{REC}/fills/efficiency/issued-r1/PROOF-DEPENDENCIES.json'))['named_api_ledger_overlap']
lev = json.load(open(f'{REC}/maintainer/proof-prerequisites-2026-11-10/provider-comparison.json'))['levin']
with open(f'{out}/provider-pairs.tsv', 'w') as f:
    f.write('set\tid\tdeclaration\thome_at_ruling\tbase_path\tbase_match\n')
    for x in eff:
        c = cur_by_id[x['id']]
        f.write(f"efficiency-72\t{x['id']}\t{x['name']}\t{x['home']}\t{c[8]}\t{c[9]}\n")
    for i, n in lev:
        c = cur_by_id[i]
        f.write(f"levin-52\t{i}\t{n}\t{c[2][:-5].replace('/', '.')}\t{c[8]}\t{c[9]}\n")
prov_paths = {cur_by_id[x['id']][8] for x in eff} | {cur_by_id[i][8] for i, _ in lev}

# ---------- named findings (SG-F07, SY-F07, C-F02)
NAMED = {
    'TCSlib/Complexity/TuringMachine/CodeSimulator.lean': 'C-F02',
    'TCSlib/Complexity/CircuitComplexity/Uniform.lean': 'SY-F07 (Uniform, 4 canonical-A failures)',
}

# ---------- record-named paths (ledger rows and pairs) at the base
rec_paths = collections.Counter()
for l in open(f'{out}/ledger-historical.tsv').readlines()[1:]:
    for p in l.rstrip('\n').split('\t')[8].split(';'):
        if p: rec_paths[p] += 1
for r in cur_rows:
    for p in r[8].split(';'):
        if p: rec_paths[p] += 1

# ---------- tiers
STAGE_HOMES = set()   # Stage 1/Stage 2 homes named in cleanup-stage1 closures.txt (CHANGED)
for l in open(f'{REC}/cleanup-stage1/issued-r1/closures.txt'):
    if l.startswith('CHANGED\t'):
        STAGE_HOMES.add(mod2path(l.rstrip('\n').split('\t')[3]))
PRIMARY = {l.split('\t')[0].strip() for l in
           open(f'{REC}/fills/cleanup-part2/issued-r1/inputs/primary-owner-files.txt') if l.strip()}
rows, considered = [], []
for p in sorted(all_paths):
    o = orig[p]; lbl = o['origin_label']
    if p == 'TCSlib.lean':
        continue
    reason = None
    if ps_label(lbl):
        tier = 'T1'; reason = 'created by ' + lbl
    elif p in P0:
        tier = 'T1'; reason = 'created by #183 cryptography/pass-shelat-ch5-8-p0 (P0, on main; arrived via #186)'
    elif (GARG.match(lbl) or BGW_IT.match(lbl)) and ps_touches(p):
        tier = 'T2'
        reason = ('adopted: ' + ('Garg concrete layer' if GARG.match(lbl) else 'InformationTheory (BGW)') +
                  '; changed by ' + ', '.join(sorted({(x.split()[0] if not x.startswith('direct:') else 'the 2026-10-28 direct commit') for x in ps_touches(p)})) +
                  ('; #248 ledger rows' if rec_paths[p] else '') + ('; #248 primary owner' if p in PRIMARY else '')
                  + ('; Stage 1 home' if p in STAGE_HOMES else ''))
    elif rec_paths[p] or p in prov_paths or p in NAMED:
        tier = 'LIST'
        why = []
        if rec_paths[p]: why.append(f'{rec_paths[p]} #248 ledger rows')
        if p in prov_paths: why.append('provider pairs')
        if p in NAMED: why.append(NAMED[p])
        reason = 'outside the campaign (' + lbl + '): ' + '; '.join(why)
    else:
        if p in PRIMARY or ps_touches(p):
            why = []
            if ps_touches(p):
                why.append('changed by ' + ', '.join(sorted({(x.split()[0] if not x.startswith('direct:') else 'the 2026-10-28 direct commit') for x in ps_touches(p)})))
            if p in PRIMARY:
                why.append('#248 primary owner')
            considered.append((p, 'EXCLUDED', '; '.join(why) + f'; origin {lbl}; no reconciled item at the base'))
        continue
    if EXCL_LABEL.match(lbl) and tier != 'LIST':
        continue
    rows.append((p, tier, reason))
owners = [r for r in rows if r[1] in ('T1', 'T2') and ndecl[r[0]] > 0]
facades = [r for r in rows if r[1] in ('T1', 'T2') and ndecl[r[0]] == 0]
listonly = [r for r in rows if r[1] == 'LIST']

# ---------- closures, order, roots, estimate
def up(m, acc):
    stack = [m]
    while stack:
        x = stack.pop()
        for y in imps.get(x, []):
            if y in imps and y not in acc:
                acc.add(y); stack.append(y)
    return acc


targets = [path2mod(r[0]).replace('/', '.') for r in owners + listonly]
need = set(targets)
for t in targets:
    up(t, need)
order = [m for m in full_order if m.replace('/', '.') in need]
missing = sorted(need - {m.replace('/', '.') for m in full_order})
order += [m.replace('.', '/') for m in missing]
open(f'{out}/order.txt', 'w').write('\n'.join(order) + '\n')
roots = sorted({i for m in order for i in imps[m.replace('/', '.')] if not i.startswith('TCSlib')})
open(f'{out}/roots.txt', 'w').write('\n'.join(r for r in roots if r.startswith('Mathlib')) + '\n')
nonml = [r for r in roots if not r.startswith('Mathlib')]
est = {}
for t in targets:
    clo = up(t, set()) | {t}
    est[t] = sum(defs_in[mod2path(c)] for c in clo)

sorries = collections.defaultdict(list)
for l in open(f'{work}/idx/sorries.tsv'):
    m, name, n = l.rstrip('\n').split('\t')
    if m in set(order):
        sorries[m].append(name)
with open(f'{out}/base-sorries.txt', 'w') as f:
    tot = 0
    for m in order:
        if m in sorries:
            f.write(f"{m}: {len(sorries[m])}: {', '.join(sorted(sorries[m]))}\n"); tot += len(sorries[m])
    f.write(f'TOTAL {tot}\n')


def emit(fn, rws, title, cols):
    with open(f'{out}/{fn}', 'w') as f:
        f.write(title)
        f.write('\t'.join(cols) + '\n')
        for p, tier, reason in rws:
            m = path2mod(p).replace('/', '.')
            f.write('\t'.join([p, tier, str(pos.get(path2mod(p), '-')), str(order.index(path2mod(p)) + 1) if path2mod(p) in order else '-',
                               str(ndecl[p]), str(defs_in[p]), str(est.get(m, 0)), str(rec_paths[p]),
                               reason]) + '\n')


cols = ['path', 'tier', 'pos_full_order', 'pos_order', 'decls', 'defs', 'est_seal_requests_A',
        'ledger_rows_at_base', 'derivation']
json.dump({'owners': len(owners), 'T1': sum(1 for r in owners if r[1] == 'T1'),
           'T2': sum(1 for r in owners if r[1] == 'T2'), 'facades': len(facades), 'list_only': len(listonly),
           'order': len(order), 'mathlib_roots': sum(1 for r in roots if r.startswith('Mathlib')),
           'non_mathlib_roots': nonml,
           'est_requests_owners_A': sum(est[path2mod(r[0]).replace('/', '.')] for r in owners),
           'est_requests_listonly_A': sum(est[path2mod(r[0]).replace('/', '.')] for r in listonly),
           'base_sorries': sum(len(v) for v in sorries.values()), 'base_sorry_modules': len(sorries)},
          open(f'{out}/estimate.json', 'w'), indent=1)
emit('owners.body.tsv', owners, '', cols)
emit('facades.body.tsv', facades, '', cols)
emit('list-only.body.tsv', listonly, '', cols)
emit('considered-excluded.body.tsv', considered, '', cols)
print(open(f'{out}/estimate.json').read())
