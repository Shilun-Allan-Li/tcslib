# reconcile.py (dw10-seal-inventory, Claude lead, 2026-11-17): NEW. Builds inventory.tsv from the four input tables, the
# seal tables (seal-errors.jsonl, seals.tsv), the scan (scan/<batch>/explicit.json), eqrefs.tsv, the collectors and
# readers.json, by the brief's Reconciliation and Classification sections. Usage:
#   python3 -I reconcile.py <evidence> <pack> <repo> <base> <out-inventory.tsv> <out-summary.json>
# Matching (brief, "Matching by channel"):
#  provider test detail: when our side names no provider and the declaration references none (coercions and instances
#  elaborate away), the provider is not used to match; a ledger provider FinDist.instCoeFunForallReal matches a declaration
#  whose strict-A count exceeds its coe-A count (the coercion's signature).
#  seal   - SEAL ids: the declaration's strict-A errors at the base, one-to-one by normalized message class (first message
#           line, `…` -> X, digits -> N) and provider overlap (the ledger's providers against the providers named in the
#           message or referenced by the declaration); STILL_OPEN = matched and the declaration's strict-A error count equals
#           its number of ledger ids; CHANGED = still failing otherwise (count, class/provider, variant: now B-only/strict-only),
#           or moved/removed; FIXED_SINCE = no error in strict-A and coe-A (and none in B, else CHANGED "now B-only").
#           Historical seal rows: the linked SEAL ids' statuses when linked, else the recorded line count against strict-A.
#           Provider pairs: their SEAL id's status. Named findings: the per-declaration count in the stated variant.
#  unfold - C1 ids and historical unfold rows: the scan's foreign items of the declaration, one-to-one by resolved provider and
#           tactic (CHANGED when only the tactic differs).
#  eqn    - C3 ids and historical eqn-term rows: eqrefs.tsv by reference name (private prefix removed), CHANGED when only the
#           equation lemma differs for the same target.
# NEW rows: each failing declaration (any variant) with no seal item, each foreign scan item (subkinds semireducible,
# irreducible, instance; abbrev/reducible/projection items are notation and only counted) with no unfold item, each
# attributed eqref with no eqn item.
import sys, os, re, json, csv, glob, collections, subprocess
ev, pack, repo, base, outp, outs = sys.argv[1:7]
def tsv(p): return list(csv.DictReader((l for l in open(p, encoding='utf-8') if not l.startswith('#')), delimiter='\t'))
H = tsv(os.path.join(pack, 'ledger-historical.tsv')); C = tsv(os.path.join(pack, 'ledger-current.tsv'))
PP = tsv(os.path.join(pack, 'provider-pairs.tsv')); NF = tsv(os.path.join(pack, 'named-findings.tsv'))
batches = [l.rstrip('\n').split('\t') for l in open(os.path.join(ev, 'collect/batches.tsv'))][1:]
owner = {r[2]: dict(batch=r[0], module=r[1], tier=r[3], agent=r[4]) for r in batches}
mod2path = {r[1]: r[2] for r in batches}
AUX = re.compile(r'\.(proof_\d+|match_\d+|eq_\d+|eq_def|eq_unfold|_unary|_binary|_sunfold|_unsafe_rec|splitter|_proof_\d+|_simp_\d+|_cstage\d|_lambda_\d+|_eq_\d+)$')
def userbase(n):
    n = re.sub(r'^_private\.[^ ]*?\.0\.', '', n) if n.startswith('_private.') else n
    while AUX.search(n): n = AUX.sub('', n)
    return n
def mclass(msg):
    first = msg.strip().split('\n')[0] if msg.strip() else ''
    first = re.sub(r'`[^`]*`', 'X', first); first = re.sub(r'\d+', 'N', first)
    return first[:80].strip()
# collector: names, CAT homes
names = collections.defaultdict(set); cathome = {}; catinfo = {}
for b in sorted({r[0] for r in batches}):
    lp = os.path.join(ev, 'collect', b, 'runs/mods', f'DW10Probe_Collect_{b}.log')
    if not os.path.exists(lp): continue
    for l in open(lp, encoding='utf-8'):
        if l.startswith('ROOT '):
            r = json.loads(l[5:]); names[mod2path[r['module']]].add(userbase(r['name']['display']))
        elif l.startswith('CAT '):
            r = json.loads(l[4:]); cathome[r['name']['display']] = r['home']['display']; catinfo[r['name']['display']] = r
def resolve(path, n):
    if not n: return None
    u = userbase(n); S = names.get(path, set())
    if u in S: return u
    c = sorted([x for x in S if x.endswith('.' + u) or u.endswith('.' + x)], key=len)
    return c[0] if c else None
# seals
sealrows = collections.defaultdict(dict)  # path -> variant -> row
if os.path.exists(os.path.join(ev, 'seals.tsv')):
    for r in tsv(os.path.join(ev, 'seals.tsv')): sealrows[r['path']][r['variant']] = r
errs = collections.defaultdict(lambda: collections.defaultdict(list))  # (path, decl) -> variant -> [errors]
if os.path.exists(os.path.join(ev, 'seal-errors.jsonl')):
    for l in open(os.path.join(ev, 'seal-errors.jsonl'), encoding='utf-8'):
        e = json.loads(l); errs[(e['path'], e['declaration'])][e['variant']].append(e)
V = ['strict-A', 'strict-B', 'coe-A', 'coe-B']
def sealed(path): return path in sealrows and all(sealrows[path].get(v, {}).get('rc', 'NOT_RUN') != 'NOT_RUN' for v in V)
def counts(path, d): return {v: len(errs[(path, d)][v]) for v in V} if d else {v: 0 for v in V}
# scan
scan = collections.defaultdict(list); scanned = set(); notation_items = collections.Counter()
for f in glob.glob(os.path.join(ev, 'scan/b*/explicit.json')):
    b = f.split('/')[-2]
    for k, it in enumerate(json.load(open(f))['items']):
        scanned.add(it['file'])
        if it['classification'] != 'FOREIGN_TCSLIB_DEFINITION': continue
        if it['subkind'] in ('abbrev', 'reducible', 'projection'): notation_items[(it['file'], it['subkind'])] += 1; continue
        it = dict(it, decl=resolve(it['file'], it['declaration']) or it['declaration'], ev=f'evidence/scan/{b}/explicit.json#items[{k}]')
        scan[(it['file'], it['decl'])].append(it)
# eqrefs
eqr = collections.defaultdict(list)
if os.path.exists(os.path.join(ev, 'eqrefs.tsv')):
    for k, r in enumerate(tsv(os.path.join(ev, 'eqrefs.tsv'))):
        if r['attributed'] != 'yes': continue
        eqr[(r['path'], resolve(r['path'], r['declaration']) or r['declaration'])].append(dict(r, ev=f'evidence/eqrefs.tsv:{k + 2}'))
readers = json.load(open(os.path.join(ev, 'readers/readers.json'))) if os.path.exists(os.path.join(ev, 'readers/readers.json')) else {}
structs = json.load(open(os.path.join(ev, 'readers/readers-structs.json'))) if os.path.exists(os.path.join(ev, 'readers/readers-structs.json')) else {}
# statement spans
touched = json.load(open(os.path.join(ev, 'touched/touched-all.json')))['files']
srccache = {}
def stmt_end(path, d):
    decls = touched.get(path, {}).get('declarations', [])
    if path not in srccache: srccache[path] = subprocess.run(['git', '-C', repo, 'show', f'{base}:{path}'], capture_output=True, text=True).stdout.split('\n')
    L = srccache[path]
    for x in decls:
        if resolve(path, x['name']) == d or x['name'] == d:
            depth = 0
            for i in range(x['decl_line'] - 1, x['end']):
                t = re.sub(r'--.*', '', L[i])
                for k, ch in enumerate(t):
                    if ch in '([{⟨': depth += 1
                    elif ch in ')]}⟩': depth -= 1
                    elif depth == 0 and t.startswith(':=', k): return (x['decl_line'], i + 1)
                if depth == 0 and (re.search(r'(^|\s)where\b', t) and i >= x['decl_line']): return (x['decl_line'], i + 1)
                if i > x['decl_line'] - 1 and re.match(r'^\s*\|', t): return (x['decl_line'], i)
            return (x['decl_line'], x['end'])
    return None
LIST = {l.split('\t')[0] for l in open(os.path.join(pack, 'list-only.txt'), encoding='utf-8') if l.strip() and not l.startswith(('#', 'path\t'))}
def homepath(n):
    h = cathome.get(n); return (h.replace('.', '/') + '.lean') if h else None
# case lemmas that together cover every input (policy.md §1: `_of_lt`/`_of_le`, `_true`/`_false`, one per constructor)
CASES = {'zero', 'succ', 'nil', 'cons', 'true', 'false', 'of_lt', 'of_le', 'of_gt', 'of_ge', 'none', 'some', 'pos', 'neg', 'inl', 'inr', 'empty', 'singleton', 'append', 'one', 'pure', 'bind'}
def fixfor(prov):
    """(class, fix) for a read of definition prov."""
    if not prov: return ('STAGE2', 'reader to be identified (no provider named in the message; see seal-errors.jsonl)')
    allr = readers.get(prov, [])
    # published readers: the brief's forms (_eq/_def/_apply/_iff/_eq_def) and run/contract lemmas; other <P>_* lemmas are
    # listed as related only (for example polyTimeComputable_id is a closure lemma, not a reader of PolyTimeComputable)
    def isreader(t):
        last = t.rsplit('.', 1)[-1]; base = prov.rsplit('.', 1)[-1]; b2 = base[:1].lower() + base[1:]
        sfx = [last[len(b) + 1:] for b in (base, b2) if last.startswith(b + '_')]
        return any(x in ('eq', 'def', 'apply', 'iff', 'eq_def') or x.split('_')[0] in ('computes', 'run', 'runs', 'contract', 'spec', 'eval')
                   or x in structs.get(prov, []) or x in CASES for x in sfx)  # field equations (policy §1) and case lemmas
    rs = [x for x in allr if isreader(x[0])]
    hp = homepath(prov)
    rel = ('; related: ' + ', '.join(x[0] for x in allr[:3])) if allr and not rs else ''
    if rs: return ('STAGE2', f'use {rs[0][0]} ({rs[0][1].replace(".", "/")}.lean)')
    if hp in owner: return ('STAGE2', f'add {prov}_eq (or _iff/_apply) in {hp}' + rel)
    return ('STAGE2-PROVIDER-READER', f'provider {hp or "?"}: add {prov}_eq (or _iff/_apply) next to {prov}; no published reader found' + rel)
# Gate 11 (Levin, #286): the owner files #286 created or changed (derivation/origins.tsv touching commits).
GATE11 = {'TCSlib/Complexity/ClassP/BinaryArith/Unary.lean', 'TCSlib/Complexity/Randomized/Build/PairSplit.lean',
          'TCSlib/Complexity/Randomized/Primitives.lean', 'TCSlib/Complexity/Randomized/UnaryPolynomial.lean',
          'TCSlib/Complexity/TuringMachine/Build/WordTiming.lean', 'TCSlib/Cryptography/Asymptotic/UniversalPadding.lean',
          'TCSlib/Cryptography/Asymptotic/UniversalPadding/BinaryRoot.lean', 'TCSlib/Cryptography/Asymptotic/UniversalPadding/Machine.lean',
          'TCSlib/Cryptography/Asymptotic/UniversalPadding/Parameter.lean'}
def known(path, d):
    n = (d or '').rsplit('.', 1)[-1]
    if path.endswith('Build/ModuleHost.lean') and n in ('stop_step', 'stop_clean', 'clean_install', 'clean_emit', 'pad_seam', 'pad_apply', 'pad_run', 'host_seam', 'host_call'): return 'DW-9'
    if path.endswith('Build/IterateFindHost.lean'): return 'DW-9'
    if path.endswith('Build/IterateFind.lean') and n in ('computesFunInTime_find', 'polyTimeComputable_find'): return 'F-01'
    if path.endswith('Games/Probability.lean'): return 'BS-F06'
    if path.endswith('Asymptotic/Universal.lean'): return 'Gate 35; Gate 11'
    if path in GATE11: return 'Gate 11'
    return '-'
def classify_seal(path, d):
    c = counts(path, d)
    if c['coe-A'] > 0:
        e0 = errs[(path, d)]['coe-A'][0]; sp = stmt_end(path, d)
        if sp and e0['source_line'] and sp[0] <= e0['source_line'] <= sp[1]:
            return ('STATEMENT', 'yes', 'separate ruling: the statement reads ' + (','.join(e0['providers']) or 'a sealed definition'))
        prov = next((p for e in errs[(path, d)]['coe-A'] for p in e['providers']), None)
        cl, fx = fixfor(prov)
        return (cl, 'no', fx)
    if c['strict-A'] > 0: return ('STRICT-ONLY (notation, no fix)', 'no', 'none (notation)')
    if c['coe-B'] > 0: return ('SEAL-B-ONLY', 'no', 'separate ruling (PolyExpr.eval, DW-10)')
    if c['strict-B'] > 0: return ('STRICT-ONLY (notation, no fix)', 'no', 'none (notation)')
    return ('-', 'no', '-')
def classify_read(path, d, prov, line):
    sp = stmt_end(path, d)
    if sp and line and sp[0] <= int(line) <= sp[1]: return ('STATEMENT', 'yes', f'separate ruling: the statement reads {prov}')
    cl, fx = fixfor(prov); return (cl, 'no', fx)
OUT = []
def row(item_id, source, channel, path, d, record, status, change, cnt=None, scan_s='-', cls='-', stl='no', fix='-', pending='-', kr='-', evid='-'):
    tier = owner[path]['tier'] if path in owner else ('HANDED' if path in LIST else '-')
    c = cnt or {}
    OUT.append([item_id, source, channel, path or '-', tier, d or '-', record] + [str(c.get(v, '-')) for v in V] +
               [scan_s, status, change, cls, stl, fix, pending, kr, evid])
def seal_evidence(path, d):
    for v in ('coe-A', 'strict-A', 'coe-B', 'strict-B'):
        if errs[(path, d)][v]:
            e = errs[(path, d)][v][0]; return f"evidence/seals/runs/mods/{e['run_module'].replace('/', '_')}.log:{e['probe_line']}"
    r = sealrows.get(path, {}).get('coe-A')
    return f"evidence/seals/runs/mods/{r['run_module'].replace('/', '_')}.log" if r else '-'
used_seal = set(); used_scan = set(); used_eq = set()
# ---- current SEAL ids (needed first: historical rows and pairs use them)
seal_status = {}
bydecl = collections.defaultdict(list)
for r in C:
    if r['id'].startswith('SEAL') and r['scope'] == 'OWNER':
        bydecl[(r['base_path'], resolve(r['base_path'], r['declaration']))].append(r)
for (path, d), rs in bydecl.items():
    if not d or not sealed(path):
        for r in rs: seal_status[r['id']] = ('NOT_CHECKED' if not sealed(path) else 'CHANGED', 'declaration not found at the base (collector)' if not d else 'owner not yet sealed')
        continue
    c = counts(path, d); used_seal.add((path, d)); A = errs[(path, d)]['strict-A']
    free = list(range(len(A)))
    for r in sorted(rs, key=lambda r: int(r['line_248'] or 0)):
        cls = mclass(r['error_or_item']); lp = set(filter(None, r['providers'].split(',')))
        best = None
        for k in free:
            e = A[k]
            if e['cascade'] and False: continue
            okc = e['message_class'] == cls
            ours = set(e['providers']) | set(e.get('referenced', []))
            # provider test: unknown on our side (coercions and instances elaborate away from the stored term) -> not used;
            # the ledger's FinDist coercion provider matches a step that fails under strict and not under coe
            coe_sig = 'TCSlib.InformationTheory.FinDist.instCoeFunForallReal' in lp and c['strict-A'] > c['coe-A']
            okp = not lp or not ours or bool(lp & ours) or coe_sig
            if okc and okp: best = k; break
        mv = r['base_match'] == 'moved'
        if c['strict-A'] == 0 and c['coe-A'] == 0:
            if c['strict-B'] or c['coe-B']: seal_status[r['id']] = ('CHANGED', 'now B-only' + ('; moved' if mv else ''))
            else: seal_status[r['id']] = ('FIXED_SINCE', 'moved to the base path' if mv else '-')
        elif best is not None:
            free.remove(best)
            same = c['strict-A'] == len(rs)
            ch = [] if same else [f'count {len(rs)}->{c["strict-A"]} (strict-A)']
            if c['coe-A'] == 0: ch.append('now strict-only')
            if mv: ch.append('moved')
            seal_status[r['id']] = ('STILL_OPEN' if same and not mv else 'CHANGED', '; '.join(ch) or '-')
        else:
            seal_status[r['id']] = ('CHANGED', f'still fails ({c["strict-A"]} strict-A) with another message class or provider' + ('; moved' if mv else ''))
def seal_item(item_id, source, r, path, d, record, status, change, pend='-'):
    if status in ('FIXED_SINCE', 'HANDED-OFF', 'NOT_CHECKED') or not d: cl = ('-', 'no', '-')
    else: cl = classify_seal(path, d)
    row(item_id, source, 'seal', path, d, record, status, change, counts(path, d) if d else None, '-', cl[0], cl[1], cl[2],
        '#347' if known(path, d) == 'F-01' else pend, known(path, d), seal_evidence(path, d) if d else '-')
# ---- historical
for r in H:
    iid = f"H:{r['row']}"; path = r['base_path']; ch = r['channel']
    rec = f"{r['canonical']} ({r['detail']}; #248 {r['disposition_248']})"
    chn = {'seal': 'seal', 'unfold': 'unfold', 'eqn-term': 'eqn'}[ch]
    if r['scope'] == 'HANDED-OFF':
        row(iid, '#248-historical', chn, path, r['canonical'], rec, 'HANDED-OFF', '-'); continue
    if r['scope'] == 'NO-DECLARATION':
        row(iid, '#248-historical', chn, path, r['canonical'], rec, 'CHANGED', 'declaration removed: not found at the base (collector)'); continue
    if ';' in path:
        cands = [(p, resolve(p, r['canonical'])) for p in path.split(';')]
        cands = [x for x in cands if x[1]]; path, d = cands[0] if cands else (path.split(';')[0], None)
    else: d = resolve(path, r['canonical'])
    mv = r['base_match'] == 'moved'
    if not d:
        row(iid, '#248-historical', chn, path, r['canonical'], rec, 'CHANGED', 'declaration not found at the base (collector)'); continue
    if ch == 'seal':
        if not sealed(path): row(iid, '#248-historical', chn, path, d, rec, 'NOT_CHECKED', 'owner not yet sealed'); continue
        used_seal.add((path, d)); c = counts(path, d)
        linked = [x for x in r['linked_current_ids'].split(',') if x and x in seal_status]
        if not any(c.values()): st, chg = 'FIXED_SINCE', ('stayed fixed' if r['disposition_248'].startswith('REPAIRED') else '-') + ('; moved' if mv else '')
        elif c['strict-A'] == 0 and c['coe-A'] == 0: st, chg = 'CHANGED', 'now B-only'
        elif linked:
            sts = {seal_status[x][0] for x in linked}
            st = 'STILL_OPEN' if sts == {'STILL_OPEN'} else 'CHANGED'; chg = '-' if st == 'STILL_OPEN' else 'linked ids: ' + ','.join(f'{x}={seal_status[x][0]}' for x in linked)
        elif r['disposition_248'].startswith('REPAIRED'):
            st, chg = 'CHANGED', f'repaired row regressed ({c["strict-A"]} strict-A, {c["coe-A"]} coe-A)'
        else:
            n = len(re.findall(r'\d+', r['detail']))
            st, chg = ('STILL_OPEN', '-') if n == c['strict-A'] and not mv else ('CHANGED', f'count {n}->{c["strict-A"]} (strict-A)' + ('; moved' if mv else ''))
        seal_item(iid, '#248-historical', r, path, d, rec, st, chg)
    elif ch == 'unfold':
        m = re.match(r'(\d+)\s+(\S+)\s+(\S+)', r['detail']); tac, prov = (m.group(2), m.group(3)) if m else (None, None)
        if not sealed(path) and path not in scanned: row(iid, '#248-historical', chn, path, d, rec, 'NOT_CHECKED', 'owner not yet scanned'); continue
        its = [x for x in scan.get((path, d), []) if (path, d, id(x)) not in used_scan]
        hit = next((x for x in its if x['resolved'] == prov and x['tactic'] == tac), None) or next((x for x in its if x['resolved'] == prov), None)
        if hit is None: st, chg, sc = 'FIXED_SINCE', ('stayed fixed' if r['disposition_248'].startswith('REPAIRED') else '-'), '-'
        else:
            used_scan.add((path, d, id(hit))); sc = f"{hit['line']} {hit['tactic']} {hit['resolved']}"
            st = 'STILL_OPEN' if hit['tactic'] == tac and not r['disposition_248'].startswith('REPAIRED') and not mv else 'CHANGED'
            chg = '-' if st == 'STILL_OPEN' else ('; '.join(x for x in [('repaired row regressed' if r['disposition_248'].startswith('REPAIRED') else ''), (f'tactic {tac}->{hit["tactic"]}' if hit['tactic'] != tac else ''), ('moved' if mv else '')] if x))
        cl = classify_read(path, d, prov, hit['line'] if hit else None) if st not in ('FIXED_SINCE',) else ('-', 'no', '-')
        row(iid, '#248-historical', chn, path, d, rec, st, chg, None, sc, *cl, '-', known(path, d), hit['ev'] if hit else '-')
    else:
        ref = r['detail'].strip()
        its = eqr.get((path, d), [])
        hit = next((x for x in its if userbase(x['ref']) == userbase(ref) or re.sub(r'^_private\.[^ ]*?\.0\.', '', x['ref']) == ref), None)
        hit2 = hit or next((x for x in its if userbase(x['target']) == userbase(ref)), None)
        if hit2 is None: st, chg = 'FIXED_SINCE', ('stayed fixed' if r['disposition_248'].startswith('REPAIRED') else '-')
        else:
            used_eq.add(id(hit2)); st = 'STILL_OPEN' if hit and not r['disposition_248'].startswith('REPAIRED') and not mv else 'CHANGED'
            chg = '-' if st == 'STILL_OPEN' else ('repaired row regressed' if r['disposition_248'].startswith('REPAIRED') else ('reference ' + hit2['ref'] if not hit else 'moved'))
        cl = classify_read(path, d, hit2['target'], None) if hit2 else ('-', 'no', '-')
        row(iid, '#248-historical', chn, path, d, rec, st, chg, None, hit2['ref'] if hit2 else '-', *cl, '-', known(path, d), hit2['ev'] if hit2 else '-')
# ---- current
for r in C:
    iid = r['id']; path = r['base_path']; rec = f"{r['declaration']} l.{r['line_248']}: {r['error_or_item'][:120]} (#248 {r['disposition_248']})"
    chn = 'seal' if iid.startswith('SEAL') else ('unfold' if iid.startswith('C1') else 'eqn')
    if r['scope'] == 'HANDED-OFF': row(iid, '#248-current', chn, path, r['declaration'], rec, 'HANDED-OFF', '-'); continue
    if r['scope'] == 'NO-DECLARATION': row(iid, '#248-current', chn, path, r['declaration'], rec, 'CHANGED', 'declaration removed: not found at the base (collector)'); continue
    d = resolve(path, r['declaration']); mv = r['base_match'] == 'moved'
    if not d: row(iid, '#248-current', chn, path, r['declaration'], rec, 'CHANGED', 'declaration not found at the base (collector)'); continue
    if chn == 'seal':
        st, chg = seal_status.get(iid, ('NOT_CHECKED', 'owner not yet sealed')); seal_item(iid, '#248-current', r, path, d, rec, st, chg)
    elif chn == 'unfold':
        if path not in scanned: row(iid, '#248-current', chn, path, d, rec, 'NOT_CHECKED', 'owner not yet scanned'); continue
        m = re.match(r'(\S+)\s+(\S+)', r['error_or_item']); tac = m.group(1) if m else None; prov = r['providers']
        its = [x for x in scan.get((path, d), []) if (path, d, id(x)) not in used_scan]
        hit = next((x for x in its if x['resolved'] == prov and x['tactic'] == tac), None) or next((x for x in its if x['resolved'] == prov), None)
        if hit is None: st, chg, sc = 'FIXED_SINCE', '-', '-'
        else:
            used_scan.add((path, d, id(hit))); sc = f"{hit['line']} {hit['tactic']} {hit['resolved']}"
            st = 'STILL_OPEN' if hit['tactic'] == tac and not mv else 'CHANGED'
            chg = '-' if st == 'STILL_OPEN' else '; '.join(x for x in [(f'tactic {tac}->{hit["tactic"]}' if hit['tactic'] != tac else ''), ('moved' if mv else '')] if x)
        cl = classify_read(path, d, prov, hit['line'] if hit else None) if hit else ('-', 'no', '-')
        row(iid, '#248-current', chn, path, d, rec, st, chg, None, sc, *cl, '-', known(path, d), hit['ev'] if hit else '-')
    else:
        ref = r['error_or_item'].strip(); its = eqr.get((path, d), [])
        hit = next((x for x in its if x['ref'] == ref or userbase(x['ref']) == userbase(ref)), None)
        hit2 = hit or next((x for x in its if userbase(x['target']) == userbase(r['providers'])), None)
        if hit2 is None: st, chg = 'FIXED_SINCE', '-'
        else: used_eq.add(id(hit2)); st = 'STILL_OPEN' if hit and not mv else 'CHANGED'; chg = '-' if st == 'STILL_OPEN' else ('reference ' + hit2['ref'] if not hit else 'moved')
        cl = classify_read(path, d, hit2['target'], None) if hit2 else ('-', 'no', '-')
        row(iid, '#248-current', chn, path, d, rec, st, chg, None, hit2['ref'] if hit2 else '-', *cl, '-', known(path, d), hit2['ev'] if hit2 else '-')
# ---- provider pairs
for r in PP:
    iid = ('EFF72:' if r['set'].startswith('efficiency') else 'LEV52:') + r['id']; path = r['base_path']
    rec = f"{r['set']} pair {r['id']} {r['declaration']} (home at ruling {r['home_at_ruling']})"
    if r['scope'] == 'HANDED-OFF': row(iid, 'provider-pair', 'seal', path, r['declaration'], rec, 'HANDED-OFF', '-'); continue
    d = resolve(path, r['declaration']); st, chg = seal_status.get(r['id'], ('NOT_CHECKED', 'owner not yet sealed'))
    seal_item(iid, 'provider-pair', r, path, d, rec, st, f'status of {r["id"]}' + ('' if chg == '-' else '; ' + chg))
# ---- named findings
# rows recorded without a per-declaration count (SG-F07's PRFOut group): the first row of the group carries the file total
# `file total Ne/Md` for the group's declarations; the group is STILL_OPEN when our counts in the stated variant sum to N over
# M failing declarations (each row then notes the group comparison), else CHANGED.
nfgroups = []
for r in NF:
    if r['scope'] == 'OWNER' and not r['errors_at_record']:
        if nfgroups and nfgroups[-1]['path'] == r['base_path'] and nfgroups[-1]['open']: nfgroups[-1]['rows'].append(r)
        else:
            m = re.search(r'file total (\d+)e/(\d+)d', r['note'])
            nfgroups.append(dict(path=r['base_path'], rows=[r], total=(int(m.group(1)), int(m.group(2))) if m else None, open=True))
    elif nfgroups: nfgroups[-1]['open'] = False
nfgroup_of = {id(r): g for g in nfgroups for r in g['rows']}
nfc = collections.Counter()
for r in NF:
    nfc[r['finding']] += 1; iid = f"{r['finding']}:{nfc[r['finding']]}"; path = r['base_path']
    rec = f"{r['declaration']}: {r['errors_at_record'] or '?'} errors, variant {r['variant']} ({r['note'][:100]})"
    if r['scope'] == 'HANDED-OFF': row(iid, r['finding'], 'seal', path, r['declaration'], rec, 'HANDED-OFF', '-'); continue
    d = resolve(path, r['declaration'])
    if not d: row(iid, r['finding'], 'seal', path, r['declaration'], rec, 'CHANGED', 'declaration not found at the base (collector)'); continue
    if not sealed(path): row(iid, r['finding'], 'seal', path, d, rec, 'NOT_CHECKED', 'owner not yet sealed'); continue
    used_seal.add((path, d)); c = counts(path, d); want = int(r['errors_at_record'] or 0)
    if id(r) in nfgroup_of and nfgroup_of[id(r)]['total']:
        g = nfgroup_of[id(r)]; N, M = g['total']
        gc = [counts(path, resolve(path, x['declaration'])) for x in g['rows']]
        tot = sum(x['coe-B'] for x in gc); nd = sum(1 for x in gc if x['coe-B'] > 0)
        clean_a = all(x['coe-A'] == 0 and x['strict-A'] == 0 for x in gc) and all(x['strict-B'] == x['coe-B'] for x in gc)
        if not any(c.values()): st, chg = 'FIXED_SINCE', '-'
        elif tot == N and nd == M and clean_a: st, chg = 'STILL_OPEN', f'per-declaration count not recorded; group {N}e/{M}d recorded, {tot}e/{nd}d at the base (B, strict = coe)'
        else: st, chg = 'CHANGED', f'group {N}e/{M}d recorded, {tot}e/{nd}d at the base (coe-B); A {sum(x["coe-A"] for x in gc)} coe'
    elif r['variant'].startswith('B'):
        if not any(c.values()): st, chg = 'FIXED_SINCE', '-'
        elif c['coe-B'] == want and c['strict-B'] == want and c['coe-A'] == 0 and c['strict-A'] == 0: st, chg = 'STILL_OPEN', '-'
        else: st, chg = 'CHANGED', f'B {want}->{c["coe-B"]} coe/{c["strict-B"]} strict; A {c["coe-A"]} coe/{c["strict-A"]} strict'
    else:
        if not any(c.values()): st, chg = 'FIXED_SINCE', '-'
        elif all(c[v] == want for v in V): st, chg = 'STILL_OPEN', '-'
        else: st, chg = 'CHANGED', f'{want} -> ' + ', '.join(f'{v} {c[v]}' for v in V)
    seal_item(iid, r['finding'], r, path, d, rec, st, chg)
# ---- NEW
newn = 0
for (path, d), vv in sorted(errs.items(), key=lambda x: (x[0][0], str(x[0][1]))):
    if (path, d) in used_seal or path not in owner: continue
    c = counts(path, d)
    if not any(c.values()): continue
    newn += 1; cascades = sum(max(0, len(vv[v]) - 1) for v in ('coe-A',))
    e0 = next(vv[v][0] for v in ('coe-A', 'strict-A', 'coe-B', 'strict-B') if vv[v])
    rec = f"first error l.{e0['source_line']}: {e0['message_class']}" + (f"; providers {','.join(e0['providers'])}" if e0['providers'] else '')
    cl = classify_seal(path, d)
    row(f'NEW:{newn}', 'new', 'seal', path, d, rec, 'NEW', (f'{cascades} cascade error(s) after the first (coe-A)' if cascades else '-'),
        c, '-', cl[0], cl[1], cl[2], '#347' if known(path, d) == 'F-01' else '-', known(path, d), seal_evidence(path, d))
for (path, d), its in sorted(scan.items(), key=lambda x: (x[0][0], str(x[0][1]))):
    if path not in owner: continue
    for it in its:
        if (path, d, id(it)) in used_scan: continue
        newn += 1; cl = classify_read(path, d, it['resolved'], it['line'])
        kr = 'DW-9' if path.endswith('IterateFindHost.lean') else known(path, d)
        row(f'NEW:{newn}', 'new', 'unfold', path, d, f"{it['line']} {it['tactic']} {it['resolved']} ({it['subkind']})", 'NEW', '-', None,
            f"{it['line']} {it['tactic']} {it['resolved']}", cl[0], cl[1], cl[2], '-', kr, it['ev'])
for (path, d), its in sorted(eqr.items(), key=lambda x: (x[0][0], str(x[0][1]))):
    if path not in owner: continue
    for it in its:
        if id(it) in used_eq: continue
        newn += 1; cl = classify_read(path, d, it['target'], None)
        row(f'NEW:{newn}', 'new', 'eqn', path, d, f"{it['ref']} (target {it['target']}, {it['target_home']})", 'NEW', '-', None, it['ref'], cl[0], cl[1], cl[2], '-', known(path, d), it['ev'])
HD = ['item_id', 'source', 'channel', 'base_path', 'tier', 'declaration', 'record', 'strict_A', 'strict_B', 'coe_A', 'coe_B', 'scan', 'status',
      'change', 'class', 'statement_level', 'fix', 'pending', 'known_record', 'evidence']
with open(outp, 'w', encoding='utf-8') as f:
    f.write('\t'.join(HD) + '\n')
    for x in OUT: f.write('\t'.join(str(v).replace('\t', ' ').replace('\n', ' ') for v in x) + '\n')
summ = dict(rows=len(OUT), by_source_status={f'{k[0]}|{k[1]}': v for k, v in collections.Counter((x[1], x[12]) for x in OUT).items()},
            by_class={k: v for k, v in collections.Counter(x[14] for x in OUT).items()}, notation_scan_items=sum(notation_items.values()))
json.dump(summ, open(outs, 'w'), indent=1)
print(json.dumps(summ, indent=1))
