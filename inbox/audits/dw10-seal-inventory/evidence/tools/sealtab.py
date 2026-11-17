# sealtab.py (dw10-seal-inventory, Claude lead, 2026-11-17; reads every <rundir>/results*.jsonl of the parallel workers): NEW, after sealsum.py (same error/line attribution: probe line ->
# source line through the record's source_to_probe_lines -> declaration span of touched-all.json). Writes the brief's
# evidence/seals.tsv (one row per owner and variant) and evidence/seal-decls.tsv (one row per failing declaration and
# variant), and seal-errors.jsonl (every error with its message). Usage:
#   python3 -I sealtab.py <evidence> <dedup.json>... -- <rundir> <out-prefix>
# Change (final): each error also records its column (`col`, Lean's 0-based codepoint column; the probe line equals the
# source line, so the column applies to the source), for the statement test of reconcile.py.
# Errors are counted in both forms: `^\S+\.lean:\d+:\d+: error[:(]` and the substring `error`. Install/EOF: every harness
# part (label or label_partN) must log `G06-SEAL label=<part> requested=R ... verified=R` and `G06-SEAL-END label=<part>
# requested=R verified=R` (requested = verified, summed over parts = the record's request count). Message class: the
# first line of the message with `...` spans replaced by `X` and digits by N, cut at 80 characters. Providers: the
# sealed definitions (request rows) named in the message (full spelling, or a dotted suffix of at least two components,
# or a last component unique among the rows), restricted first to the sealed definitions that the declaration's stored
# constants reference (collector type/value refs); `refs:` lists that referenced set when the message names none.
# Cascade: within one declaration and variant, every error after the first is marked cascade (attributed to the first).
import sys, json, re, os, collections
ev = sys.argv[1]; i = sys.argv.index('--'); dfiles = sys.argv[2:i]; rd, outp = sys.argv[i + 1:i + 3]
dedup = [x for f in dfiles for x in json.load(open(f))]
touched = json.load(open(os.path.join(ev, 'touched/touched-all.json')))['files']
res = {}
import glob as _g
for _f in sorted(_g.glob(os.path.join(rd, 'results*.jsonl'))):  # parallel workers (results-<tag>.jsonl)
    for l in open(_f):
        x = json.loads(l)
        if 'module' in x: res[x['module']] = x
roots = {}  # module -> list of ROOT
def load_roots(batch):
    if batch in roots: return
    roots[batch] = collections.defaultdict(list)
    for l in open(os.path.join(ev, 'collect', batch, 'runs/mods', f'DW10Probe_Collect_{batch}.log'), encoding='utf-8'):
        if l.startswith('ROOT '):
            r = json.loads(l[5:]); roots[batch][r['module']].append(r)
DIAG = re.compile(r'^(\S+\.lean):(\d+):(\d+): (error|warning|info)(?:\(([^)]*)\))?: ?(.*)$')
def parse(log):
    out, cur = [], None
    for line in log.split('\n'):
        m = DIAG.match(line)
        if m:
            cur = dict(line=int(m.group(2)), col=int(m.group(3)), sev=m.group(4), msg=m.group(6)); out.append(cur)
        elif cur is not None: cur['msg'] += '\n' + line
    return out
def mclass(msg):
    first = msg.strip().split('\n')[0] if msg.strip() else ''
    first = re.sub(r'`[^`]*`', 'X', first); first = re.sub(r'\d+', 'N', first)
    return first[:80].strip()
AUX = re.compile(r'\.(proof_\d+|match_\d+|eq_\d+|eq_def|eq_unfold|_unary|_binary|_sunfold|_unsafe_rec|splitter|_proof_\d+|_simp_\d+|_cstage\d|_lambda_\d+|_eq_\d+)$')
def userbase(n):
    n = re.sub(r'^_private\.[^ ]*?\.0\.', '', n) if n.startswith('_private.') else n
    while AUX.search(n): n = AUX.sub('', n)
    return n
seal_rows, decl_rows, errs_out = [], [], []
cache = {}
for d in dedup:
    rm = d['run_module']; r_ = res.get(rm)
    v = d['variant']; label_rec = None
    # the record of the probe actually run (its label and line map)
    run_variant = next(x for x in dedup if x['module'] == d['module'] and x['probe_module'] == rm)
    pre = 'SealB_' if run_variant['variant'].endswith('B') else 'SealA_'
    rp = os.path.join(ev, 'seals/records', run_variant['variant'], d['batch'], pre + d['module'].split('.', 1)[1].replace('.', '_') + '.json')
    rec = json.load(open(rp))
    if r_ is None:
        seal_rows.append([d['path'], d['tier'], d['agent'], v, str(d['requested']), 'NOT_RUN', '-', '-', '-', '-', '-', d['dedup_with'], d['probe_sha256'], '-']); continue
    lp = os.path.join(rd, 'mods', rm.replace('/', '_') + '.log')
    if lp not in cache: cache[lp] = open(lp, encoding='utf-8', errors='replace').read()
    log = cache[lp]
    n1 = len(re.findall(r'^\S+\.lean:\d+:\d+: error[:(]', log, re.M)); n2 = log.count('error')
    lab = rec['label']
    inst = re.findall(r'G06-SEAL label=(' + re.escape(lab) + r'(?:_part\d+)?) requested=(\d+) active=(\d+) already_irreducible=(\d+) verified=(\d+)', log)
    eof = re.findall(r'G06-SEAL-END label=(' + re.escape(lab) + r'(?:_part\d+)?) requested=(\d+) verified=(\d+)', log)
    req = rec['requested']
    inst_ok = bool(inst) and all(a[1] == a[4] for a in inst) and sum(int(a[1]) for a in inst) == req
    eof_ok = bool(eof) and all(a[1] == a[2] for a in eof) and sum(int(a[1]) for a in eof) == req
    instS = f"{'ok' if inst_ok else 'MISSING'}:{len(inst)}part:{sum(int(a[4]) for a in inst)}/{req}"
    eofS = f"{'ok' if eof_ok else 'MISSING'}:{len(eof)}part:{sum(int(a[2]) for a in eof)}/{req}"
    p2s = {x['probe_line']: x['source_line'] for x in rec['source_to_probe_lines']}
    decls = touched.get(d['path'], {}).get('declarations', [])
    load_roots(d['batch'])
    rnames = {x['name']['display'] for x in roots[d['batch']][d['module']]}
    refs_by_decl = collections.defaultdict(set)
    for x in roots[d['batch']][d['module']]:
        for t in x['type_refs'] + x['value_refs']: refs_by_decl[userbase(x['name']['display'])].add(t['display'])
    reqs = [x['spelling'] for x in rec['rows']]; reqset = set(reqs)
    last = collections.Counter(s.rsplit('.', 1)[-1] for s in reqs)
    def resolve_decl(static):
        if static in rnames: return static
        c = [n for n in rnames if userbase(n) == static or userbase(n).endswith('.' + static) or static.endswith('.' + userbase(n))]
        c = sorted({userbase(n) for n in c}, key=len)
        return c[0] if c else static
    def providers(msg, decl):
        refd = refs_by_decl.get(decl, set()) & reqset
        found = set()
        for s in (refd or reqset):
            parts = s.split('.')
            if s in msg: found.add(s); continue
            if len(parts) >= 3 and re.search(r'(?<![\w.])' + re.escape('.'.join(parts[-2:])) + r'(?![\w])', msg): found.add(s); continue
            if (refd or last[parts[-1]] == 1) and re.search(r'(?<![\w])' + re.escape('.' + parts[-1]) + r'(?![\w\'])|(?<![\w.])' + re.escape(parts[-1]) + r'(?![\w\'])', msg) and len(parts[-1]) > 2:
                found.add(s)
        return sorted(found), sorted(refd)
    perdecl = collections.OrderedDict()
    for e in parse(log):
        if e['sev'] != 'error': continue
        s = p2s.get(e['line'])
        dd = [x for x in decls if s and x['start'] <= s <= x['end']]
        static = dd[0]['name'] if dd else (f'<harness probe:{e["line"]}>' if s is None else f'<outside src:{s}>')
        name = resolve_decl(static) if dd else static
        pv, refd = providers(e['msg'], name)
        k = name; first = k not in perdecl
        perdecl.setdefault(k, []).append(dict(src=s, cls=mclass(e['msg']), prov=pv, refd=refd, static=static))
        errs_out.append(dict(path=d['path'], variant=v, run_module=rm, probe_line=e['line'], col=e['col'], source_line=s, declaration=name,
                             static_name=static, cascade=not first, message_class=mclass(e['msg']), providers=pv, referenced=refd, message=e['msg'][:4000]))
    for k, es in perdecl.items():
        f0 = es[0]
        prov = sorted({p for e in es for p in e['prov']})
        decl_rows.append([d['path'], k, v, str(len(es)), str(f0['src']), f0['cls'], ','.join(prov) if prov else ('refs:' + ','.join(f0['refd']) if f0['refd'] else '-'),
                          ';'.join(f"{e['src']}:{e['cls']}" for e in es[1:]) or '-', d['tier'], d['agent'], rm])
    seal_rows.append([d['path'], d['tier'], d['agent'], v, str(req), str(r_['rc']), str(n1), str(n2), instS, eofS,
                      ','.join(perdecl) or '-', d['dedup_with'], d['probe_sha256'], rm])
H1 = ['path', 'tier', 'agent', 'variant', 'requests', 'rc', 'errors', 'error_substr', 'install', 'eof', 'failing_declarations', 'dedup_with', 'probe_sha256', 'run_module']
H2 = ['path', 'declaration', 'variant', 'errors', 'first_error_source_line', 'message_class', 'providers', 'cascade_errors', 'tier', 'agent', 'run_module']
with open(outp + 'seals.tsv', 'w') as f: f.write('\t'.join(H1) + '\n' + ''.join('\t'.join(x) + '\n' for x in seal_rows))
with open(outp + 'seal-decls.tsv', 'w') as f: f.write('\t'.join(H2) + '\n' + ''.join('\t'.join(x) + '\n' for x in decl_rows))
with open(outp + 'seal-errors.jsonl', 'w') as f: f.write(''.join(json.dumps(x, ensure_ascii=False) + '\n' for x in errs_out))
c = collections.Counter(x[3] for x in seal_rows if x[5] not in ('NOT_RUN',) and x[6] != '0')
print('rows', len(seal_rows), 'failing owner-variants', dict(c), 'failing decl rows', len(decl_rows),
      'incomplete', sum(1 for x in seal_rows if x[5] != 'NOT_RUN' and ('MISSING' in x[8] or 'MISSING' in x[9])))
