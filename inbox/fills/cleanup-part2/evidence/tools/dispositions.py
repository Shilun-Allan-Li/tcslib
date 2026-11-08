#!/usr/bin/env python3
"""Per-row (764 historical rows) and per-key (509 canonical work keys) dispositions of the
cleanup-part2 J/N ledger, computed only from final evidence at one revision.

python3 -I dispositions.py <rev> <seal.json> <strict-seal.json|-> <explicit-scan.json> <c3.tsv>
                           <census axioms.tsv> <blocked.json|-> <out.json>

* seal channels (HIST_SEAL, GATE06_SEAL, GATE08_SEAL, S2_SEAL, G06_C2_SHOW): the key's declaration
  has (FAIL) / has no (PASS) error diagnostic in the whole-file seal of its file (standard variant;
  the strict variant is reported beside it when given);
* explicit channels (HIST_UNFOLD, G06_C1_TCS, G06_C1_CORE_MATHLIB, J_CORE_FUNCTION_COMP): the
  declaration has (OPEN) / has no (GONE) FOREIGN_TCS_DEF / CORE_MATHLIB_DEF item in its explicit
  simp/rw/unfold/dsimp/delta lists at the revision;
* C3 channels (HIST_EQN-TERM, G06_C3_EQN): the (module, root) pair with the recorded generated
  equation reference is present (OPEN) / absent (GONE) in the final C3 census.
A key whose declaration no longer exists in the final census of its module is REMOVED (the
old→new map names the replacement). Canonical names of failing declarations are resolved from
the source at the revision (namespace/section tracking, `_root_`, private prefix) and verified
against the census."""
import sys, json, re, subprocess, collections
rev, sealf, strictf, scanf, c3f, axf, blockedf, out = sys.argv[1:9]
CLONE = '/workspace/cp2/src'
PACK = '/workspace/tcslib/outbox/fills/cleanup-part2/inputs'
rows = json.load(open(f'{PACK}/historical/row-dispositions.json'))
keys = json.load(open(f'{PACK}/observations/canonical-work-units.json'))
seal = json.load(open(sealf))
strict = json.load(open(strictf)) if strictf != '-' else None
scan = json.load(open(scanf))['items']
blocked = json.load(open(blockedf)) if blockedf != '-' else {}
bidx = {(v['path'], v['decl_line']): v for v in blocked.values()}
census = collections.defaultdict(set)
for l in open(axf):
    p = l.rstrip('\n').split('\t')
    if p[0] != 'AXIOMS': continue
    n = p[2]; m = re.match(r'_private\.(.+?)\.0\.(.+)$', n)
    census[p[1]].add(m.group(2) if m else n)
c3 = set()
for l in open(c3f):
    p = l.rstrip('\n').split('\t')
    if p[0] != 'C3': continue
    r = p[2]; m = re.match(r'_private\.(.+?)\.0\.(.+)$', r)
    c3.add((p[1], m.group(2) if m else r, p[3]))
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*"
                  r"(theorem|lemma|def|instance|structure|inductive|abbrev|class|example|opaque|axiom)\b\s*([^\s(:{\[]*)")
_src = {}
def source(path):
    if path not in _src:
        _src[path] = subprocess.run(['git', '-C', CLONE, 'show', f'{rev}:{path}'], capture_output=True,
                                    text=True, check=True).stdout.split('\n')
    return _src[path]
_ns = {}
declline = {}
def decl_table(path):
    """[(line, spelling, canonical)] for every declaration start of the file at rev."""
    if path in _ns: return _ns[path]
    stack = []; out_ = []; depth = 0
    for i, l in enumerate(source(path)):
        s = l
        # block comments (docstrings) never start a command line we track
        if depth or s.lstrip().startswith('/-'):
            depth += s.count('/-') - s.count('-/'); depth = max(depth, 0); continue
        m = re.match(r'^namespace\s+(\S+)', s)
        if m: stack.append(('ns', m.group(1))); continue
        m = re.match(r'^(?:noncomputable\s+)?section(?:\s+(\S+))?\s*$', s)
        if m: stack.append(('sec', m.group(1) or '')); continue
        m = re.match(r'^end(?:\s+(\S+))?\s*$', s)
        if m and stack: stack.pop(); continue
        m = DECL.match(s)
        if m and m.group(2):
            nm = m.group(2)
            ns = '.'.join(x[1] for x in stack if x[0] == 'ns')
            can = nm[len('_root_.'):] if nm.startswith('_root_.') else (f'{ns}.{nm}' if ns else nm)
            out_.append((i + 1, nm, can))
    _ns[path] = out_
    return out_
def module(path): return path[:-len('.lean')].replace('/', '.')
def failing(sealres, path):
    """canonical names of declarations with an error diagnostic in the seal of path."""
    r = sealres.get(path[:-len('.lean')])
    if r is None: return None
    tab = decl_table(path)
    out_ = {}
    for d in r['diagnostics']:
        ln = d['decl_line_in_source']
        cand = [t for t in tab if t[0] == ln]
        can = cand[0][2] if cand else d['decl']
        out_.setdefault(can, []).append(f"{d['error_line_in_source']}: {d['message'][:100]}")
        declline[(path, can)] = ln
    return out_
def explicit_open(path, can):
    tab = decl_table(path)
    # map each item to its enclosing declaration by line
    res = []
    for it in scan:
        if it['file'] != path or it['class'] not in ('FOREIGN_TCS_DEF', 'CORE_MATHLIB_DEF', 'FOREIGN_TCS_DEF?AMBIGUOUS'):
            continue
        d = max((t for t in tab if t[0] <= it['line']), default=None)
        if d and d[2] == can: res.append(f"{it['line']} {it['tactic']} {it['ident']} ({it['class']})")
    return res
SEALCH = {'HIST_SEAL', 'GATE06_SEAL', 'GATE08_SEAL', 'S2_SEAL', 'G06_C2_SHOW'}
EXPCH = {'HIST_UNFOLD', 'G06_C1_TCS', 'G06_C1_CORE_MATHLIB', 'J_CORE_FUNCTION_COMP'}
C3CH = {'HIST_EQN-TERM', 'G06_C3_EQN'}
fcache = {}; scache = {}
def key_status(path, can, channels, other=True):
    mod = module(path)
    exists = can in census[mod]
    res = {'exists_at_final': exists}
    if not exists:
        homes = [m for m in census if can in census[m]]
        if len(homes) == 1:
            res['moved_to'] = homes[0]
            path = homes[0].replace('.', '/') + '.lean'; mod = homes[0]
        else:
            res['disposition'] = 'REMOVED_EXACT_MAPPING'
            return res
    if path not in fcache: fcache[path] = failing(seal, path)
    f = fcache[path]
    if strict is not None and path not in scache: scache[path] = failing(strict, path)
    st = {}
    if channels & SEALCH:
        if f is None: st['seal'] = 'NOT_MEASURED'
        else: st['seal'] = 'FAIL' if can in f else 'PASS'
        if st['seal'] == 'FAIL': res['seal_diagnostics'] = f[can]
        if strict is not None and scache.get(path) is not None:
            st['strict_seal'] = 'FAIL' if can in scache[path] else 'PASS'
    if channels & EXPCH:
        o = explicit_open(path, can)
        st['explicit'] = 'OPEN' if o else 'GONE'
        if o: res['explicit_items'] = o
    if channels & C3CH:
        refs = [(m, r, q) for (m, r, q) in c3 if m == mod and r == can]
        st['c3'] = 'OPEN' if refs else 'GONE'
        if refs: res['c3_refs'] = [q for _, _, q in refs]
    # any measured seal failure of a key declaration is open work regardless of channel
    if other and 'seal' not in st and f is not None and can in f:
        st['seal_other'] = 'FAIL'; res['seal_diagnostics'] = f[can]
    res['status'] = st
    bad = [k for k, v in st.items() if v in ('FAIL', 'OPEN') and k != 'strict_seal']
    if not bad: res['disposition'] = 'REPAIRED_VERIFIED_AT_FINAL'
    else:
        b = bidx.get((path, declline.get((path, can))))
        cls = b['class'] if b else 'OPEN_INCOMPLETE'
        if [k for k in bad if k != 'seal' and k != 'seal_other']: cls = 'OPEN_INCOMPLETE'
        res['disposition'] = cls
        if b: res['residual_class'] = b['class']
    return res
kout = []
for k in keys:
    chans = {o['channel'] for o in k['observations']}
    r = key_status(k['path'], k['canonical'], chans)
    kout.append({'path': k['path'], 'canonical': k['canonical'], 'channels': sorted(chans),
                 'observation_ids': [o['id'] for o in k['observations']], **r})
kidx = {(k['path'], k['canonical']): k for k in kout}
rout = []
CH = {'unfold': 'HIST_UNFOLD', 'seal': 'HIST_SEAL', 'eqn-term': 'HIST_EQN-TERM'}
for x in rows:
    path, can = x['post_s2_work_key']
    k = kidx.get((path, can))
    r = key_status(path, can, {CH[x['channel']]}, other=False)
    if k is not None: r['key_disposition'] = k['disposition']
    rout.append({'row': x['row'], 'channel': x['channel'], 'path': path, 'canonical': can,
                 'detail': x['detail'], 'input_row_disposition': x['row_disposition'],
                 'key_in_509_union': k is not None, **r})
summ = {'keys': dict(collections.Counter(k['disposition'] for k in kout)),
        'rows': dict(collections.Counter(r['disposition'] for r in rout)),
        'rows_by_channel': {c: dict(collections.Counter(r['disposition'] for r in rout if r['channel'] == c))
                            for c in ('unfold', 'seal', 'eqn-term')}}
# resolution check: every failing declaration's canonical name must be a census name of its module
unres = []
for path, f in fcache.items():
    for can in (f or {}):
        if can not in census[module(path)]: unres.append((path, can))
summ['unresolved_failing_names'] = len(unres)
json.dump({'revision': rev, 'unresolved_failing_names': unres, 'summary': summ, 'keys': kout, 'rows': rout}, open(out, 'w'), indent=1)
print(json.dumps(summ, indent=1))
