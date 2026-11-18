"""mkctl_regev.py <archived-tools-dir> <seals-dir> <worktree> <probe-subdir> <outdir>   [env CTL_ROWS=<rows.tsv>]

ORIGIN / ADAPTATIONS (tools-agent, sub-agent of fill ef-r23-regev, 2026-11-18). Modelled on
/home/user/ef-r23/tools/bb1m-tools/seal/review/mkctl_bb1m_readers.py (fill bb1-machine; lineage mkctl_bb1m.py <-
mkctl_pbdh.py <- mkctl_g40.py <- ... <- the nm-cca2 review mkctl.py). Kept VERBATIM: the archived harness
(build_seals.seal_command through request_payload_adapter.configure_builders, SEAL_CHUNK), `assemble` (imports,
options, sealed install / EOF verifier, start/end line bookkeeping), the covering-subset choice of seal records (per
target and per variant letter, the record with the fewest requests whose request set contains the target), the
ControlS_/ControlU_ labels and the controls-plan.json format read by ctlcheck2.py. Adaptations:
  (1) the hard-coded rows dict B is replaced by rows read from a TSV file (CTL_ROWS, default control-rows.tsv next
      to this script) so the lead can add series-3 rows without editing code; each TSV row gives one negative
      (`theorem <control> <binders> : type_of% (<reader>) := <neg>`, default neg `rfl`) and one positive
      (`theorem <control>Reader ... := <pos>`, default pos `<reader>`), the `trow`/`rrow` shape of the bb1m rows;
  (2) the control namespace is RegevControls (was PairingControls);
  (3) consistency checks: duplicate control names are refused; each target's `home` in the chosen record must
      equal the TSV owner column; targets covered by no record are listed as UNCOVERED (exit 3 when
      CTL_REQUIRE_ALL=1), so a row cannot silently drop out (the lineage only noted "rows whose target is in no
      sealed request set are not exercised");
  (4) writes coverage.tsv (target, variant, chosen label, owner module, requests) in <outdir>;
  (6) optional env CTL_OWNERS=<mod,mod,...> restricts the covering-subset candidates to those sealed owners (e.g. to
      force the series-1 controls into the Symmetric.Regev.Asymptotic probe instead of the smaller facade
      Encoding probe the rule would otherwise pick);
  (5) <probe-subdir> may be an absolute directory (pathlib: Path(wt)/abs == abs), so probes need not live inside
      the repository; the plan's `module` is then the absolute path without `.lean` (runner_regev.py runs
      `lean <module>.lean` from <worktree>, which accepts an absolute path).
Covering-subset rule (as in the lineage): a target is controlled in the probe of the sealed OWNER whose request set
(every ordinary TCSlib definition of its transitive import closure) contains it with the fewest requests, i.e. a
LATER CONSUMER of the target's module, where the target is foreign. Series-1 targets (Encoding.ModularArithmetic)
are thus controlled in a consumer such as Encryption.Symmetric.Regev.Asymptotic or the facade Encoding; series-2
targets in a consumer of Symmetric.Regev.Asymptotic (the facade Symmetric.Regev, or series 3's
PublicKey.Regev.Asymptotic) -- they are exercised only if such a consumer is among the sealed owners.
"""
import sys, json, importlib.util, os
from pathlib import Path
tools, sealdir, wt, sub, outdir = sys.argv[1:6]
sys.dont_write_bytecode = True
def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path); m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m); return m
bs = load(Path(tools) / 'build_seals.py', 'levin_bs'); controls = load(Path(tools) / 'build_controls.py', 'levin_controls')
adapter = load(Path(tools) / 'request_payload_adapter.py', 'levin_adapter'); adapter.configure_builders(bs, controls)
CHUNK = int(os.environ.get('SEAL_CHUNK', '0'))
if CHUNK:
    _orig = bs.seal_command
    def _chunked(label, rows, *, end):
        if len(rows) <= CHUNK: return _orig(label, rows, end=end)
        return b''.join(_orig(f'{label}_part{i // CHUNK + 1}', rows[i:i + CHUNK], end=end) for i in range(0, len(rows), CHUNK))
    bs.seal_command = _chunked

ROWS = os.environ.get('CTL_ROWS', str(Path(__file__).with_name('control-rows.tsv')))
COLS = ['target', 'owner', 'control', 'open', 'binders', 'reader', 'neg', 'pos', 'note']
def read_rows(path):
    B, owners, names = {}, {}, set()
    for ln, line in enumerate(open(path, encoding='utf-8'), 1):
        line = line.rstrip('\n')
        if not line.strip() or line.startswith('#'): continue
        f = line.split('\t')
        if f[0] == 'target': continue
        assert len(f) == len(COLS), f'{path}:{ln}: {len(f)} columns, expected {len(COLS)}'
        r = {k: ('' if v == '-' else v.replace('\\n', '\n')) for k, v in zip(COLS, f)}
        for k in ('target', 'owner', 'control', 'reader'):
            assert r[k], f'{path}:{ln}: empty {k}'
        for n in (r['control'], r['control'] + 'Reader'):
            assert n not in names, f'{path}:{ln}: duplicate control name {n}'; names.add(n)
        assert owners.setdefault(r['target'], r['owner']) == r['owner'], f'{path}:{ln}: owner differs for {r["target"]}'
        op = r['open'] + '\n' if r['open'] else ''
        bnd = (' ' + r['binders']) if r['binders'] else ''
        neg = r['neg'] or 'rfl'; pos = r['pos'] or r['reader']
        stmt = lambda n, p: f"theorem {n}{bnd} :\n    type_of% ({r['reader']}) :=\n  {p}\n"
        B.setdefault(r['target'], []).extend([
            (r['control'], True, op + stmt(r['control'], neg)),
            (r['control'] + 'Reader', False, op + stmt(r['control'] + 'Reader', pos))])
    return B, owners
B, OWNER = read_rows(ROWS)
assert B, f'no control rows in {ROWS}'
print('rows', ROWS, 'targets', len(B), 'controls', sum(len(v) for v in B.values()))

def assemble(label, module, rows, bodies, sealed):
    src = (f"import Lean\nimport {module}\n\nset_option maxHeartbeats 0\nset_option autoImplicit false\n"
           "set_option relaxedAutoImplicit false\n\n").encode()
    if sealed: src += bs.seal_command(label, rows, end=False)
    src += b"namespace RegevControls\n\n"
    expect = []
    for name, target, negative, body in bodies:
        start = src.count(b"\n") + 1
        src += body.encode() + b"\n"
        expect.append(dict(control=name, target=target, negative=negative, start_line=start,
                           end_line=start + body.count('\n') - 1))
    src += b"end RegevControls\n\n"
    if sealed: src += bs.seal_command(label, rows, end=True)
    return src, expect
out = Path(outdir); out.mkdir(parents=True, exist_ok=True); plan = []
recs = [json.load(open(p)) for p in sorted(Path(sealdir).glob('Seal*_*.json'))]
if os.environ.get('CTL_OWNERS'):  # optional: restrict the candidate consumers (comma-separated dotted modules)
    keep = set(os.environ['CTL_OWNERS'].split(',')); recs = [r for r in recs if r['module'] in keep]
    print('CTL_OWNERS restricts candidates to', sorted(keep))
assert recs, f'no seal records in {sealdir}'
chosen, cover, uncovered = {}, [], []
letters = sorted({r['label'].split('_')[0][-1] for r in recs})
for t in B:
    for letter in letters:
        c = [r for r in recs if r['label'].split('_')[0][-1] == letter and t in {x['spelling'] for x in r['rows']}]
        if c:
            r = min(c, key=lambda r: (len(r['rows']), r['label'])); chosen[r['label']] = r
            home = next(x['home'] for x in r['rows'] if x['spelling'] == t)
            assert home == OWNER[t], f'{t}: record home {home} differs from TSV owner {OWNER[t]}'
            cover.append((t, letter, r['label'], r['module'], len(r['rows'])))
        else:
            uncovered.append((t, letter)); cover.append((t, letter, 'UNCOVERED', '-', 0))
(out / 'coverage.tsv').write_text(''.join('\t'.join(map(str, x)) + '\n' for x in cover))
print('chosen', sorted(chosen))
for t, l in uncovered: print('UNCOVERED', l, t)
for rec in [chosen[k] for k in sorted(chosen)]:
    module = rec['module']; rows = rec['rows']
    have = {r['spelling'] for r in rows}
    bodies = [(n, t, neg, b) for t, lst in B.items() if t in have for (n, neg, b) in lst]
    for sealed in (True, False):
        lab = ('ControlS_' if sealed else 'ControlU_') + rec['label'][4:]  # keep the A/B letter of 'SealA_'/'SealB_'
        src, expect = assemble(lab, module, rows, bodies, sealed)
        p = Path(wt) / sub / (lab + '.lean'); p.parent.mkdir(parents=True, exist_ok=True); p.write_bytes(src)
        (out / (lab + '.lean.txt')).write_bytes(src)
        plan.append(dict(label=lab, module=f'{sub}/{lab}', owner=module, kind='own-seal', sealed=sealed,
                         requested=len(rows) if sealed else 0, controls=expect,
                         expected_errors=[e['start_line'] for e in expect if e['negative']] if sealed else []))
(out / 'controls-plan.json').write_text(json.dumps(plan, indent=1))
print(len(plan), 'control probes;', sum(len(p['expected_errors']) for p in plan), 'expected sealed failures;',
      len(uncovered), 'uncovered (target, variant)')
if uncovered and os.environ.get('CTL_REQUIRE_ALL') == '1': sys.exit(3)
