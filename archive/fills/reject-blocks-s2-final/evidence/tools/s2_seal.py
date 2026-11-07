#!/usr/bin/env python3
"""S2 Rule-10 whole-file seals (adapted from the Gate 08 round-2 `conservative-checks.py`).

For each owned module, at the fill HEAD and at the issue ancestor, a probe copy of the whole
file with the module's conservative import-closure seal (CLOSUREROW names of
`Probe/S2Collect.lean`) inserted after its `namespace`/`open` lines; the names are resolved
against the environment (numerical/hygienic components included), each seal's installed status
is verified, already-irreducible names are counted separately. Error lines are mapped to their
enclosing declarations; seal-command diagnostics are rejected as harness failures. Then the
anonymous-read controls (narrow and under the full HEAD RSA seal) and the repetition-matcher
control (pre-ship sources, verbatim). One Lean process at a time (scripts/lean_check_tree.sh).
Usage: python3 -I s2_seal.py  (from anywhere)"""
import json, os, re, subprocess, datetime, sys
F = '/workspace/tcslib-fill'; ANC = '31348fcf7dee32f84db1fc8f929d80653137995e'
E = '/workspace/s2-evidence'; P = F + '/Probe'
PRE = '/workspace/tcslib/outbox/fills/reject-blocks-s2/preship'
FILES = ['Concrete', 'DiscreteLog', 'ElGamal', 'RSA', 'Rabin']
env = dict(os.environ, TCSLIB_OLEANS='/workspace/s2-oleans', PATH=os.path.expanduser('~/.elan/bin') + ':' + os.environ['PATH'])
os.makedirs(E + '/seals', exist_ok=True)

def check(stem, source):
    path = f'{P}/{stem}.lean'
    open(path, 'w').write(source)
    open(f'{E}/seals/{stem}.source.txt', 'w').write(source)
    log = f'{E}/seals/{stem}.log'
    with open(log, 'w') as h:
        h.write('START ' + datetime.datetime.now(datetime.timezone.utc).isoformat() + '\n'); h.flush()
        pr = subprocess.Popen(['bash', 'scripts/lean_check_tree.sh', f'Probe/{stem}'],
                              cwd=F, env=env, stdout=h, stderr=subprocess.STDOUT)
        _, status, ru = os.wait4(pr.pid, 0)
        rc = os.waitstatus_to_exitcode(status)
        h.write('\nEND ' + datetime.datetime.now(datetime.timezone.utc).isoformat() +
                f' RC {rc} maxrss(child tree)={ru.ru_maxrss // 1024}MiB\n')
    print(stem, 'rc', rc, flush=True)
    return rc, open(log).read()

collected = open(f'{E}/logs/S2Collect.log').read()
names = {f: set() for f in FILES}
for mod, n in re.findall(r'CLOSUREROW TCSlib\.Cryptography\.Candidates\.(\w+) \| (\S+) \|', collected):
    names[mod].add(n)
sealrows = {f: set() for f in FILES}
for mod, n in re.findall(r'SEALROW TCSlib\.Cryptography\.Candidates\.(\w+) \| (\S+) \|', collected):
    sealrows[mod].add(n)
EXCL = {'Complexity.PolyExpr.eval', 'TCSlib.Cryptography.glNeed'}
excluded_reads = {}
for f in FILES:
    missing = sealrows[f] - names[f]
    excluded_reads[f] = sorted(missing & EXCL)
    assert not (missing - EXCL), (f, 'elaborated reads outside the conservative list', missing - EXCL)
touched = {k.split('.')[-1]: v for k, v in json.load(open(f'{E}/logs/touched.json')).items()}
blocks = json.load(open(f'{E}/logs/blocks-head.json'))
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec)\s+)*"
                  r"(theorem|lemma|def|instance|structure|inductive|abbrev|class|example)\s*([^\s(:{\[]*)")

def seal_block(ns):
    spellings = json.dumps(sorted(ns), ensure_ascii=False)
    return '''-- S2 import-closure seal (evidence probe), independent of stored-constant reads.
run_cmd do
  let env ← Lean.getEnv
  let mut catalog : Std.HashMap String (Array Lean.Name) := {}
  let mut active : Nat := 0
  let mut already : Nat := 0
  for (n, _) in env.constants.map₁.toList do
    let some mi := env.getModuleIdxFor? n | continue
    unless (`TCSlib).isPrefixOf env.header.moduleNames[mi.toNat]! do continue
    let ns := (catalog[n.toString]?).getD #[]
    catalog := catalog.insert n.toString (ns.push n)
  for spelling in (#''' + spellings + ''' : Array String) do
    let ns := (catalog[spelling]?).getD #[]
    unless ns.size == 1 do throwError "seal name not found or ambiguous: {spelling}"
    let n := ns[0]!
    let before ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
    if before == .irreducible then
      already := already + 1
    else
      let id := Lean.mkIdent n
      Lean.Elab.Command.elabCommand (← `(command| attribute [local irreducible] $id:ident))
      active := active + 1
    let status ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
    unless status == .irreducible do throwError "seal not installed: {n}"
  Lean.logInfo m!"S2-SEAL active={active} already={already}"
-- END S2 IMPORT-CLOSURE SEAL
'''

def sealed_source(text, ns):
    L = text.split('\n')
    i = next(k for k, l in enumerate(L) if l.startswith('namespace '))
    j = i + 1
    while j < len(L) and not L[j].strip(): j += 1
    ins = j if L[j].startswith('open ') else i
    L.insert(ins + 1, seal_block(ns))
    return '\n'.join(L)

def failing(source, text):
    L = source.split('\n')
    starts = [(i + 1, m.group(2)) for i, l in enumerate(L) if (m := DECL.match(l))]
    end = L.index('-- END S2 IMPORT-CLOSURE SEAL') + 1
    errs = [int(x) for x in re.findall(r'\.lean:(\d+):\d+: error', text)]
    assert all(e > end for e in errs), ('seal-command diagnostic', errs, end)
    out = []
    for e in errs:
        d = max((s for s in starts if s[0] <= e), default=(0, '?'))
        if d[1] not in [o['decl'] for o in out]: out.append({'decl': d[1], 'line': e, 'decl_line': d[0]})
    return out, len(errs)

results = {}
for f in FILES:
    ns = names[f]
    for side, rev in (('Head', 'fill/reject-blocks-s2'), ('Anc', ANC)):
        text = subprocess.run(['git', '-C', F, 'show', f'{rev}:TCSlib/Cryptography/Candidates/{f}.lean'],
                              capture_output=True, text=True, check=True).stdout
        src = sealed_source(text, ns)
        rc, log = check(f'S2Sealed{side}{f}', src)
        assert not re.search(r'unknownIdentifier|unexpected token|seal name not found|seal not installed', log), (f, side)
        cnt = re.findall(r'S2-SEAL active=(\d+) already=(\d+)', log)
        assert len(cnt) == 1 and sum(map(int, cnt[0])) == len(ns), (f, side, cnt, len(ns))
        fl, nerr = failing(src, log)
        results[f'{f}/{side}'] = {'candidates': len(ns), 'active': int(cnt[0][0]), 'already_irreducible': int(cnt[0][1]),
                                  'rc': rc, 'error_diagnostics': nerr, 'failing': fl}
# classification of head failures against the ancestor
classification = {}
for f in FILES:
    hf = {d['decl'] for d in results[f'{f}/Head']['failing']}
    af = {d['decl'] for d in results[f'{f}/Anc']['failing']}
    changed = {c['name'] for c in blocks[f]['changed']} | {c['name'] for c in blocks[f]['added']}
    classification[f] = {
        'head_failing': sorted(hf), 'ancestor_failing': sorted(af),
        'head_only': sorted(hf - af), 'ancestor_only': sorted(af - hf),
        'touched_failing': sorted(hf & (set(touched[f]) | changed)),
        'untouched_failing_code_identical': sorted(hf - changed)}
# controls
plain = ('import TCSlib.Cryptography.Candidates.Concrete\n'
         'example (w : List Bool) : TCSlib.Cryptography.Candidates.primeStr w = '
         '[decide (TCSlib.Cryptography.NumberTheory.listToNat w).Prime] := rfl\n')
sealed = plain.replace('example (w', 'attribute [local irreducible] TCSlib.Cryptography.Candidates.primeStr\nexample (w')
c = {}
c['anonymous_unsealed_rc'], _ = check('S2AnonUnsealed', plain)
c['anonymous_sealed_rc'], t = check('S2AnonSealed', sealed)
c['anonymous_sealed_errors'] = re.findall(r'\.lean:(\d+:\d+): error', t)
rsa_src = open(f'{E}/seals/S2SealedHeadRSA.source.txt').read().split('\n')
a = rsa_src.index('-- S2 import-closure seal (evidence probe), independent of stored-constant reads.')
b = rsa_src.index('-- END S2 IMPORT-CLOSURE SEAL') + 1
broad = '\n'.join(rsa_src[a:b]) + '\n'
bplain = plain.replace('Candidates.Concrete', 'Candidates.RSA')
imp, ex = bplain.split('\n', 1)
c['anonymous_broad_unsealed_rc'], _ = check('S2AnonBroadUnsealed', bplain)
c['anonymous_broad_sealed_rc'], t = check('S2AnonBroadSealed', imp + '\n' + broad + ex)
c['anonymous_broad_sealed_errors'] = re.findall(r'\.lean:(\d+:\d+): error', t)
c['primeStr_in_RSA_list'] = 'TCSlib.Cryptography.Candidates.primeStr' in names['RSA']
c['matcher_in_Concrete_list'] = 'Complexity.polyTimeComputable_iterateFind.match_1' in names['Concrete']
mu = open(f'{PRE}/MatcherUnsealed.source.txt').read(); ms = open(f'{PRE}/MatcherSealed.source.txt').read()
c['matcher_unsealed_rc'], _ = check('S2MatcherUnsealed', mu)
c['matcher_sealed_rc'], t = check('S2MatcherSealed', ms)
c['matcher_sealed_errors'] = re.findall(r'\.lean:(\d+:\d+): error', t)
summary = {'head': subprocess.check_output(['git', '-C', F, 'rev-parse', 'fill/reject-blocks-s2'], text=True).strip(),
           'ancestor': ANC, 'candidate_pairs': sum(len(v) for v in names.values()),
           'elaborated_rows': {f: len(sealrows[f]) for f in FILES},
           'elaborated_reads_in_documented_exclusions': excluded_reads,
           'exclusions': ['instances', 'reducible non-matchers', 'Complexity.PolyExpr.eval', 'TCSlib.Cryptography.glNeed'],
           'seal_results': results, 'classification': classification, 'controls': c,
           'base_seals_rerun': True}
json.dump(summary, open(f'{E}/logs/seal-summary.json', 'w'), indent=1)
print(json.dumps(classification, indent=1)); print(json.dumps(c, indent=1))
