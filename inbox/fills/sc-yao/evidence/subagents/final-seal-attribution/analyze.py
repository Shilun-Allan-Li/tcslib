#!/usr/bin/env python3
"""Read only stored seal diagnostics; produce per-error attribution without running Lean."""
from pathlib import Path
import collections
import difflib
import hashlib
import json
import re
import runpy

ROOT = Path('/Users/seyoonr/.codex/worktrees/sc-yao/tcslib-exchange')
OUT = Path(__file__).resolve().parent
lex = runpy.run_path(str(ROOT / 'evidence/tools/header_lexer.py'))
current_path = ROOT / 'TCSlib/Cryptography/SecureComputation/Yao.lean'
current = current_path.read_text()
inputs = {}

def read(path):
    path = Path(path)
    raw = path.read_bytes()
    inputs[str(path.relative_to(ROOT))] = dict(bytes=len(raw), sha256=hashlib.sha256(raw).hexdigest())
    return raw.decode()

def rows(path):
    return [json.loads(s) for s in read(path).splitlines()]

def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

read(current_path)
final_rows = rows(ROOT / 'evidence/probe-runs/final-frozen-files-1/results.jsonl')
base_rows = rows(ROOT / 'evidence/probe-runs/checkpoint1-frozen-readers/results.jsonl')
eff_rows = rows(ROOT / 'evidence/probe-runs/yao-efficiency-repair-1/results.jsonl')
proto_rows = rows(ROOT / 'evidence/subagents/a12/probe-runs/concrete-final-audit-02/results.jsonl')
read(ROOT / 'evidence/efficiency-seal-summary.json')
read(ROOT / 'evidence/subagents/a12/B-ATTRIBUTION.json')
base = read(ROOT / 'evidence/headers/final-exact/Yao.base')
proto = read(ROOT / 'evidence/subagents/a12/probes/CompleteSimulators.lean')

ERROR = re.compile(r'^(\S+\.lean):(\d+):(\d+): (error(?::|\([^\n]*?\):))([^\n]*)', re.M)
MESSAGE = re.compile(r'^\S+\.lean:\d+:\d+: (?:error[:(]|warning:|info:)', re.M)

def diagnostics(row, expected_source):
    raw = read(ROOT / row['log'])
    snapshot = ROOT / row['log'].replace('.log', '.source.lean')
    sealed = read(snapshot)
    assert digest(snapshot) == row['source_sha256']
    probe = ROOT / row['probe']
    assert read(probe) == sealed
    ls = sealed.splitlines(keepends=True)
    original = ''.join(ls[:row['original_insert_line']] +
                       ls[row['original_insert_line'] + row['inserted_lines']:])
    assert original == expected_source, (snapshot, 'instrumentation removal mismatch')
    ds = lex['declarations'](original)
    boundaries = list(MESSAGE.finditer(raw))
    found = list(ERROR.finditer(raw))
    assert len(found) == row['errors']
    assert not re.search(r'^error[:(]', raw, re.M)
    result = []
    for index, match in enumerate(found, 1):
        end = next((m.start() for m in boundaries if m.start() > match.start()), len(raw))
        block = raw[match.start():end]
        block = re.split(r'^\s+\d+(?:\.\d+)? real\s+', block, flags=re.M)[0].rstrip()
        sealed_line, col = int(match.group(2)), int(match.group(3))
        line = sealed_line - row['inserted_lines']
        assert line > row['original_insert_line']
        offset = sum(len(s) + 1 for s in original.splitlines()[:line-1])
        decl = next(d for d in ds if d['start'] <= offset < d['end'])
        message = block.split(': '+match.group(4), 1)[1].lstrip()
        result.append(dict(index=index, sealed_line=sealed_line, column=col,
            source_line=line, declaration=decl['name'], source_line_text=original.splitlines()[line-1],
            full_excerpt=block, normalized_message=message))
    return result

def selected(rows_, coe, probe_prefix):
    matches = [r for r in rows_ if r.get('variant') == 'B' and r.get('coercions') == coe
               and r.get('probe', '').startswith(probe_prefix)]
    assert len(matches) == 1, (coe, probe_prefix, len(matches))
    return matches[0]

# The 15 original diagnostics survive at these final positions.
base_map = {i:i for i in range(1,12)} | {14:12, 15:13, 23:14, 24:15}
# Each old efficiency-only diagnostic is exactly the corresponding final one.
eff_map = {12:12, 13:13}
# Prototype has exactly the simulator header/body diagnostics, including two base headers.
proto_map = {i+13:i for i in range(1,10)}

reasons = {
1: ('base polynomial evaluation', 'The unchanged yaoCoins_eval rfl requires the polynomial coin expression to evaluate to 10*S(n)*n+2*S(n). B seals PolyExpr.eval and blocks that owner-local arithmetic reduction.'),
2: ('base call-index polynomial multiplication', 'The first yaoHybrid callA argument j has Fin ((Y.inB.mul var).eval n), whereas yaoCall expects Fin (Y.inB.eval n*n). Sealed polynomial evaluation blocks the definitional identification.'),
3: ('base call-index polynomial multiplication', 'The second yaoHybrid callA use of yaoCall has the same explicit mul-evaluation index mismatch; it is a separate diagnostic in the unchanged definition.'),
4: ('base call-index polynomial multiplication', 'The yaoHybrid callB use of yaoCall has the same explicit mul-evaluation index mismatch in the unchanged definition.'),
5: ('base public callA reader index', 'The unchanged yaoHybrid_callA reader passes product-index j into the protocol call domain ((yaoHybrid...).calls.eval n), which no longer reduces under the B eval seal.'),
6: ('base public callB reader index', 'The unchanged yaoHybrid_callB reader has the corresponding product-index/protocol-call-domain mismatch.'),
7: ('base answer reader callA index, first occurrence', 'The unchanged answersB getD proof calls callA with product-index j; the protocol call-count evaluation is opaque in B.'),
8: ('base answer reader callB index, first occurrence', 'The same unchanged answer-reader expression calls callB with product-index j; this is its separate call-domain mismatch.'),
9: ('base answer reader callA index, second occurrence', 'The later ofFn expression in the unchanged answer-reader proof again calls callA with product-index j, with the opaque polynomial call domain.'),
10: ('base answer reader callB index, second occurrence', 'The later ofFn expression separately calls callB with product-index j; the same eval multiplication reduction is blocked.'),
11: ('base good-seed PRF signature', 'The frozen yaoSeed_good_whp signature supplies G1 with Fin(n+n) output, while PRFOut (.add var var) asks for Fin ((var.add var).eval n). This existing signature depends on exempt polynomial notation.'),
12: ('existing efficiency-body callA index', 'CallEquations.inputA_eq ranges over Fin (Y.inB.eval n*n), while the goal ranges over Fin ((yaoHybrid...).calls.eval n). Its ordinary/canonical-A application uses the authorized polynomial-evaluation notation; this exact failure already appears in the efficiency audit.'),
13: ('existing efficiency-body callB index', 'CallEquations.inputB_eq has the same product-domain versus opaque calls.eval mismatch. This exact failure is the second efficiency-only diagnostic.'),
14: ('base simulator PRF signature', 'The frozen simulator G1 hypothesis has the same Fin(n+n) versus Fin ((var.add var).eval n) mismatch as the baseline; it is also prototype diagnostic1.'),
15: ('base simulator joint-PRF signature', 'The frozen simulator concatenation Fin.append has output length n+n+(var.add innerLen).eval n, whereas joint PRFOut expects the opaque outer add evaluation; this is baseline and prototype diagnostic2.'),
16: ('new direct factory circuit input-index mismatch', 'FakeSimulatorFactory is instantiated at inputs=.add Y.inA Y.inB. The actual circuit has DAGCircuit (Y.inA.eval n+Y.inB.eval n), while the sealed factory expects DAGCircuit ((Y.inA.add Y.inB).eval n). This is the first direct new body mismatch, corresponding to prototype diagnostic3.'),
17: ('new direct factory input-range index mismatch', 'The supplied Nat.le_refl proves A(n)+B(n)<=A(n)+B(n), while the factory expects A(n)+B(n)<=(Y.inA.add Y.inB).eval n. This is a second direct eval-add mismatch, prototype diagnostic4.'),
18: ('new dependent factory key-premise cascade', 'After diagnostic16 rejected the actual circuit family, the key obligation explicitly contains (sorry n).size and (sorry n q) rather than Y.circ/yaoSeed. The actual seed-key reader cannot close that poisoned dependent obligation. This is the matching prototype diagnostic5 cascade, not an independent unproved seed law.'),
19: ('new dependent factory first-nonce cascade', 'The nonce0 simp step is a premise of the same factory whose circuit family was rejected in diagnostic16. The supplied actual nonce reader no longer matches that dependent family. The exact same source line/message is prototype diagnostic6; canonical A checks this premise successfully.'),
20: ('new dependent factory second-nonce cascade', 'The nonce1 premise is the separate corresponding dependent-family simp failure after diagnostic16, matching prototype diagnostic7; canonical A checks the unchanged source successfully.'),
21: ('new dependent factory permutation cascade', 'The factory permutation premise uses the actual seed/permutation readers, but the factory family is poisoned by diagnostic16. This separate simp-no-progress cascade matches prototype diagnostic8 and disappears in canonical A.'),
22: ('new direct computational joint-family index mismatch', 'The GateHybridSecurity call supplies Fin.append G1 G2 at the exact joint polynomial L. B prevents reducing L.eval n to the explicit concatenation output length, so this body application fails just like prototype diagnostic9.'),
23: ('base HBC theorem PRF signature', 'The unchanged yaoHybrid_hbcSecure G1 hypothesis again requires n+n to identify with the opaque polynomial add evaluation. It is the penultimate baseline diagnostic.'),
24: ('base HBC theorem joint-PRF signature', 'The unchanged yaoHybrid_hbcSecure joint-family header has the same explicit concatenation length versus opaque nested-add evaluation mismatch as the last baseline diagnostic.')}

variants = {}
comparisons = {}
for coe in ['strict', 'coe']:
    fr = selected(final_rows, coe, 'evidence/seals/final-frozen-files/final/Yao_')
    br = selected(base_rows, coe, 'evidence/seals/frozen/base/Yao_')
    er = selected(eff_rows, coe, 'evidence/seals/yao-efficiency-repair/final/Yao_')
    pr = selected(proto_rows, coe, 'evidence/subagents/a12/seals/final-owner-fixed/CompleteSimulators_')
    fd, bd, ed, pd = diagnostics(fr,current), diagnostics(br,base), diagnostics(er,
        ''.join((ROOT / er['log'].replace('.log','.source.lean')).read_text().splitlines(keepends=True)[:10] +
                (ROOT / er['log'].replace('.log','.source.lean')).read_text().splitlines(keepends=True)[52:])), diagnostics(pr,proto)
    assert len(fd)==24 and len(bd)==15 and len(ed)==17 and len(pd)==9
    matches = []
    for d in fd:
        idx = d['index']
        category, why = reasons[idx]
        d.update(category=category, attribution=why,
            causal_classification='dependent-elaboration cascade (inference)' if idx in [18,19,20,21] else 'direct diagnostic',
            origin='base' if idx in base_map else 'efficiency' if idx in eff_map else 'new simulator body',
            comparators=[])
        for kind, mapping, previous, rr in [('base',base_map,bd,br),('efficiency',eff_map,ed,er),('a12',proto_map,pd,pr)]:
            if idx in mapping:
                other=previous[mapping[idx]-1]
                # The error bodies are compared individually, not just their counts.
                equal=d['normalized_message']==other['normalized_message']
                assert equal, (coe,idx,kind,'diagnostic text differs')
                if kind=='a12':
                    assert d['source_line_text']==other['source_line_text'],(coe,idx,'prototype source differs')
                d['comparators'].append(dict(kind=kind,index=other['index'],log=rr['log'],
                    sealed_line=other['sealed_line'],source_line=other['source_line'],
                    declaration=other['declaration'],normalized_message_identical=equal,
                    source_line_text=other['source_line_text'],full_excerpt=other['full_excerpt']))
        matches.append(dict(final_index=idx,comparators=[dict(kind=x['kind'],index=x['index']) for x in d['comparators']]))
    variants[coe]=dict(row=fr,errors=fd,counts=dict(total=24,base=15,efficiency=2,new_body=7,
        new_direct_eval_index=3,new_dependent_cascade=4),failing_declarations=dict(collections.Counter(d['declaration'] for d in fd)))
    comparisons[coe]=matches

strict, coe = variants['strict']['errors'], variants['coe']['errors']
assert [(d['sealed_line'],d['column'],d['declaration'],d['normalized_message']) for d in strict] == [(d['sealed_line'],d['column'],d['declaration'],d['normalized_message']) for d in coe]
# Confirm canonical A uses exactly the same original source and has no diagnostics.
canonical=[]
for rr in final_rows:
    if rr.get('file','').endswith('/Yao.lean') and rr['variant']=='A':
        assert rr['exit']==rr['errors']==rr['generic_errors']==0 and rr['fresh_olean']
        assert diagnostics(rr,current)==[]
        canonical.append(rr)
assert len(canonical)==2

instrumentation=[]
for rr in canonical:
    a=read(ROOT / rr['probe'])
    b_row=variants[rr['coercions']]['row']
    b=read(ROOT / b_row['probe'])
    diff=list(difflib.unified_diff(a.splitlines(),b.splitlines(),fromfile=rr['probe'],tofile=b_row['probe'],lineterm=''))
    changed=[line for line in diff if line.startswith(('+','-')) and not line.startswith(('+++','---'))]
    assert len(changed)==2 and all('PolyExpr.eval' in line for line in changed)
    instrumentation.append('\n'.join(diff))

report=dict(scope='Final actual Yao full-file B seals; no Lean execution by this reviewer',
    current_source_sha256=digest(current_path),current_lines=len(current.splitlines()),
    base_source_sha256=hashlib.sha256(base.encode()).hexdigest(),canonical_A=canonical,
    strict_coe_diagnostic_difference=[],strict_coe_diagnostics_identical=True,
    variants=variants,input_hashes=inputs)
(OUT/'ATTRIBUTION.json').write_text(json.dumps(report,indent=2,ensure_ascii=False)+'\n')
(OUT/'INPUT-HASHES.json').write_text(json.dumps(inputs,indent=2,ensure_ascii=False)+'\n')
(OUT/'INSTRUMENTATION-DIFF.md').write_text('# Canonical A versus diagnostic B instrumentation\n\nBoth variants reconstruct exactly the same current Yao source. Their only instrumentation\nchange below switches the `PolyExpr.eval` notation exemption off. No proof source differs.\n\n'+ '\n\n'.join('```diff\n'+s+'\n```' for s in instrumentation)+'\n')
md=['# Individual final Yao B diagnostics','',
    'Each row below occurs independently in **strict** and **coe**, at the same line/column with byte-identical normalized error text. Both canonical A variants pass. B deliberately seals the Q1-exempt `PolyExpr.eval`; these B failures are reported as failures, not passes.','',
    '| # | Original line | Sealed line | Declaration | Origin | Individual attribution |',
    '|---|---:|---:|---|---|---|']
for d in strict:
    md.append(f"| {d['index']} | {d['source_line']} | {d['sealed_line']} | `{d['declaration']}` | {d['origin']} | {d['attribution']} |")
md += ['', 'Per variant: **24 = 15 baseline + 2 efficiency + 7 new simulator body**. The seven new body errors are three direct polynomial-index mismatches and four dependent factory-premise cascades. Prototype B9 includes the simulator header\'s two baseline errors, so those two must not be added a second time.', '',
    'The four cascade classifications are causal inferences from the rejected factory circuit family, the poisoned `(sorry n)` key goal, the shared dependent factory premises, exact prototype matches, and the one-flag A/B instrumentation difference. They are distinguished from the three direct new index mismatches.','',
    'Failing-declaration multiplicities: '+', '.join(f'`{k}` {v}' for k,v in variants['strict']['failing_declarations'].items())+'.','',
    'Every baseline/efficiency/prototype comparator was checked individually for identical normalized diagnostic text; prototype rows also have identical source lines. `ATTRIBUTION.json` contains all48 full final excerpts, full comparator excerpts and exact input hashes. No strict-only/coercion-only difference remains.','',
    'This review reads stored outputs only. It does not rerun Lean, replace the lead\'s broader Rule10/axiom checks, or alter the source/frozen signatures. The original source is1152 lines, SHA256 `'+digest(current_path)+'`.']
(OUT/'REPORT-fragment.md').write_text('\n'.join(md)+'\n')
excerpts=['# Full final Yao B excerpts','']
for mode in ['strict','coe']:
    for d in variants[mode]['errors']:
        excerpts += [f"## {mode} · error {d['index']} · {d['declaration']} · original line {d['source_line']}", '', '```text',d['full_excerpt'],'```','']
(OUT/'FULL-EXCERPTS.md').write_text('\n'.join(excerpts))
manifest=[]
for path in sorted(OUT.iterdir()):
    if path.is_file() and path.name!='SHA256SUMS':
        manifest.append(digest(path)+'  '+path.name)
(OUT/'SHA256SUMS').write_text('\n'.join(manifest)+'\n')
for line in manifest:
    h,n=line.split(None,1);assert digest(OUT/n)==h
print(json.dumps(dict(report=str(OUT/'REPORT-fragment.md'),files=len(manifest),report_sha256=digest(OUT/'REPORT-fragment.md'),manifest_sha256=digest(OUT/'SHA256SUMS'),strict_errors=24,coe_errors=24,strict_coe_diagnostics_identical=True)))
