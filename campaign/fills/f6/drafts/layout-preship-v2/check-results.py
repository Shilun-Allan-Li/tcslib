"""Offline receipt/control verification only. Does not invoke Lean or mutate source."""
from pathlib import Path
import collections
import datetime
import hashlib
import json
import re

OUT = Path(__file__).resolve().parent
CTX = json.loads((OUT / 'context.json').read_text())
ERROR = re.compile(r'^(.+\.lean):(\d+):(\d+): error(?:\(([^)]*)\))?: (.*)$', re.M)
FINALS = ['Final-native', 'Final-return', 'Final-layout', 'Final-bundle',
          'Final-zero-outer', 'Final-correction']
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def errors(text):
    return [dict(line=int(m[2]), column=int(m[3]), code=m[4], message=m[5])
            for m in ERROR.finditer(text)]


def negative_ok(source, diagnostics, status):
    starts = [i for i, line in enumerate(source.splitlines(), 1)
              if re.match(r'^example(?:\s|:)', line)]
    ends = starts[1:] + [len(source.splitlines()) + 1]
    counts = [0] * len(starts)
    if status != 1 or len(diagnostics) != len(starts):
        return False
    for d in diagnostics:
        if d['code'] is not None or not d['message'].startswith('Tactic `rfl` failed:'):
            return False
        owners = [i for i, (lo, hi) in enumerate(zip(starts, ends))
                  if lo <= d['line'] < hi]
        if len(owners) != 1:
            return False
        counts[owners[0]] += 1
    return all(n == 1 for n in counts)


rows = []
for receipt in sorted(OUT.glob('*-run.json')):
    name = receipt.name.removesuffix('-run.json')
    run = json.loads(receipt.read_text())
    req = json.loads((OUT / (name + '-request.json')).read_text())
    text = (OUT / (name + '.out')).read_text()
    assert all(run[k] == v for k, v in req.items()), name
    assert sha(OUT / (name + '.lean.txt')) == run['input_sha256'], name
    assert sha(OUT / (name + '.out')) == run['output_sha256'], name
    copied = Path(run['command'][-1])
    assert copied.exists() and sha(copied) == run['input_sha256'], name
    assert run['local_slots'] == '3' and run['plain_managed'] and run['no_outer_lock'], name
    assert run['command'][0] == 'bash' and run['command'][1].endswith('/devtools/seyoon/leanelab.sh')
    assert run['command'][2:4] == [CTX['worktree'], CTX['snapshot']], name
    actual = len(errors(text))
    counter_note = None
    if actual != run['errors']:
        assert name == 'Native-startup-v1' and (actual, run['errors']) == (4, 3)
        counter_note = 'Original runner omitted coded unknownIdentifier diagnostic; raw count is 4. Original receipt preserved.'
    rows.append(dict(name=name, exit=run['exit'], raw_errors=actual,
                     recorded_errors=run['errors'], warnings=len(re.findall(r'^.*:\d+:\d+: warning:', text, re.M)),
                     counter_note=counter_note))

final_axioms = {}
guard = (OUT / 'final-guard.txt').read_text()
for name in FINALS:
    run = json.loads((OUT / (name + '-run.json')).read_text())
    text = (OUT / (name + '.out')).read_text()
    src = (OUT / (name + '.lean.txt')).read_text()
    assert run['exit'] == 0 and not errors(text) and 'warning:' not in text, name
    assert not re.search(r'\b(sorry|admit|axiom)\b', src), name
    assert src.index(guard) < src.index('namespace F6LayoutPreship') < src.index('theorem '), name
    ax = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text)
    assert ax and 'sorryAx' not in text, name
    for decl, axioms in ax:
        used = {a.strip() for a in axioms.split(',') if a.strip()}
        assert used <= STANDARD, (name, decl, used)
    final_axioms[name] = {decl: [a.strip() for a in axioms.split(',') if a.strip()]
                          for decl, axioms in ax}

posname = 'Final-controls-unsealed-v2'
negname = 'Final-controls-sealed-v2'
pos = (OUT / (posname + '.lean.txt')).read_text()
neg = (OUT / (negname + '.lean.txt')).read_text()
assert neg.replace(guard, '', 1) == pos
assert len(re.findall(r'^example(?:\s|:)', pos, re.M)) == 64
assert json.loads((OUT / (posname + '-run.json')).read_text())['exit'] == 0
assert not errors((OUT / (posname + '.out')).read_text())
nd = errors((OUT / (negname + '.out')).read_text())
ns = json.loads((OUT / (negname + '-run.json')).read_text())['exit']
assert negative_ok(neg, nd, ns)
synthetic = {
    'missing_error_rejected': not negative_ok(neg, nd[:-1], ns),
    'duplicated_error_replacing_missing_rejected': not negative_ok(neg, [nd[0]] + nd[:-1], ns),
    'exit_zero_rejected': not negative_ok(neg, nd, 0),
    'unexpected_error_kind_rejected': not negative_ok(neg, [dict(nd[0], code='lean.synthetic')] + nd[1:], ns),
}
assert all(synthetic.values())
defs = json.loads((OUT / 'final-seal-inventory.json').read_text())['definitions']
order = defs[:19] + ['Turing.pairEncode', 'Turing.Cfg.mapState', 'Turing.embedEmitTM',
                    'Turing.seamCompTM', 'Turing.embedEmitRetTM', 'Turing.embedEmitCfg',
                    'Turing.rulerHostCfg', 'Turing.StepBlock.forwardLoopCfg', 'Turing.startupLoopTM',
                    'Turing.CodeTM.toFinTM', 'Turing.tapeAction', 'Turing.tableBitsK', 'Turing.unaryFin']
assert len(order) == len(set(order)) == 32 and set(order) == set(defs)
starts = [i for i, line in enumerate(neg.splitlines(), 1) if re.match(r'^example(?:\s|:)', line)]
index = [dict(definition=d, pointwise_start_line=starts[2*i], abstracted_start_line=starts[2*i+1],
              pointwise_error_line=nd[2*i]['line'], abstracted_error_line=nd[2*i+1]['line'])
         for i, d in enumerate(order)]
(OUT / 'controls-index.json').write_text(json.dumps(index, indent=2) + '\n')

pin_check = {}
for rel, expected in CTX['sources'].items():
    path = Path(CTX['worktree']) / rel
    assert sha(path) == expected, path
    olean = Path(CTX['snapshot']) / Path(rel).with_suffix('.olean')
    assert sha(olean) == CTX['compiled'][rel], olean
    pin_check[rel] = dict(source_unchanged=True, compiled_unchanged=True)
assert not list(OUT.rglob('*.lean')) and not list(OUT.rglob('*.pyc'))

result = dict(status='PASS for bounded components/receipts only; F6 remains DRAFT, not ready to dispatch',
              checked_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
              elaboration_attempts=rows, final_component_axioms=final_axioms,
              final_controls=dict(definitions=32, examples=64, unsealed_exit=0, unsealed_errors=0,
                                  sealed_exit=1, sealed_errors=64, exactly_one_error_per_example=True,
                                  source_difference='Only final guard insertion', synthetic_rejections=synthetic),
              pin_checks=pin_check, records_contain_no_actual_lean_or_pyc=True,
              named_argument_review='Manual review recorded in README; this script does not prove absence of foreign unfolding',
              unused_fragment='Additional-controls.lean.txt was generated mechanically from a fragment and never elaborated; authoritative controls are Final-controls-*-v2.')
(OUT / 'verification.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(dict(attempts=len(rows), final_components=len(FINALS), controls='64/32 paired',
                      source_compiled_pins_unchanged=len(pin_check), synthetic_rejections=synthetic), indent=2))
