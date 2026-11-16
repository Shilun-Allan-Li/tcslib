#!/usr/bin/env python3
"""Check frozen headers, definitions, order, exact insertion scope, and controls."""
import argparse
import difflib
import json
from pathlib import Path
import re
import runpy
import subprocess

lexer = runpy.run_path('evidence/tools/header_lexer.py')
declarations = lexer['declarations']
BASE = '6ce4658db08a1dc2a03a149987197660db078011'
YAOPATH = 'TCSlib/Cryptography/SecureComputation/Yao.lean'
FILES = [YAOPATH, 'TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean',
         'TCSlib/Complexity/CircuitComplexity/Uniform.lean']
TARGETS = {'yaoHybrid_polyTime', 'yaoHybrid_simulators'}
READERS = {
    FILES[1]: {'isFaninTwo_iff'},
    FILES[2]: {'encodeList_nil', 'encodeList_cons', 'GateKind.encode_and',
               'GateKind.encode_or', 'GateKind.encode_not', 'DAGGate.encode_eq',
               'DAGCircuit.encode_parts'},
}

def source_at(path):
    return subprocess.check_output(['git', 'show', BASE + ':' + path], text=True)

def compare_headers(old, new):
    before, after = declarations(old), declarations(new)
    names = {d['name'] for d in before}
    retained = [d for d in after if d['name'] in names]
    differences = []
    if [d['name'] for d in before] != [d['name'] for d in retained]:
        differences.append({'field': 'ORDER_OR_MISSING'})
    else:
        # Compare by occurrence and order, so names in different namespaces never collide.
        for d, now in zip(before, retained):
            if d['header'] != now['header']:
                differences.append({'name': d['name'], 'field': 'HEADER'})
            elif d['kind'] not in {'theorem', 'lemma'} and d['full'] != now['full']:
                differences.append({'name': d['name'], 'field': 'DEFINITION'})
    return before, after, differences

def mask_yao(text):
    spans = []
    for d in declarations(text):
        if d['name'] not in TARGETS:
            continue
        spans.append((d['cut'], d['end'], '<TARGET_BODY>'))
        a, b = d['doc_range']
        sketch = text.index('**Proof sketch.**', a, b)
        spans.append((sketch, b - 2, '<TARGET_SKETCH>'))
    first = re.search(r'^\* `SecureComputation\.(?:yaoSeed_good_whp|yaoHybrid_polyTime)`', text, re.M)
    last = re.search(r'^\* `SecureComputation\.yaoHybrid_hbcSecure`', text, re.M)
    assert first and last
    spans.append((first.start(), last.start(), '<MAIN_RESULTS_BULLET>\n'))
    for a, b, value in sorted(spans, reverse=True):
        text = text[:a] + value + text[b:]
    hub = 'import TCSlib.Cryptography.SecureComputation.Yao.HybridProof\n'
    if hub in text:
        assert text.count(hub) == 1
        assert 'import TCSlib.Cryptography.Foundations.BitLists\n' + hub in text
        text = text.replace(hub, '')
    return text

def remove_readers(text, allowed, before_names):
    spans = []
    for d in declarations(text):
        if d['name'] in before_names:
            continue
        if d['name'] not in allowed:
            raise ValueError('unapproved declaration ' + d['name'])
        assert d['doc_range'] is not None, d['name']
        assert '@[' not in d['header'], d['name']
        assert d['full'][d['cut'] - d['start']:].strip() in {':= rfl', ':= Iff.rfl'}, d['name']
        a = d['doc_range'][0]
        b = d['end']
        assert text[b:b+2] == '\n\n', (d['name'], repr(text[b:b+5]))
        spans.append((a, b + 2))
    for a, b in sorted(spans, reverse=True):
        text = text[:a] + text[b:]
    return text

parser = argparse.ArgumentParser()
parser.add_argument('--output', required=True)
args = parser.parse_args()
out = Path(args.output)
out.mkdir(parents=True, exist_ok=True)
reports = []
for path in FILES:
    old, new = source_at(path), Path(path).read_text()
    before, after, differences = compare_headers(old, new)
    names = {d['name'] for d in before}
    if path == YAOPATH:
        scope = mask_yao(old) == mask_yao(new)
        added = [d['name'] for d in after if d['name'] not in names]
        if added:
            differences.append({'field': 'NEW_YAO_DECLARATION', 'names': added})
        lines = len(new.splitlines())
        if lines + 28 > 1200:
            differences.append({'field': 'LINE_BUDGET', 'issue_base_lines': lines})
    else:
        stripped = remove_readers(new, READERS[path], names)
        scope = stripped == old
        if path == FILES[1]:
            d = next(d for d in after if d['name'] == 'isFaninTwo_iff')
            block = new[d['doc_range'][0]:d['end']]
            garble = subprocess.check_output(['git', 'show',
                'a73072f1:inbox/fills/sc-garble/src/' + path], text=True)
            relative = next(d for d in declarations(garble) if d['name'] == 'isFaninTwo_iff')
            assert block == garble[relative['doc_range'][0]:relative['end']]
    if not scope:
        differences.append({'field': 'REGION_VIOLATION'})
    stem = Path(path).stem
    (out / (stem + '.base')).write_text(old)
    (out / (stem + '.diff')).write_text(''.join(difflib.unified_diff(
        old.splitlines(True), new.splitlines(True), fromfile='base/' + path,
        tofile='current/' + path)))
    report = dict(path=path, base_declarations=len(before), current_declarations=len(after),
                  base_private=sum('private ' in d['header'] for d in before),
                  scope_identical_after_masking=scope, differences=differences)
    reports.append(report)
    print(json.dumps(report))
old = source_at(YAOPATH)
changed = old.replace('theorem yaoHybrid_polyTime (hE₁', 'theorem yaoHybrid_polyTime (hF₁', 1)
(out / 'header-control.lean.txt').write_text(changed)
header_differences = compare_headers(old, changed)[2]
assert header_differences == [{'name': 'yaoHybrid_polyTime', 'field': 'HEADER'}]
changed = old.replace('set_option autoImplicit false\n',
                      'set_option autoImplicit false\n-- frozen-region control\n', 1)
(out / 'region-control.lean.txt').write_text(changed)
region_violations = int(mask_yao(old) != mask_yao(changed))
assert region_violations == 1
(out / 'controls.json').write_text(json.dumps(dict(header=header_differences,
    region_violations=region_violations), indent=2) + '\n')
(out / 'results.json').write_text(json.dumps(reports, indent=2) + '\n')
print('CONTROLS PASS: exactly one changed header; exactly one frozen-region violation')
raise SystemExit(any(r['differences'] for r in reports))
