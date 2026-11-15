#!/usr/bin/env python3
"""Compare frozen Lean declarations, including prefixes and definition bodies."""
import argparse
import difflib
import json
from pathlib import Path
import re
import subprocess

BASE = 'fbd37f447596d4207c8d08b7ef7602f57fe95198'
DIRECTORY = 'TCSlib/Cryptography/SecureComputation/'
FILES = ['SpecialEncryptionSecurity.lean', 'SpecialEncryptionMulti.lean',
         'Garbling.lean', 'GarblingSecurity.lean', 'Yao.lean']
TARGETS = {'spDecStr_wrongKey', 'specialScheme_wrongKey', 'specialScheme_multiMessageSecure',
           'nestedSpecial_wrongKeyBot', 'uprob_not_good_le', 'yaoSeed_good_whp',
           'sliceMultiMessageSecure_of_prfOut', 'specialScheme_multiMessageSecure_of_joint'}
REMOVALS = {'specialScheme_gen_runAt', 'specialScheme_enc_runAt', 'specialKeyEq',
            'ofFn_specialKeyEq', 'specialNonceEq', 'ofFn_specialNonceEq'}
DECL = re.compile(r'^(?:@\[[\s\S]*?\][ \t\n]*)?'
    r'(?:(?:private|protected|noncomputable|nonrec|unsafe|partial)\s+)*'
    r'(?P<kind>theorem|lemma|def|abbrev|structure|inductive|class|instance|opaque|axiom)\b', re.M)
COMMAND = re.compile(r'^(?:namespace|section|end|variable|open|include|omit|set_option|attribute)\b', re.M)

def lex(text):
    """Blank nested comments and strings while preserving all offsets."""
    code = list(text)
    comments = []
    i = 0
    while i < len(text):
        start = i
        if text.startswith('/-', i):
            depth = 1
            i += 2
            while depth:
                if text.startswith('/-', i): depth += 1; i += 2
                elif text.startswith('-/', i): depth -= 1; i += 2
                else: i += 1
                if i > len(text): raise ValueError('unclosed comment')
            comments.append((start, i))
        elif text.startswith('--', i):
            i = text.find('\n', i)
            if i < 0: i = len(text)
        elif text[i] == '"':
            i += 1
            while i < len(text) and text[i] != '"':
                i += 2 if text[i] == '\\' else 1
            i += 1
        else:
            i += 1
            continue
        for j in range(start, min(i, len(text))):
            if code[j] != '\n': code[j] = ' '
    return ''.join(code), comments

def declarations(text):
    code, comments = lex(text)
    matches = list(DECL.finditer(code))
    boundaries = sorted([m.start() for m in matches] + [m.start() for m in COMMAND.finditer(code)]
                        + [len(code)])
    result = []
    for index, match in enumerate(matches):
        start = match.start()
        end = next(x for x in boundaries if x > start)
        end = start + len(code[start:end].rstrip())
        depth = 0
        cut = None
        pos = match.end()
        while pos < end:
            c = code[pos]
            if c in '([{': depth += 1
            elif c in ')]}': depth -= 1
            if depth == 0 and (code.startswith(':=', pos) or
                re.match(r'\b(?:where|by)\b', code[pos:]) or c == '|'):
                cut = pos
                break
            pos += 1
        cut = end if cut is None else cut
        token = re.match(r'\s*([^\s({\[:=]+)', code[match.end():cut])
        name = token.group(1) if token else '@anonymous_' + str(index)
        prefix = ''
        previous = code[:start].rstrip()
        if previous:
            line_start = previous.rfind('\n') + 1
            if re.fullmatch(r'(?:include|omit|open)\b[^\n]*\bin', previous[line_start:]):
                prefix = text[line_start:len(previous)] + '\n'
        doc = next(((a, b) for a, b in reversed(comments)
                    if b <= start and text[a:a+3] == '/--'), None)
        result.append(dict(name=name, kind=match.group('kind'),
            header=prefix + text[start:cut], full=text[start:end],
            start=start, end=end, cut=cut,
            doc=text[doc[0]:doc[1]] if doc else '', doc_range=doc))
    return result

def compare(old, new, file):
    before, after = declarations(old), declarations(new)
    lookup = {x['name']: x for x in after}
    assert len(lookup) == len(after), 'duplicate parsed declaration name'
    issues, expected = [], []
    for decl in before:
        name = decl['name']
        if name not in lookup:
            (expected if file == 'SpecialEncryptionMulti.lean' and name in REMOVALS else issues).append(
                dict(kind='REMOVED', name=name))
            continue
        now = lookup[name]
        if now['header'] != decl['header']:
            issues.append(dict(kind='CHANGED', name=name, field='header'))
        if decl['kind'] not in ('theorem', 'lemma') or name not in TARGETS:
            if now['full'] != decl['full']:
                issues.append(dict(kind='CHANGED', name=name, field='definition/proof'))
        doc_before, doc_after = decl['doc'], now['doc']
        if name in TARGETS and name != 'specialScheme_multiMessageSecure_of_joint':
            doc_before = doc_before.split('**Proof sketch.**')[0]
            doc_after = doc_after.split('**Proof sketch.**')[0]
        if doc_before != doc_after:
            issues.append(dict(kind='CHANGED', name=name, field='statement/docstring'))
    before_names = [d['name'] for d in before if d['name'] in lookup]
    retained = {d['name'] for d in before}
    after_names = [d['name'] for d in after if d['name'] in retained]
    if before_names != after_names:
        issues.append(dict(kind='ORDER', before=before_names, after=after_names))
    return dict(file=file, base_declarations=len(before), final_declarations=len(after),
                expected_removals=expected, issues=issues)

def mask_yao(text):
    decl = next(x for x in declarations(text) if x['name'] == 'yaoSeed_good_whp')
    spans = [(decl['cut'], decl['end'], '<BODY>')]
    a, b = decl['doc_range']
    sketch = text.index('**Proof sketch.**', a, b)
    spans.append((sketch, b-2, '<SKETCH>'))
    bullet = re.search(r'^\*[^\n]*yaoSeed_good_whp[^\n]*\n(?:  [^\n]*\n)*', text, re.M)
    assert bullet
    spans.append((bullet.start(), bullet.end(), '<BULLET>\n'))
    for start, end, value in sorted(spans, reverse=True):
        text = text[:start] + value + text[end:]
    return text

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', required=True)
    args = parser.parse_args()
    dest = Path(args.output)
    dest.mkdir(parents=True, exist_ok=True)
    reports = []
    for file in FILES:
        old = subprocess.check_output(['git','show',BASE+':'+DIRECTORY+file]).decode()
        new = Path(DIRECTORY+file).read_text()
        report = compare(old, new, file)
        if file == 'Yao.lean':
            report['outside_allowed_ranges_identical'] = mask_yao(old) == mask_yao(new)
            if not report['outside_allowed_ranges_identical']:
                report['issues'].append(dict(kind='YAO_OUTSIDE_SCOPE'))
            (dest/'Yao.diff').write_text(''.join(difflib.unified_diff(old.splitlines(True),
                new.splitlines(True), fromfile='base/Yao.lean', tofile='final/Yao.lean')))
        (dest/(file+'.base')).write_text(old)
        reports.append(report)
    sec = subprocess.check_output(['git','show',BASE+':'+DIRECTORY+FILES[0]]).decode()
    altered = sec.replace('theorem spDecStr_wrongKey (ℓ : PolyExpr)',
                          'theorem spDecStr_wrongKey (α : PolyExpr)', 1)
    (dest/'header-character-control.lean.txt').write_text(altered)
    control = compare(sec, altered, FILES[0])
    assert len(control['issues']) == 1 and control['issues'][0]['field'] == 'header', control
    multi = subprocess.check_output(['git','show',BASE+':'+DIRECTORY+FILES[1]]).decode()
    seventh = next(x for x in declarations(multi) if x['name']=='zipWith_xor_append_of_le')
    altered = multi[:seventh['start']] + multi[seventh['end']:]
    (dest/'seventh-removal-control.lean.txt').write_text(altered)
    removal = compare(multi, altered, FILES[1])
    assert len(removal['issues']) == 1 and removal['issues'][0]['kind'] == 'REMOVED', removal
    (dest/'controls.json').write_text(json.dumps(dict(character=control,seventh=removal),indent=2)+'\n')
    (dest/'results.json').write_text(json.dumps(reports,indent=2)+'\n')
    for report in reports:
        print(report['file'], 'base', report['base_declarations'], 'final',
              report['final_declarations'], 'expected REMOVED',len(report['expected_removals']),
              'differences', len(report['issues']))
        for issue in report['issues']: print(issue)
    print('CONTROLS PASS: one changed header; one unexpected seventh removal')
    if any(r['issues'] for r in reports): raise SystemExit(1)

if __name__ == '__main__': main()
