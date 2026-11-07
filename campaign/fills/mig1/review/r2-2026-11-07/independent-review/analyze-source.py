"""Pure data comparison; no imported payload/repository tool scripts, Git or Lean execution."""
from pathlib import Path
from collections import Counter
import difflib
import hashlib
import json
import re

OUT = Path(__file__).resolve().parent
inputs = json.loads((OUT / 'source-inputs.json').read_text())['inputs']
KW = r'(theorem|lemma|def|abbrev|instance|structure|inductive|class)'
DECL = re.compile(r'^(@\[[^\]]*\]\s*)*((private|protected|noncomputable|nonrec|partial|unsafe)\s+)*'
                  + KW + r'\s+([^\s(:{\[]+)')
ANON = re.compile(r'^(@\[[^\]]*\]\s*)*((private|protected|noncomputable|nonrec|partial|unsafe)\s+)*instance(?=\s*[(:{\[]|\s*$)')
STOP = re.compile(r'^(end\b|namespace\b|section\b|/-!|open\b|variable\b|set_option\b|#|attribute\b|universe\b)')
SCOPE = re.compile(r'^(?:(namespace)\s+(\S+)|(?:noncomputable\s+)?(section)\b\s*(\S*)|(mutual)\b|(end)\b\s*(\S*))')


def sha(t):
    return hashlib.sha256(t.encode()).hexdigest()


def strip_comments(s):
    out = []
    depth = 0
    string = False
    i = 0
    while i < len(s):
        if depth:
            if s.startswith('/-', i):
                depth += 1; out.extend('  '); i += 2; continue
            if s.startswith('-/', i):
                depth -= 1; out.extend('  '); i += 2; continue
            out.append('\n' if s[i] == '\n' else ' '); i += 1; continue
        if string:
            out.append(s[i])
            if s[i] == '\\' and i + 1 < len(s):
                out.append(s[i + 1]); i += 2; continue
            if s[i] == '"': string = False
            i += 1; continue
        if s.startswith('/-', i):
            depth = 1; out.extend('  '); i += 2; continue
        if s.startswith('--', i):
            end = s.find('\n', i)
            if end < 0: end = len(s)
            out.extend(' ' * (end - i)); i = end; continue
        if s[i] == '"': string = True
        out.append(s[i]); i += 1
    assert depth == 0 and not string
    return ''.join(out)


def norm(s):
    return ' '.join(strip_comments(s).split())


def chunks(text):
    # Namespace-qualified, comment-aware source declarations, including anonymous instances.
    raw = text.split('\n'); code = strip_comments(text).split('\n')
    out = []; pending = None; current = None; scope = []

    def qualify(name):
        if name.startswith('_root_.'): return name[len('_root_.'):]
        ns = '.'.join(n for kind, n in scope if kind == 'namespace')
        return ns + '.' + name if ns else name

    def close(i):
        nonlocal current
        if current:
            name, private, kind, start, decl_line = current
            t = '\n'.join(raw[start:i]).rstrip()
            if name is None: name = 'instance⟨' + norm(t) + '⟩'
            original = name; k = 1
            while any(row['name'] == name for row in out):
                k += 1; name = original + '#' + str(k)
            out.append(dict(name=name, private=private, kind=kind, text=t,
                            first_line=start + 1, declaration_line=decl_line + 1))
        current = None

    for i, line in enumerate(code):
        if raw[i].startswith('/--'):
            close(i); pending = i; continue
        match = DECL.match(line)
        if match:
            if pending is None: close(i)
            start = pending if pending is not None else i; pending = None
            private = bool(re.search(r'\bprivate\b', line[:match.start(4)]))
            current = (qualify(match.group(5)), private, match.group(4), start, i)
            continue
        if ANON.match(line):
            if pending is None: close(i)
            start = pending if pending is not None else i; pending = None
            current = (None, bool(re.search(r'\bprivate\b', line)), 'instance', start, i)
            continue
        if STOP.match(line) or raw[i].startswith('/-!'):
            close(i); pending = None
            match = SCOPE.match(line)
            if match:
                if match.group(1): scope += [('namespace', c) for c in match.group(2).split('.')]
                elif match.group(3): scope.append(('section', match.group(4)))
                elif match.group(5): scope.append(('mutual', ''))
                else:
                    for c in reversed(match.group(7).split('.')):
                        if scope and scope[-1][1] == c: scope.pop()
                        elif scope and c == '': scope.pop()
    close(len(raw))
    return out


def delimiter(s, kind):
    code = strip_comments(s); stack = []; string = False; candidates = []; i = 0
    pairs = {')': '(', ']': '[', '}': '{', '⟩': '⟨'}
    while i < len(code):
        c = code[i]
        if string:
            if c == '\\': i += 2; continue
            if c == '"': string = False
            i += 1; continue
        if c == '"': string = True
        elif c in '([{⟨': stack.append(c)
        elif c in pairs:
            assert stack and stack.pop() == pairs[c], (kind, i, c)
        elif not stack and code.startswith(':=', i):
            candidates.append(i)
            # Ignore the statement-level let assignments preceding a tactic proof.
            if kind in ['theorem', 'lemma'] and re.match(r':=\s*by\b', code[i:]): return i
            if kind not in ['theorem', 'lemma']: return i
        i += 1
    return candidates[0] if candidates else None


def split(row):
    i = delimiter(row['text'], row['kind'])
    return (row['text'], '') if i is None else (row['text'][:i], row['text'][i + 2:])


def compare(a, b, label, path):
    ca, cb = chunks(a), chunks(b); A = {r['name']: r for r in ca}; B = {r['name']: r for r in cb}
    common = A.keys() & B.keys()
    added = [dict(name=r['name'], kind=r['kind'], private=r['private'], line=r['declaration_line'])
             for r in cb if r['name'] not in A]
    removed = [dict(name=r['name'], kind=r['kind'], private=r['private'], line=r['declaration_line'])
               for r in ca if r['name'] not in B]
    changed = []
    for name in [r['name'] for r in cb if r['name'] in common]:
        x, y = A[name], B[name]
        if x['text'] == y['text']: continue
        hx, bx = split(x); hy, by = split(y)
        changed.append(dict(name=name, kind=y['kind'], private_before=x['private'], private_after=y['private'],
                            before_line=x['declaration_line'], after_line=y['declaration_line'],
                            header_literal_equal=hx == hy, header_code_equal=norm(hx) == norm(hy),
                            body_literal_equal=bx == by, body_code_equal=norm(bx) == norm(by),
                            header_before=hx if norm(hx) != norm(hy) else None,
                            header_after=hy if norm(hx) != norm(hy) else None,
                            declaration_before_sha256=sha(x['text']), declaration_after_sha256=sha(y['text'])))
    imports_a = re.findall(r'^import .*', strip_comments(a), re.M)
    imports_b = re.findall(r'^import .*', strip_comments(b), re.M)
    attrs_a = re.findall(r'^(?:attribute|set_option) .*', strip_comments(a), re.M)
    attrs_b = re.findall(r'^(?:attribute|set_option) .*', strip_comments(b), re.M)
    result = dict(path=path, comparison=label, byte_equal=a == b, code_equal=norm(a) == norm(b),
                  source_before_sha256=sha(a), source_after_sha256=sha(b),
                  public_before=sum(not r['private'] for r in ca), public_after=sum(not r['private'] for r in cb),
                  private_before=sum(r['private'] for r in ca), private_after=sum(r['private'] for r in cb),
                  added=added, removed=removed, changed=changed,
                  imports_equal=imports_a == imports_b, imports_before=imports_a, imports_after=imports_b,
                  attribute_option_commands_equal=attrs_a == attrs_b,
                  retained_order_equal=[r['name'] for r in ca if r['name'] in common] == [r['name'] for r in cb if r['name'] in common])
    diff = ''.join(difflib.unified_diff(a.splitlines(keepends=True), b.splitlines(keepends=True),
                                     fromfile=label.split('-to-')[0] + '/' + path,
                                     tofile=label.split('-to-')[1] + '/' + path))
    dest = OUT / 'diffs' / label / (path + '.diff'); dest.parent.mkdir(parents=True, exist_ok=True); dest.write_text(diff)
    return result


results = []; admissions = []; census = {}
for row in inputs:
    texts = {key: Path(row['current_snapshot'] if key == 'current' else row[key]).read_text()
             for key in ['r1', 'r2', 'current']}
    for key, text in texts.items():
        assert sha(text) == row['hashes'][key]['sha256']
        code = strip_comments(text)
        for match in re.finditer(r'\b(sorry|admit)\b', code):
            line = code.count('\n', 0, match.start()) + 1
            owners = [r for r in chunks(text) if r['first_line'] <= line]
            admissions.append(dict(version=key, path=row['path'], line=line, token=match[1],
                                   declaration=owners[-1]['name'] if owners else None))
        census.setdefault(key, []).extend(dict(path=row['path'], **{k: r[k] for k in ['name', 'private', 'kind', 'declaration_line']}) for r in chunks(text))
    for label in ['r1-to-r2', 'r2-to-current']:
        before, after = label.split('-to-')
        results.append(compare(texts[before], texts[after], label, row['path']))
(OUT / 'declaration-comparisons.json').write_text(json.dumps(results, indent=2) + '\n')
(OUT / 'admissions.json').write_text(json.dumps(admissions, indent=2) + '\n')
(OUT / 'source-census.json').write_text(json.dumps(census, indent=2) + '\n')
for result in results:
    if result['comparison'] != 'r1-to-r2' or result['byte_equal']: continue
    print(json.dumps(dict(path=result['path'], added=result['added'], removed=result['removed'],
                         semantic_changes=[dict(name=r['name'], kind=r['kind'], header_equal=r['header_code_equal'])
                                           for r in result['changed'] if not r['body_code_equal'] or not r['header_code_equal']],
                         all_imports_equal=result['imports_equal'], all_attrs_options_equal=result['attribute_option_commands_equal']), indent=2))
print('CENSUS', {key: dict(public=sum(not r['private'] for r in values), private=sum(r['private'] for r in values)) for key, values in census.items()})
print('ADMISSIONS', dict(Counter(row['version'] for row in admissions)))
