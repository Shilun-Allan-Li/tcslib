"""Compare issued declaration headers, definition bodies, order, and frozen proofs.

This scanner preserves byte offsets, masks nested comments and string contents, and
only recognizes declaration commands at indentation zero. Binder delimiters keep
proof terms inside header binders from being mistaken for the declaration body.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

BASE = '01de2d8baed9113e4a099e13c5d50c81e6dbc66f'
FILES = [
    'TCSlib/Complexity/Randomized/SeedMajority.lean',
    'TCSlib/Cryptography/Randomness/Derandomization.lean',
    'TCSlib/Complexity/Randomized/Build/IterateFind.lean',
    'TCSlib/Complexity/ClassP/DTIME.lean',
    'TCSlib/Complexity/Randomized/Classes.lean',
]
MUTABLE = {'exists_seedMajorityTM', 'seedMajority_mem_DTIME', 'bpp_subset_dtime_subexp'}
DECL = re.compile(r'(?m)^(?:(?:@\[[^\n]*\]|private|protected|noncomputable|unsafe|partial|'
                  r'nonrec|local|scoped)\s+)*'
                  r'(?P<kind>theorem|lemma|def|abbrev|structure|inductive|class|instance)'
                  r'\s+(?P<name>[^\s(:\[{]+)')

def mask(src):
    chars = list(src)
    i = 0
    while i < len(src):
        if src.startswith('/-', i):
            start, depth = i, 1
            i += 2
            while i < len(src) and depth:
                if src.startswith('/-', i):
                    depth += 1
                    i += 2
                elif src.startswith('-/', i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            for j in range(start, i):
                if chars[j] != '\n':
                    chars[j] = ' '
        elif src.startswith('--', i):
            end = src.find('\n', i)
            end = len(src) if end < 0 else end
            chars[i:end] = ' ' * (end - i)
            i = end
        elif src[i] == '"':
            i += 1
            while i < len(src):
                if src[i] == '\\':
                    chars[i:i + 2] = '  '
                    i += 2
                elif src[i] == '"':
                    i += 1
                    break
                else:
                    if chars[i] != '\n':
                        chars[i] = ' '
                    i += 1
        else:
            i += 1
    return ''.join(chars)

def extract(src):
    masked = mask(src)
    found = list(DECL.finditer(masked))
    result = []
    for j, match in enumerate(found):
        start = match.start()
        # An open-in prefix is a part of the frozen header, even across its docstring.
        prior = masked[:start].rstrip()
        openin = re.search(r'(?m)^open [^\n]+ in[ \t]*\Z', prior)
        prefix = src[openin.start():openin.end()].strip() if openin else ''
        pos, depth, boundary = match.end(), 0, None
        while pos < len(src):
            char = masked[pos]
            if depth == 0 and (masked.startswith(':=', pos) or char == '|' or
                               re.match(r'(by|where)\b', masked[pos:])):
                boundary = pos
                break
            if char in '([{⦃':
                depth += 1
            elif char in ')]}⦄':
                depth -= 1
            pos += 1
        if boundary is None:
            raise ValueError('No body boundary for ' + match['name'])
        limit = found[j + 1].start() if j + 1 < len(found) else len(src)
        # Namespaces and section ends delimit the last declaration in each scope.
        command = re.search(r'(?m)^(?:end(?:\s+[^\n]+)?|namespace\s+[^\n]+|'
                            r'section(?:\s+[^\n]+)?)\s*$', masked[boundary:limit])
        if command:
            limit = boundary + command.start()
        # Stop at the last non-comment token, keeping inline comments in the body.
        end = boundary + len(masked[boundary:limit].rstrip())
        header = src[start:boundary]
        if prefix:
            header = prefix + '\n' + header
        result.append(dict(name=match['name'], kind=match['kind'], header=header,
                           whole=src[start:end], start=start,
                           line=src.count('\n', 0, start) + 1))
    return result

def compare(base, final):
    before, after = extract(base), extract(final)
    by_name = {d['name']: d for d in after}
    differences = []
    for d in before:
        f = by_name.get(d['name'])
        if f is None:
            differences.append((d['name'], 'missing'))
        elif d['header'] != f['header']:
            differences.append((d['name'], 'header'))
        elif d['kind'] not in {'theorem', 'lemma'} and d['whole'] != f['whole']:
            differences.append((d['name'], 'definition body'))
        elif d['name'] not in MUTABLE and d['whole'] != f['whole']:
            differences.append((d['name'], 'frozen proof'))
    names = {d['name'] for d in before}
    if [d['name'] for d in after if d['name'] in names] != [d['name'] for d in before]:
        differences.append(('<order>', 'declaration order'))
    return before, after, differences

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--out', default='evidence/headers')
    args = parser.parse_args()
    out = Path(args.out)
    out.mkdir(parents=True, exist_ok=True)
    all_rows, errors = [], []
    for path in FILES:
        base = subprocess.check_output(['git', 'show', f'{BASE}:{path}'], text=True)
        final = Path(path).read_text()
        before, after, differences = compare(base, final)
        errors.extend((path, *d) for d in differences)
        for declaration in before:
            all_rows.append(dict(path=path, name=declaration['name'], kind=declaration['kind'],
                                 header_sha256=hashlib.sha256(
                                     declaration['header'].encode()).hexdigest()))
        print(f'{path}: base={len(before)} final={len(after)} differences={len(differences)}')
    # Negative control alters exactly one type character, leaving the name/order intact.
    path = FILES[0]
    base = subprocess.check_output(['git', 'show', f'{BASE}:{path}'], text=True)
    control = base.replace('theorem half_lt_randProb_iff (m : ℕ)',
                           'theorem half_lt_randProb_iff (m : ℤ)', 1)
    (out / 'control.lean').write_text(control)
    _, _, control_diff = compare(base, control)
    control_ok = control_diff == [('half_lt_randProb_iff', 'header')]
    print(f'CONTROL differences={len(control_diff)} {control_diff}: '
          f'{"PASS" if control_ok else "FAIL"}')
    (out / 'headers.json').write_text(json.dumps(all_rows, indent=2) + '\n')
    (out / 'results.json').write_text(json.dumps(dict(differences=errors,
                                                    control=control_diff), indent=2) + '\n')
    print(f'FROZEN STATEMENTS {"PASS" if not errors and control_ok else "FAIL"}: '
          f'{len(all_rows)} base declarations; {len(errors)} differences')
    for row in errors:
        print(row)
    raise SystemExit(bool(errors or not control_ok))

if __name__ == '__main__':
    main()
