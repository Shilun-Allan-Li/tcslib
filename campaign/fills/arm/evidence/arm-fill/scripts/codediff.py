"""Comment-stripped code diff (the stripping of the maintainer's codeonly.py, verbatim logic:
nesting-aware block comments and docstrings removed, `--` line comments cut, blank lines
dropped), optionally ignoring a given set of import lines on the after side.
usage: python3 -I codediff.py <before> <after> [--ignore-added-imports]
Prints `code identical (comments stripped)` or a unified diff of the stripped code.
"""
import difflib, sys
def strip(src):
    out, i, depth = [], 0, 0
    while i < len(src):
        if src.startswith('/-', i): depth += 1; i += 2; continue
        if src.startswith('-/', i) and depth > 0: depth -= 1; i += 2; continue
        if depth == 0: out.append(src[i])
        i += 1
    return [l.split('--')[0].rstrip() for l in ''.join(out).split('\n') if l.split('--')[0].strip()]
a = strip(open(sys.argv[1], encoding='utf-8').read())
b = strip(open(sys.argv[2], encoding='utf-8').read())
if '--ignore-added-imports' in sys.argv:
    added = [l for l in b if l.startswith('import ') and l not in a]
    b = [l for l in b if l not in added]
    print(f'(ignoring {len(added)} added import lines)')
if a == b:
    print('code identical (comments stripped)')
else:
    print('CODE DIFFERS')
    sys.stdout.writelines(l + '\n' for l in difflib.unified_diff(a, b, 'before', 'after', lineterm='', n=1))
