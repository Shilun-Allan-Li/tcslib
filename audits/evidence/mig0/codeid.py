import sys, difflib
def strip(src):
    out, i, depth = [], 0, 0
    while i < len(src):
        if src.startswith('/-', i): depth += 1; i += 2; continue
        if src.startswith('-/', i) and depth > 0: depth -= 1; i += 2; continue
        if depth == 0:
            if src.startswith('--', i):
                j = src.find('\n', i); i = len(src) if j < 0 else j; continue
            out.append(src[i])
        i += 1
    return [l.rstrip() for l in ''.join(out).split('\n') if l.strip()]
a, b = (strip(open(p, encoding='utf-8').read()) for p in sys.argv[1:3])
d = [l for l in difflib.unified_diff(a, b, lineterm='', n=0) if l[:1] in '+-' and not l.startswith(('+++', '---'))]
print(f'{sys.argv[1]} -> {sys.argv[2]}: {len(a)} and {len(b)} code lines (comments, docstrings and module docs removed); differing lines:')
print('\n'.join(d) if d else '(none)')
