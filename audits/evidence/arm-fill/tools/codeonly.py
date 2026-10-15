import sys
def strip(src):
    out, i, depth = [], 0, 0
    while i < len(src):
        if src.startswith('/-', i): depth += 1; i += 2; continue
        if src.startswith('-/', i) and depth > 0: depth -= 1; i += 2; continue
        if depth == 0: out.append(src[i])
        i += 1
    return [l.split('--')[0].rstrip() for l in ''.join(out).split('\n') if l.split('--')[0].strip()]
a, b = (strip(open(p, encoding='utf-8').read()) for p in sys.argv[1:3])
print('code identical (comments stripped)' if a == b else 'CODE DIFFERS')
