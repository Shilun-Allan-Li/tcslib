import sys
def strip(src):
    out, i, n, depth = [], 0, len(src), 0
    while i < n:
        if src.startswith('/-', i):
            depth += 1; i += 2; continue
        if depth and src.startswith('-/', i):
            depth -= 1; i += 2; continue
        if depth: i += 1; continue
        if src.startswith('--', i):
            j = src.find('\n', i); i = n if j < 0 else j; continue
        if src[i] == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == '\\' else 1
            out.append(src[i:j+1]); i = j + 1; continue
        out.append(src[i]); i += 1
    return '\n'.join(l.rstrip() for l in ''.join(out).splitlines() if l.strip())
a, b = (open(p, encoding='utf-8').read() for p in sys.argv[1:3])
print('CODE IDENTICAL' if strip(a) == strip(b) else 'CODE DIFFERS')
