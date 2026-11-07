"""sorrycensus.py <repo> <rev> <path prefix>: executable `sorry` tokens per .lean file at <rev>
(nested block comments, line comments and string literals stripped in one lexer pass)."""
import sys, subprocess, re
repo, rev, pre = sys.argv[1], sys.argv[2], sys.argv[3]
files = subprocess.run(['git', '-C', repo, 'ls-tree', '-r', '--name-only', rev, pre],
                       capture_output=True, text=True, check=True).stdout.split()
def strip(src):
    out, i, d, n = [], 0, 0, len(src)
    while i < n:
        if src.startswith('/-', i): d += 1; i += 2; continue
        if d:
            if src.startswith('-/', i): d -= 1; i += 2
            else: i += 1
            continue
        if src.startswith('--', i):
            j = src.find('\n', i); i = n if j < 0 else j; continue
        c = src[i]
        if c == '"':
            i += 1
            while i < n and src[i] != '"': i += 2 if src[i] == '\\' else 1
            i += 1; out.append('""'); continue
        if c == "'" and i + 2 < n and (src[i+2] == "'" or (src[i+1] == '\\' and "'" in src[i+2:i+8])):
            j = src.find("'", i + 2 if src[i+1] != '\\' else i + 3); i = j + 1; out.append("'c'"); continue
        out.append(c); i += 1
    return ''.join(out)
tot = 0
for f in files:
    if not f.endswith('.lean'): continue
    src = subprocess.run(['git', '-C', repo, 'show', f'{rev}:{f}'], capture_output=True, text=True).stdout
    k = len(re.findall(r'(?<![\w.\'])sorry(?![\w\'!?])', strip(src)))
    if k: print(f, k); tot += k
print('TOTAL', tot)
