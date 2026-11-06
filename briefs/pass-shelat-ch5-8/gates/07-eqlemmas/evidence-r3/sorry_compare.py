"""sorry_compare.py <worktree> <base> <head-rev> <replay-log-dir> <files...>: executable `sorry` tokens
(block/line comments and string literals removed, nested `/- -/` handled) per file at <base> and at
<head-rev>, and the head replay's `declaration uses 'sorry'` warnings where the module was replayed."""
import re, subprocess, sys, os
WT, BASE, HEAD, LOGS = sys.argv[1:5]
def strip(src):
    out, i, depth, n = [], 0, 0, len(src)
    while i < n:
        if src.startswith('/-', i): depth += 1; i += 2; continue
        if depth and src.startswith('-/', i): depth -= 1; i += 2; continue
        if depth: i += 1; continue
        if src.startswith('--', i):
            j = src.find('\n', i); i = n if j < 0 else j; continue
        if src[i] == '"':
            j = i + 1
            while j < n and src[j] != '"': j += 2 if src[j] == '\\' else 1
            i = j + 1; continue
        out.append(src[i]); i += 1
    return ''.join(out)
def count(rev, f):
    p = subprocess.run(['git', '-C', WT, 'show', f'{rev}:{f}'], capture_output=True, text=True)
    return len(re.findall(r'(?<![\w.])sorry(?![\w])', strip(p.stdout))) if p.returncode == 0 else 'absent'
print('file\tbase_sorry_tokens\thead_sorry_tokens\thead_replay_sorry_warnings')
for f in sys.argv[5:]:
    log = os.path.join(LOGS, f[:-5].replace('/', '_') + '.log')
    w = open(log).read().count("declaration uses 'sorry'") if os.path.exists(log) else '-'
    print(f'{f}\t{count(BASE, f)}\t{count(HEAD, f)}\t{w}')
