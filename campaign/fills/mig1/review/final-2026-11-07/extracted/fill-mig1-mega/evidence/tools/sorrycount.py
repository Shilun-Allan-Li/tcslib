"""sorrycount.py <repo> <rev-or-WORKTREE> <file>...: static `sorry` tokens outside comments and
strings, per file, with the declarations containing them (declfreeze chunks)."""
import os, re, subprocess, sys
repo, rev, files = sys.argv[1], sys.argv[2], sys.argv[3:]
code = open(os.path.join(repo, 'devtools/seyoon/declfreeze.py'), encoding='utf-8').read()
code = code[:code.index('a = chunks(open(sys.argv[1])')]; ns = {}; exec(compile(code, 'df', 'exec'), ns)
def strip(t):
    out = []; i = 0; d = 0
    while i < len(t):
        if t.startswith('/-', i): d += 1; i += 2; continue
        if d and t.startswith('-/', i): d -= 1; i += 2; continue
        if d: i += 1; continue
        if t.startswith('--', i):
            j = t.find('\n', i); i = len(t) if j < 0 else j; continue
        out.append(t[i]); i += 1
    return ''.join(out)
tot = 0
for f in files:
    t = open(os.path.join(repo, f), encoding='utf-8').read() if rev == 'WORKTREE' else \
        subprocess.run(['git', '-C', repo, 'show', f'{rev}:{f}'], capture_output=True, text=True).stdout
    names = [n for n, p, c in ns['chunks'](t) if re.search(r'\bsorry\b', strip(c))]
    n = len(re.findall(r'\bsorry\b', strip(t))); tot += n
    print(f'{n:3d} {f} {names}')
print('TOTAL', tot)
