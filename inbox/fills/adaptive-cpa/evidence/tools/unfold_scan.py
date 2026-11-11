"""Explicit-unfold scan over the lines added since the issue base in the changed files.

Lists `unfold`/`delta` targets and every identifier inside `rw`/`simp`/`simpa`/`simp only`
brackets, and flags those naming a TCSlib `def`/`abbrev` declared outside the file that uses it.
Usage (from the clone): python3 -I unfold_scan.py <base>
"""
import re
import subprocess
import sys

base = sys.argv[1]
files = subprocess.run(['git', 'diff', '--name-only', base, 'HEAD'], capture_output=True,
                       text=True, check=True).stdout.split()
defs = {}
for path in subprocess.run(['git', 'ls-files', 'TCSlib'], capture_output=True, text=True,
                           check=True).stdout.split():
    if not path.endswith('.lean'):
        continue
    for line in open(path, encoding='utf-8'):
        m = re.match(r'^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?(?:noncomputable\s+)?'
                     r'(?:def|abbrev)\s+([^\s(:]+)', line)
        if m:
            defs.setdefault(m.group(1).split('.')[-1], set()).add(path)
flag = False
for f in files:
    diff = subprocess.run(['git', 'diff', '-U0', base, 'HEAD', '--', f], capture_output=True,
                          text=True, check=True).stdout
    added = '\n'.join(l[1:] for l in diff.splitlines() if l.startswith('+') and not l.startswith('+++'))
    unf = re.findall(r'\b(?:unfold|delta)\s+([^\n]+)', added)
    targets = sorted({t for u in unf for t in u.split()})
    brackets = re.findall(r'\b(?:rw|rewrite|simp|simp only|simpa only|simpa|dsimp only|dsimp)\s*\[([^\]]*)\]', added, re.S)
    ids = sorted({i.strip().lstrip('←').strip() for b in brackets for i in b.split(',') if i.strip()})
    local = set(re.findall(r'\bhave\s+([^\s:]+)', added))
    for pat in re.findall(r'\b(?:obtain|rcases)\s*⟨([^⟩]*)⟩', added):
        local |= {t.strip() for t in pat.split(',')}
    local |= set(re.findall(r'\bfun\s+(\w+)', added))
    for grp in re.findall(r'\bintro\s+([^\n]+)', added):
        local |= set(grp.split())
    foreign = []
    for i in targets + ids:
        head = i.split()[0]
        if head in local:
            continue
        key = head.split('.')[-1]
        homes = defs.get(key, set())
        if homes and f not in homes:
            foreign.append((i, sorted(homes)))
    print(f'== {f}')
    print('Explicit unfold/delta targets:', targets)
    print('Rewrite/simp bracket identifiers:', ids)
    print('Foreign definition names among them:', foreign)
    flag |= bool(foreign)
print('RESULT:', 'FLAGGED (see above)' if flag else 'PASS: no foreign definition is unfolded, rewritten or simp-unfolded explicitly')
