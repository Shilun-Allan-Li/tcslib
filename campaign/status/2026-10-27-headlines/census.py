"""Whole-tree sorry census at a revision (python3 -I): census.py <repo> <rev>; fillinputs.py's detection."""
import sys, re, subprocess
repo, rev = sys.argv[1:3]
files = [f for f in subprocess.run(['git','-C',repo,'ls-tree','-r','--name-only',rev,'TCSlib'],capture_output=True,text=True,check=True).stdout.split() if f.endswith('.lean')]
def strip(src):
    out, i, depth = [], 0, 0
    while i < len(src):
        if src.startswith('/-', i): depth += 1; i += 2; continue
        if src.startswith('-/', i) and depth > 0: depth -= 1; i += 2; continue
        if depth == 0: out.append(src[i])
        i += 1
    return ''.join(out)
DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*(?:theorem|lemma|def|abbrev|instance|structure|inductive|class|example)\s+([^\s(:{\[]*)', re.M)
tot = 0
for f in sorted(files):
    src = subprocess.run(['git','-C',repo,'show',f'{rev}:{f}'],capture_output=True,text=True,check=True).stdout
    cur, names = None, []
    for l in strip(src).split('\n'):
        d = DECL.match(l)
        if d: cur = (d.group(1) or '(anonymous)')
        elif re.match(r'^(end|namespace|section)\b', l): cur = None
        if cur and re.search(r'\bsorry\b', l.split('--')[0]) and (not names or names[-1] != cur): names.append(cur)
    if names:
        tot += len(names); print(f"{f[len('TCSlib/'):-5]}: {len(names)}: {', '.join(names)}")
print('TOTAL', tot)
