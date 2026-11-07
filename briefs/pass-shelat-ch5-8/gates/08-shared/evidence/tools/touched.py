"""touched.py <worktree> <base-rev> <file.lean>: top-level declarations of the head file whose text
(docstring included) contains an added line, or sits at a deletion point, of `git diff -U0 base`.
Prints one declaration name (as written) per line."""
import re, subprocess, sys
wt, base, f = sys.argv[1:4]
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec)\s+)*"
                  r"(theorem|lemma|def|instance|structure|inductive|abbrev|class)\s+([^\s(:{\[]+)")
diff = subprocess.run(['git', '-C', wt, 'diff', '-U0', base, '--', f], capture_output=True, text=True).stdout
hits = set()
for m in re.finditer(r'^@@ -\d+(?:,(\d+))? \+(\d+)(?:,(\d+))? @@', diff, re.M):
    start = int(m.group(2)); cnt = int(m.group(3)) if m.group(3) is not None else 1
    if cnt == 0: hits.add(start + 0.5)          # pure deletion after line `start`
    else: hits.update(range(start, start + cnt))
L = open(f"{wt}/{f}", encoding='utf-8').read().split('\n')
starts = []
for i, l in enumerate(L, 1):
    m = DECL.match(l)
    if m:
        a = i
        if i > 1 and L[i-2].rstrip().endswith('-/'):
            a = i - 1
            while not L[a-1].startswith('/--') and not L[a-1].startswith('/-!'): a -= 1
            if L[a-1].startswith('/-!'): a = i
        starts.append((a, i, m.group(2)))
names = []
for k, (a, i, n) in enumerate(starts):
    end = (starts[k+1][0] - 1) if k + 1 < len(starts) else len(L)
    if any(a <= h <= end + 0.5 for h in hits): names.append(n)
for n in names: print(n)
