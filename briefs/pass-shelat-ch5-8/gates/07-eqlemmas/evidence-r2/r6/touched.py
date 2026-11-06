"""touched.py <worktree> <base> <files...>: declarations (head side) whose source lines this PR changed
(added or modified lines inside the declaration's extent: from its header to the next declaration)."""
import re, subprocess, sys
WT, BASE = sys.argv[1], sys.argv[2]
DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec)\s+)*(theorem|lemma|def|abbrev|instance|example|structure)\b\s*([^\s:(\[{]*)')
for f in sys.argv[3:]:
    d = subprocess.run(['git', '-C', WT, 'diff', '-U0', BASE, '--', f], capture_output=True, text=True).stdout
    changed = set()
    for m in re.finditer(r'^@@ -\d+(?:,\d+)? \+(\d+)(?:,(\d+))? @@', d, re.M):
        s, c = int(m.group(1)), int(m.group(2) or 1)
        changed.update(range(s, s + max(c, 1)))
    lines = open(f'{WT}/{f}', encoding='utf-8').read().split('\n')
    starts = [(i + 1, f"{m.group(1)} {m.group(2)}") for i, l in enumerate(lines) if (m := DECL.match(l))]
    for k, (st, name) in enumerate(starts):
        en = starts[k + 1][0] - 1 if k + 1 < len(starts) else len(lines)
        # drop the trailing blank lines, comments and the next declaration's docstring/attributes
        while en > st:
            t = lines[en - 1].strip()
            if t == '' or t.startswith('@[') or t.startswith('--'):
                en -= 1; continue
            if t.endswith('-/'):
                j = en - 1
                while j >= st and '/-' not in lines[j]: j -= 1
                if j < st: break
                en = j; continue
            break
        # include the declaration's own docstring (just above its header)
        sd = st
        j = st - 2
        if j >= 0 and lines[j].strip().endswith('-/'):
            while j >= 0 and '/-' not in lines[j]: j -= 1
            sd = j + 1
        if any(sd <= x <= en for x in changed):
            print(f"{f}\t{name}@{st}")
