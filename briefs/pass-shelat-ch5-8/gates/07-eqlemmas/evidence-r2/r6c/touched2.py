"""touched2.py <worktree> <base> <files...>: declarations (head side) that #210 adds or whose code
(header to end, docstring excluded, whitespace-normalised) differs from the base declaration of the
same kind and name in the same file. Unlike a line diff, this is immune to diff alignment."""
import re, subprocess, sys
WT, BASE = sys.argv[1], sys.argv[2]
DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec)\s+)*(theorem|lemma|def|abbrev|instance|example|structure)\b\s*([^\s:(\[{]*)')
CMD = re.compile(r'^(end|namespace|section|open|variable|omit|include|universe|noncomputable section|set_option|attribute|export)\b')
INL = re.compile(r'^(variable|open|omit|include)\b.*\bin$')
def lead(lines, st):
    # `variable … in` / `open … in` lines just above the declaration (and its docstring) belong to it
    j = st - 2; out = []
    while j >= 0:
        t = lines[j].strip()
        if t.endswith('-/'):
            while j >= 0 and '/-' not in lines[j]: j -= 1
            j -= 1; continue
        if t.startswith('@['): j -= 1; continue
        if INL.match(t): out.insert(0, t); j -= 1; continue
        break
    return ' '.join(out)
def decls(src):
    lines = src.split('\n')
    starts = [(i + 1, m.group(1), m.group(2)) for i, l in enumerate(lines) if (m := DECL.match(l))]
    out = []
    for k, (st, kind, name) in enumerate(starts):
        en = starts[k + 1][0] - 1 if k + 1 < len(starts) else len(lines)
        while en > st:
            t = lines[en - 1].strip()
            if t == '' or t.startswith('@[') or t.startswith('--') or INL.match(t) or CMD.match(t):
                en -= 1; continue
            if t.endswith('-/'):
                j = en - 1
                while j >= st and '/-' not in lines[j]: j -= 1
                if j < st: break
                en = j; continue
            break
        text = ' '.join((lead(lines, st) + ' ' + ' '.join(lines[st - 1:en])).split())
        out.append((st, kind, name, text))
    return out
for f in sys.argv[3:]:
    head = open(f'{WT}/{f}', encoding='utf-8').read()
    b = subprocess.run(['git', '-C', WT, 'show', f'{BASE}:{f}'], capture_output=True, text=True)
    base = b.stdout if b.returncode == 0 else ''
    bmap = {}
    for st, kind, name, text in decls(base):
        bmap.setdefault((kind, name), []).append(text)
    for st, kind, name, text in decls(head):
        if text not in bmap.get((kind, name), []):
            print(f"{f}\t{kind} {name}@{st}")
