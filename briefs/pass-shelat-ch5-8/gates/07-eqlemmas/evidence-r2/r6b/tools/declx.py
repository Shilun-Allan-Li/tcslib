"""Declaration extents of a Lean source file (gate 04 round 4 helper).

extents(src) -> list of dict(name, kind, start, dstart, end): 1-based lines; `dstart` is the first
line of the declaration's leading docstring/attribute block, `start` the keyword line, `end` the
last non-blank line before the next top-level command.

CLI: declx.py changes <repo> <rev_old> <rev_new> <file>: per declaration of <file> at <rev_new>,
NEW / SAME / CHANGED (statement+proof text, docstring excluded, whitespace-normalised) w.r.t.
<rev_old>."""
import re, subprocess, sys

DECL = re.compile(r'^(@\[[^\]]*\]\s*)?((?:private|protected|noncomputable|nonrec|partial|unsafe|scoped)\s+)*'
                  r'(theorem|lemma|def|abbrev|instance|structure|inductive|class|example|opaque)\b\s*(\S*)')
TOP = re.compile(r'^(/--|/-!|@\[|namespace\b|end\b|section\b|open\b|variable\b|attribute\b|#|set_option\b|'
                 r'universe\b|noncomputable section|private\s|protected\s|noncomputable\s|theorem\b|lemma\b|def\b|'
                 r'abbrev\b|instance\b|structure\b|inductive\b|class\b|example\b|opaque\b|mutual\b|local\b|scoped\b|'
                 r'initialize\b|macro\b|syntax\b|notation\b|infix|alias\b|export\b|omit\b|include\b|'
                 r'suppress_compilation\b|/-)')

def extents(src):
    lines = src.split('\n')
    n = len(lines)
    # mask comment interiors so that TOP only matches real commands
    in_c, depth, code = False, 0, []
    for l in lines:
        code.append(l if depth == 0 else '')
        i = 0
        while i < len(l):
            if l.startswith('/-', i): depth += 1; i += 2; continue
            if l.startswith('-/', i) and depth: depth -= 1; i += 2; continue
            if depth == 0 and l.startswith('--', i): break
            i += 1
    ns, out = [], []
    starts = []
    anon = {}
    for idx, l in enumerate(lines):
        if not code[idx] and not l.startswith('/-'):
            continue
        m = re.match(r'^namespace\s+(\S+)', l)
        if m: ns.append(m.group(1)); continue
        m = re.match(r'^end\s+(\S+)\s*$', l)
        if m and ns and ns[-1] == m.group(1): ns.pop(); continue
        m = DECL.match(l)
        if m:
            nm = m.group(4)
            if m.group(3) == 'example' or nm.startswith('(') or nm.startswith('{') or nm.startswith('['):
                anon['example'] = anon.get('example', 0) + 1
                nm = f"example#{anon['example']}"
            if m.group(3) == 'instance' and (nm in ('', ':') or nm.startswith(':')):
                anon['instance'] = anon.get('instance', 0) + 1
                nm = f"instance#{anon['instance']}"
            full = nm[7:] if nm.startswith('_root_.') else '.'.join(ns + [nm])
            starts.append((idx, full, m.group(3)))
    for k, (idx, full, kind) in enumerate(starts):
        # leading docstring / attribute lines / `open … in`-style prefixes, in any order
        d = idx
        j = idx - 1
        while j >= 0:
            if lines[j].startswith('@[') and not DECL.match(lines[j]):
                d = j; j -= 1; continue
            if re.match(r'^(open|set_option|omit|include|variable)\b.*\bin\s*$', lines[j]):
                d = j; j -= 1; continue
            if lines[j].rstrip().endswith('-/'):
                jj = j
                while jj >= 0 and not lines[jj].startswith('/--'):
                    jj -= 1
                if jj >= 0 and all(not DECL.match(lines[t]) for t in range(jj, j + 1)) and \
                        all(not lines[t].startswith('/-!') for t in range(jj, j + 1)):
                    d = jj; j = jj - 1; continue
            break
        # end: next top-level command line
        e = n - 1
        for t in range(idx + 1, n):
            if lines[t] and not lines[t][0].isspace() and TOP.match(lines[t]) and code[t] != '' or \
               (lines[t].startswith('/--') or lines[t].startswith('/-!')):
                e = t - 1; break
        while e > idx and not lines[e].strip():
            e -= 1
        out.append(dict(name=full, kind=kind, start=idx + 1, dstart=d + 1, end=e + 1))
    return out

def body_text(src, ext):
    lines = src.split('\n')
    t = '\n'.join(lines[ext['start'] - 1:ext['end']])
    return ' '.join(t.split())

def show(repo, rev, path):
    r = subprocess.run(['git', '-C', repo, 'show', f'{rev}:{path}'], capture_output=True, text=True)
    return r.stdout if r.returncode == 0 else None

if __name__ == '__main__' and sys.argv[1] == 'changes':
    repo, r0, r1, path = sys.argv[2:6]
    old, new = show(repo, r0, path), show(repo, r1, path)
    om = {}
    if old is not None:
        for e in extents(old): om[e['name']] = body_text(old, e)
    for e in extents(new):
        b = body_text(new, e)
        st = 'NEW' if e['name'] not in om else ('SAME' if om[e['name']] == b else 'CHANGED')
        print(f"{path}\t{e['name']}\t{e['kind']}\t{e['dstart']}-{e['start']}-{e['end']}\t{st}")
