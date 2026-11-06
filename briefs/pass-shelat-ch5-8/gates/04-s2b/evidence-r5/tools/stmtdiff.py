"""stmtdiff.py <worktree> <rev_old> <rev_new> <files.txt>: for every declaration of the files at
<rev_new>, compare its statement (text from the declaration keyword to the top-level `:=`, `where`
or `|`, whitespace-normalised) and its docstring with <rev_old>. Prints ADDED / REMOVED / statement
CHANGED / docstring CHANGED rows; a declaration whose statement and docstring agree is not printed."""
import os, re, subprocess, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import declx
WT, R0, R1, FILES = sys.argv[1:5]

def show(rev, p):
    r = subprocess.run(['git', '-C', WT, 'show', f'{rev}:{p}'], capture_output=True, text=True)
    return r.stdout if r.returncode == 0 else None

def parts(src, e):
    lines = src.split('\n')
    doc = ' '.join('\n'.join(lines[e['dstart'] - 1:e['start'] - 1]).split())
    body = '\n'.join(lines[e['start'] - 1:e['end']])
    depth, i, cut = 0, 0, len(body)
    while i < len(body):
        c = body[i]
        if c in '([{⟨': depth += 1
        elif c in ')]}⟩': depth -= 1
        elif depth == 0 and (body.startswith(':=', i) or re.match(r'\swhere\b', body[i:i + 7])
                             or (c == '|' and body[:i].endswith(('\n', '\n  ')))):
            cut = i; break
        i += 1
    return doc, ' '.join(body[:cut].split())

for p in [l.strip() for l in open(FILES) if l.strip()]:
    a, b = show(R0, p), show(R1, p)
    if b is None: continue
    ea = {e['name']: e for e in declx.extents(a)} if a else {}
    eb = {e['name']: e for e in declx.extents(b)}
    for n, e in eb.items():
        if n not in ea: print(f"ADDED\t{p}\t{n}"); continue
        da, sa = parts(a, ea[n]); db, sb = parts(b, e)
        if sa != sb: print(f"STATEMENT CHANGED\t{p}\t{n}\n  old: {sa}\n  new: {sb}")
        if da != db: print(f"DOCSTRING CHANGED\t{p}\t{n}")
    for n in ea:
        if n not in eb: print(f"REMOVED\t{p}\t{n}")
