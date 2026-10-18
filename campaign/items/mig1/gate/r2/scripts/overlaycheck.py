"""Checks of the round-2 Loop overlay and of the retarget checks. Read-only.

Usage:
  python3 -I overlaycheck.py overlay <overlay.out> <baseline.out> <n prints>
      0 errors; 0 `declaration uses 'sorry'` warnings; the warning multiset (message and the
      line after it, locations dropped) equal to the baseline's (the tip's Loop.lean
      elaborated alone); exactly <n prints> `#print axioms` results, none with `sorryAx` or an
      axiom other than propext, Classical.choice, Quot.sound.
  python3 -I overlaycheck.py retarget <r2.lean> <r2.out> <tip.lean> <tip.out> <name> ...
      the r2 file has 0 errors; the tip file has errors exactly inside the examples restating
      the named copies (one or more errors each), and nowhere else.
  python3 -I overlaycheck.py diff <tip Loop.lean> <part1.lean> <added> <removed>
      the unified diff of part 1 against the tip adds and removes exactly the given numbers of
      lines, and every added line has at most 100 characters.
  python3 -I overlaycheck.py stmts <before.lean> <after.lean>
      declarations whose statement changed (cut at the proof's `:=`, bracket depth zero, not a
      `let`/`have` binder; docstrings and comments removed), added and removed declarations,
      and body-only changes: the private-statement-change list of the edit.
Each mode prints its findings and `RESULT: PASS` or `RESULT: FAIL`; exit code 0 or 1.
"""
import difflib
import re
import sys
from collections import Counter

STD = {'propext', 'Classical.choice', 'Quot.sound'}


def warnings(t):
    out, lines = [], t.split('\n')
    for i, l in enumerate(lines):
        m = re.match(r'^.*?\.lean:\d+:\d+: warning: (.*)$', l)
        if m:
            nxt = lines[i + 1] if i + 1 < len(lines) else ''
            out.append((m.group(1), nxt))
    return Counter(out)


def overlay(args):
    t, b, n = open(args[0], encoding='utf-8').read(), open(args[1], encoding='utf-8').read(), int(args[2])
    ok = True
    errs = len(re.findall(r'\.lean:\d+:\d+: error', t))
    sor = t.count("declaration uses 'sorry'")
    print(f'errors {errs}; sorry warnings {sor}')
    ok &= errs == 0 and sor == 0
    wa, wb = warnings(t), warnings(b)
    print(f'warnings {sum(wa.values())} (baseline {sum(wb.values())}); multiset equal: {wa == wb}')
    for k in (wa - wb):
        print('  extra warning:', k)
    for k in (wb - wa):
        print('  missing warning:', k)
    ok &= wa == wb
    items = re.findall(r"'([^']+)' (depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",
                       t, re.S)
    bad = []
    for name, _, ax in items:
        axs = {a.strip() for a in ax.replace('\n', ' ').split(',') if a.strip()}
        flag = 'BAD' if axs - STD else 'ok '
        if axs - STD:
            bad.append(name)
        print(f'  {flag} {name}: {", ".join(sorted(axs)) or "(none)"}')
    print(f'axiom prints {len(items)} (expected {n}); with sorryAx or a nonstandard axiom: {bad}')
    ok &= len(items) == n and not bad
    return ok


def example_of(lean_lines, n):
    for i in range(n - 1, -1, -1):
        m = re.match(r'^/-- Restates the copy (\S+) ', lean_lines[i])
        if m:
            return m.group(1)
        if lean_lines[i].startswith('/-! Retarget checks'):
            return None
    return None


def retarget(args):
    r2l, r2o, tl, to, names = args[0], args[1], args[2], args[3], set(args[4:])
    ok = True
    e2 = re.findall(r'\.lean:(\d+):\d+: error', open(r2o, encoding='utf-8').read())
    print(f'r2 file errors: {len(e2)}')
    ok &= not e2
    lines = open(tl, encoding='utf-8').read().split('\n')
    et = [int(x) for x in re.findall(r'\.lean:(\d+):\d+: error', open(to, encoding='utf-8').read())]
    where = Counter(example_of(lines, n) for n in et)
    print(f'tip file errors: {len(et)}, by restated copy: {dict(where)}')
    ok &= set(where) == names
    return ok


def diff(args):
    a = open(args[0], encoding='utf-8').read().split('\n')
    b = open(args[1], encoding='utf-8').read().split('\n')
    d = list(difflib.unified_diff(a, b, lineterm=''))
    add = [l[1:] for l in d if l.startswith('+') and not l.startswith('+++')]
    rem = [l for l in d if l.startswith('-') and not l.startswith('---')]
    wide = [l for l in add if len(l) > 100]
    print(f'added {len(add)} (expected {args[2]}); removed {len(rem)} (expected {args[3]}); '
          f'added lines over 100 characters: {len(wide)}; hunks: {sum(1 for l in d if l.startswith("@@"))}')
    return len(add) == int(args[2]) and len(rem) == int(args[3]) and not wide


KW = r'(theorem|lemma|def|abbrev|instance|structure|inductive|class)'
DECL = re.compile(r'^(@\[[^\]]*\]\s*)*((private|protected|noncomputable|nonrec|partial|unsafe)\s+)*'
                  + KW + r'\s+([^\s(:{\[]+)')
LET = re.compile(r'\b(let|have)\s+[^\s:=()]+(\s*:[^=]*)?\s*$')


def strip(text):
    out, depth, i = [], 0, 0
    while i < len(text):
        if text.startswith('/-', i):
            depth += 1; i += 2; continue
        if depth and text.startswith('-/', i):
            depth -= 1; i += 2; continue
        if not depth and text.startswith('--', i):
            j = text.find('\n', i)
            i = len(text) if j < 0 else j
            continue
        if not depth:
            out.append(text[i])
        i += 1
    return ''.join(out)


def decls(path):
    lines = strip(open(path, encoding='utf-8').read()).split('\n')
    res, cur = {}, None
    for i, l in enumerate(lines + ['end']):
        m = DECL.match(l)
        top = m or re.match(r'^(end\b|namespace\b|section\b|open\b|variable\b|set_option\b|#|'
                            r'attribute\b|theorem|lemma|example)', l)
        if top and cur:
            res[cur[0]] = (cur[1], '\n'.join(lines[cur[2]:i]).strip())
            cur = None
        if m:
            cur = (m.group(5), 'private' in (m.group(2) or ''), i)
    return res


def stmt(code):
    depth = 0
    for i, ch in enumerate(code):
        if ch in '([{⟨':
            depth += 1
        elif ch in ')]}⟩':
            depth -= 1
        elif depth == 0 and code.startswith(':=', i) and not LET.search(code[:i]):
            return ' '.join(code[:i].split())
    return ' '.join(code.split())


def stmts(args):
    A, B = decls(args[0]), decls(args[1])
    changed = sorted(('private ' if A[n][0] else 'public ') + n for n in A if n in B
                     and stmt(A[n][1]) != stmt(B[n][1]))
    body = sorted(('private ' if A[n][0] else 'public ') + n for n in A if n in B
                  and stmt(A[n][1]) == stmt(B[n][1]) and ' '.join(A[n][1].split()) != ' '.join(B[n][1].split()))
    print(f'declarations before {len(A)}, after {len(B)}')
    print('added:', sorted(('private ' if B[n][0] else 'public ') + n for n in B if n not in A))
    print('removed:', sorted(n for n in A if n not in B))
    print('STATEMENT CHANGED:', changed)
    print('body-only changes:', body)
    return True


if __name__ == '__main__':
    ok = {'overlay': overlay, 'retarget': retarget, 'diff': diff, 'stmts': stmts}[sys.argv[1]](sys.argv[2:])
    print('RESULT:', 'PASS' if ok else 'FAIL')
    sys.exit(0 if ok else 1)
