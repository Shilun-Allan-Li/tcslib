"""frozen_owned.py (gsw-6a-fills, new; copied for gsw-6b-u12 with one change: control (7), an unlisted new
public declaration, as COMMON C4 asks): C4, the frozen check of the owned files.

usage: frozen_owned.py <repo> <base-rev> <head-rev|WORKTREE> <allow.tsv> <targets.tsv> <file>... [--controls]

For each owned file, the base text and the head text (`git show <rev>:<file>`, or the worktree file when
the head is WORKTREE) are both *masked*, then compared byte for byte:
  * each target named in <targets.tsv> (`file<TAB>source name`, the names as written in the source, from
    base-sorries.txt) keeps its header (keyword through the first `:= by`) and its docstring up to and
    including `**Proof sketch.**`; the proof body (after `:= by` to the next column-0 line other than
    `termination_by`/`decreasing_by`) becomes `<BODY>` and the sketch paragraph (after `**Proof sketch.**` to
    the docstring's `-/`) becomes `<SKETCH>`;
  * in the head only, every inserted private helper block (a column-0 `private theorem|lemma|def` whose name
    is not a private declaration of the base file, with the docstring above it and its body) is removed;
  * <allow.tsv> rows `file<TAB>kind<TAB>base text<TAB>head text` (`\\n` for newlines) license the permitted
    edits: SENTENCE (the module-docstring sentence on admissions), REF (the G6A-F07 reference line) and
    IMPORT (base text empty, head text one `import Mathlib.…` line); each is undone in the head (the head text
    must occur exactly once, the base text exactly once in the base) before the comparison;
  * runs of blank lines are collapsed.
Every remaining difference hunk is reported (difflib opcodes), and every target missing at either side.
PASS = 0 differences.

--controls runs, per file and in memory only, the six controls of the brief, each expected to FAIL with
exactly one difference: (1) one character of a target header; (2) one character of a target's statement
prose (the line just before `**Proof sketch.**`), i.e. a sketch edit spilling into the prose; (3) one
character of a definition body; (4) one character of a reader (a theorem named `*_eq`/`*_iff`/case reader
that is not a target); (5) an unpermitted import line; (6) a deleted target (its whole block; expected count 2: the missing target and its removal hunk). Controls that
do not apply to a file (no definition or no reader) are reported as N/A. The unchanged head must PASS."""
import sys, re, subprocess, difflib

args = [a for a in sys.argv[1:] if a != '--controls']
CONTROLS = '--controls' in sys.argv
repo, base, head, allowf, targf = args[:5]
files = args[5:]


def show(rev, f):
    if rev == 'WORKTREE':
        return open(f'{repo}/{f}', encoding='utf-8').read()
    return subprocess.run(['git', '-C', repo, 'show', f'{rev}:{f}'], capture_output=True,
                          check=True).stdout.decode('utf-8')


allow = []
for l in open(allowf, encoding='utf-8'):
    if l.strip() and not l.startswith('#'):
        f, k, b, h = l.rstrip('\n').split('\t')
        allow.append((f, k, b.replace('\\n', '\n'), h.replace('\\n', '\n')))
targets = {}
for l in open(targf, encoding='utf-8'):
    if l.strip() and not l.startswith('#'):
        f, n = l.rstrip('\n').split('\t')[:2]
        targets.setdefault(f, []).append(n)

DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?((?:private|protected|noncomputable|nonrec)\s+)*'
                  r'(theorem|lemma|def|abbrev|instance|structure)\s+(\S+)')
CONT = re.compile(r'^(termination_by|decreasing_by)\b')


def block_end(L, i):
    """index one past the last line of the declaration starting at line i (body included)."""
    j = i + 1
    while j < len(L):
        l = L[j]
        if l and not l[0].isspace() and not CONT.match(l):
            break
        j += 1
    while j > i + 1 and L[j - 1].strip() == '':
        j -= 1
    return j


def doc_start(L, i):
    """index of the `/--` line of the docstring just above line i (or i if none)."""
    if i > 0 and L[i - 1].rstrip().endswith('-/'):
        k = i - 1
        while k >= 0 and not L[k].startswith('/--'):
            k -= 1
        return k if k >= 0 else i
    return i


def find_decl(L, name, kinds=('theorem', 'lemma')):
    for i, l in enumerate(L):
        m = DECL.match(l)
        if m and m.group(3) == name and m.group(2) in kinds:
            return i
    return None


def mask(text, f, is_head, base_privates):
    notes = []
    if is_head:
        for (af, k, b, h) in allow:
            if af != f:
                continue
            if text.count(h) != 1:
                notes.append(f'ALLOW-MISMATCH {k}: head text found {text.count(h)} times')
                continue
            if k == 'IMPORT':
                if not re.fullmatch(r'import (Mathlib|TCSlib)\.\S+\n', h):
                    notes.append(f'ALLOW-BAD-IMPORT {h!r}')
                    continue
                text = text.replace(h, '', 1)
            else:
                text = text.replace(h, b, 1)
    L = text.split('\n')
    if is_head:  # remove inserted private helper blocks
        i = 0
        while i < len(L):
            m = DECL.match(L[i])
            if m and (m.group(1) or '').strip().startswith('private') and m.group(3) not in base_privates:
                a, e = doc_start(L, i), block_end(L, i)
                del L[a:e]
                i = a
                continue
            i += 1
    missing = []
    for name in targets.get(f, []):
        i = find_decl(L, name)
        if i is None:
            missing.append(name)
            continue
        a, e = doc_start(L, i), block_end(L, i)
        blk = '\n'.join(L[a:e])
        p = blk.find(':= by')
        if p < 0:
            missing.append(name + ' (no := by)')
            continue
        hdr = blk[:p + len(':= by')] + ' <BODY>'
        q = hdr.find('**Proof sketch.**')
        if q >= 0:
            r = hdr.find('-/', q)
            hdr = hdr[:q + len('**Proof sketch.**')] + ' <SKETCH> ' + hdr[r:]
        L[a:e] = hdr.split('\n')
    out = re.sub(r'\n\s*\n(\s*\n)+', '\n\n', '\n'.join(L))
    return out, missing, notes


def privates(text):
    return {m.group(3) for l in text.split('\n') if (m := DECL.match(l))
            and (m.group(1) or '').strip().startswith('private')}


def compare(f, btext, htext, quiet=False):
    bp = privates(btext)
    mb, missb, _ = mask(btext, f, False, bp)
    mh, missh, notes = mask(htext, f, True, bp)
    ops = [o for o in difflib.SequenceMatcher(None, mb.split('\n'), mh.split('\n'),
                                              autojunk=False).get_opcodes() if o[0] != 'equal']
    n = len(ops) + len(missb) + len(missh) + len(notes)
    if not quiet:
        for o in ops:
            bl = mb.split('\n')[o[1]:o[2]]
            hl = mh.split('\n')[o[3]:o[4]]
            print(f'  DIFF {o[0]} base[{o[1]}:{o[2]}] head[{o[3]}:{o[4]}]')
            for x in bl[:6]:
                print('    - ' + x)
            for x in hl[:6]:
                print('    + ' + x)
        for x in missb:
            print(f'  MISSING-AT-BASE {x}')
        for x in missh:
            print(f'  MISSING-AT-HEAD {x}')
        for x in notes:
            print(f'  {x}')
    return n


def edit_char(text, lineidx):
    L = text.split('\n')
    l = L[lineidx]
    k = len(l.rstrip()) - 1
    L[lineidx] = l[:k] + ('X' if l[k] != 'X' else 'Y') + l[k + 1:]
    return '\n'.join(L)


total = 0
for f in files:
    b, h = show(base, f), show(head, f)
    n = compare(f, b, h, quiet=True)
    print(f'== {f}: {"PASS" if n == 0 else "FAIL"} differences={n}')
    if n:
        compare(f, b, h)
    total += n
    if not CONTROLS:
        continue
    L = h.split('\n')
    t0 = targets[f][0]
    ti = find_decl(L, t0)
    ctrl = {}
    ctrl['1-header'] = edit_char(h, ti)
    ps = next((k for k in range(ti, 0, -1) if L[k].startswith('**Proof sketch.**')), None)
    pr = ps - 1 if ps else None
    while pr is not None and pr > 0 and not L[pr].strip():
        pr -= 1
    ctrl['2-prose'] = edit_char(h, pr) if pr else None
    di = next((k for k, l in enumerate(L) if (m := DECL.match(l)) and m.group(2) == 'def'
               and not (m.group(1) or '').startswith('private')), None)
    ctrl['3-def-body'] = edit_char(h, block_end(L, di) - 1) if di is not None else None
    tg = set(targets[f])
    ri = next((k for k, l in enumerate(L) if (m := DECL.match(l)) and m.group(2) == 'theorem'
               and m.group(3) not in tg and not (m.group(1) or '').startswith('private')
               and re.search(r'(_eq|_iff|_zero|_succ|_nil|_singleton|_cons_cons|_cons_cons_cons)$',
                             m.group(3))), None)
    ctrl['4-reader'] = edit_char(h, block_end(L, ri) - 1) if ri is not None else None
    ii = max(k for k, l in enumerate(L) if l.startswith('import '))
    ctrl['5-import'] = '\n'.join(L[:ii + 1] + ['import Mathlib.Data.Real.Basic'] + L[ii + 1:])
    a, e = doc_start(L, ti), block_end(L, ti)
    ctrl['6-deleted-target'] = '\n'.join(L[:a] + L[e:])
    # (7) gsw-6b-u12: an unlisted new public declaration, inserted before the first target
    ctrl['7-new-public'] = '\n'.join(L[:a] + ['/-- Control. -/', 'theorem frozenControlNewPublic : True :=',
                                               '  trivial', ''] + L[a:])
    for k, v in ctrl.items():
        if v is None:
            print(f'   CONTROL {k}: N/A')
            continue
        c = compare(f, b, v, quiet=True)
        want = 2 if k == '6-deleted-target' else 1
        print(f'   CONTROL {k}: {"FAIL" if c else "PASS"} differences={c} '
              f'(expected FAIL {want}: {"OK" if c == want else "UNEXPECTED"})')
print(f'RESULT files={len(files)} differences={total} {"PASS" if total == 0 else "FAIL"}')
