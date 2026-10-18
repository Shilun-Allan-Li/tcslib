"""MIG-1 statement gate: code identity of the gate unit against the library sources.

Usage: python3 -I identity.py <worktree> <unit.lean> <manifest.json> [<more unit files> ...]

Read-only; standard library only. Declarations are located with scripts/decls.py in the source
file and in the unit (by name; a name must occur once in the unit). Comments and docstrings are
removed and all whitespace is collapsed before comparing. `private` is dropped and `lemma` is
read as `theorem` on both sides, so that a promotion (private -> public, same text) compares
equal. The rename map named by an entry (scripts/renames.json) is applied to the source text
token by token. Kinds:

* verbatim   -- the whole declaration (statement and body) is identical.
* statement  -- the statements (up to the `:=` opening the proof) are identical, and the gate
                body is `by sorry` (a sorried spec stated verbatim from a proved private lemma).
* transform  -- as `statement`, after the listed literal substitutions on the source statement.
* binders    -- the gate statement's binders (before its statement colon) equal the source's
                (after the listed substitutions); the conclusions are new.
* substrings -- every nonblank line of the gate declaration's body occurs, whitespace-collapsed,
                as a substring of the source declaration, except the lines listed as `allow`.

Every entry prints PASS or FAIL with the reason; the exit code is the number of failures.
"""
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from decls import scan  # noqa: E402

FILES = {
    'Composition': 'TCSlib/Complexity/TuringMachine/Composition.lean',
    'Primitives': 'TCSlib/Complexity/TuringMachine/Build/Primitives.lean',
    'Loop': 'TCSlib/Complexity/TuringMachine/Build/Loop.lean',
    'Wrappers': 'TCSlib/Complexity/TuringMachine/Build/Wrappers.lean',
    'TimeConstructible': 'TCSlib/Complexity/ClassP/TimeConstructible.lean',
    'Encoding': 'TCSlib/Complexity/TuringMachine/Encoding.lean',
    'Simulation': 'TCSlib/Complexity/TuringMachine/Simulation.lean',
    'Catalog': 'TCSlib/Complexity/TuringMachine/Build/Catalog.lean',
    'H2Draft': 'audits/evidence/h2/StepBlockDraft.lean.txt',
}
IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_'!?]*(?:\.[A-Za-z_][A-Za-z0-9_'!?]*)*")


def strip_comments(text):
    out, depth, j = [], 0, 0
    while j < len(text):
        if depth > 0:
            if text.startswith('/-', j):
                depth += 1; j += 2; continue
            if text.startswith('-/', j):
                depth -= 1; j += 2; continue
            j += 1; continue
        if text.startswith('/-', j):
            depth += 1; j += 2; continue
        if text.startswith('--', j):
            k = text.find('\n', j)
            j = len(text) if k < 0 else k
            continue
        out.append(text[j]); j += 1
    return ''.join(out)


def norm(text):
    t = ' '.join(strip_comments(text).split())
    t = re.sub(r'^private ', '', t)
    t = re.sub(r'^lemma ', 'theorem ', t)
    t = re.sub(r'^noncomputable ', 'noncomputable ', t)
    return t


def rename(text, mapping):
    def sub(m):
        return '.'.join(mapping.get(p, p) for p in m.group(0).split('.'))
    return IDENT.sub(sub, text)


def decl_text(path, name, cache):
    if path not in cache:
        ds, lines = scan(path)
        cache[path] = (ds, lines)
    ds, lines = cache[path]
    hit = [d for d in ds if d['name'] == name]
    if len(hit) != 1:
        raise KeyError(f'{name}: {len(hit)} declarations in {os.path.basename(path)}')
    d = hit[0]
    return '\n'.join(lines[d['line'] - 1:d['end']]), d['line']


def split_stmt(t):
    """(statement, body) at the `:=` that opens the proof (whitespace-collapsed text)."""
    depth = 0
    cands = []
    for i, ch in enumerate(t):
        if ch in '([{⟨':
            depth += 1
        elif ch in ')]}⟩':
            depth -= 1
        elif depth == 0 and t.startswith(':=', i):
            cands.append(i)
    for i in cands:
        if t.startswith(':= by', i):
            return t[:i].strip(), t[i:].strip()
    i = cands[0]
    return t[:i].strip(), t[i:].strip()


def first_colon(stmt):
    """The statement colon: the first top-level `:` after the binders."""
    depth = 0
    for i, ch in enumerate(stmt):
        if ch in '([{⟨':
            depth += 1
        elif ch in ')]}⟩':
            depth -= 1
        elif depth == 0 and ch == ':' and not stmt.startswith(':=', i):
            return i
    return len(stmt)


def main():
    wt, unit, manifest = sys.argv[1], sys.argv[2], sys.argv[3]
    units = [unit] + sys.argv[4:]
    renames = json.load(open(os.path.join(HERE, 'renames.json'), encoding='utf-8'))
    entries = json.load(open(manifest, encoding='utf-8'))
    cache = {}
    fails = 0
    counts = {}
    for e in entries:
        kind = e['kind']
        counts[kind] = counts.get(kind, 0) + 1
        try:
            g = None
            for u in units:
                try:
                    g, gline = decl_text(u, e['gate'], cache)
                    gfile = os.path.basename(u)
                    break
                except KeyError:
                    continue
            if g is None:
                raise KeyError(f"{e['gate']}: not found once in the unit files")
            src_path = os.path.join(wt, FILES[e['file']])
            s, sline = decl_text(src_path, e['source'], cache)
            mapping = renames.get(e.get('rename', ''), {})
            s = rename(s, mapping)
            gn, sn = norm(g), norm(s)
            for a, b in e.get('subst', []):
                if a not in sn:
                    raise ValueError(f'substitution source not found: {a!r}')
                sn = sn.replace(a, b)
            ok, why = True, ''
            if kind == 'verbatim':
                ok = gn == sn
                why = '' if ok else 'declarations differ'
            elif kind in ('statement', 'transform'):
                gs, gb = split_stmt(gn)
                ss, _ = split_stmt(sn)
                ok = gs == ss and gb in (':= by sorry', ':= sorry')
                why = '' if ok else ('statements differ' if gs != ss else f'gate body {gb!r}')
            elif kind == 'binders':
                gs, _ = split_stmt(gn)
                ss, _ = split_stmt(sn)
                gb, sb = gs[:first_colon(gs)].strip(), ss[:first_colon(ss)].strip()
                extra = e.get('gate_extra', '')
                # compare without the declaration names
                gb2 = gb.split(' ', 2)[2] if gb.count(' ') >= 2 else gb
                sb2 = sb.split(' ', 2)[2] if sb.count(' ') >= 2 else sb
                ok = gb2 == (sb2 + (' ' + extra if extra else '')).strip()
                why = '' if ok else 'binders differ'
            elif kind == 'substrings':
                body = strip_comments(g).split('\n')
                allow = [' '.join(a.split()) for a in e.get('allow', [])]
                flat = ' '.join(strip_comments(s).split())
                miss = []
                for l in body[1:]:
                    ln = ' '.join(l.split())
                    if ln and ln not in flat and ln not in allow:
                        miss.append(ln)
                ok = not miss
                why = '' if ok else 'not in source: ' + ' | '.join(miss)
            else:
                ok, why = False, f'unknown kind {kind}'
        except (KeyError, ValueError) as ex:
            ok, why = False, str(ex)
            gfile = gline = sline = '?'
        if not ok:
            fails += 1
            if os.environ.get('IDENTITY_DEBUG') and kind in ('verbatim', 'statement', 'transform'):
                print('   gate  :', gn[:2000])
                print('   source:', sn[:2000])
        print(f"{'PASS' if ok else 'FAIL'} {kind:10s} {e['gate']} ({gfile}:{gline}) <- "
              f"{e['file']}:{sline} {e['source']}"
              f"{' [rename ' + e['rename'] + ']' if e.get('rename') else ''}"
              f"{' [' + str(len(e.get('subst', []))) + ' substitutions]' if e.get('subst') else ''}"
              f"{'  -- ' + why if why else ''}")
    print(f"entries: {len(entries)}; by kind: {counts}; failures: {fails}")
    sys.exit(fails)


if __name__ == '__main__':
    main()
