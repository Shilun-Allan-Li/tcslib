r"""frozen_check.py -- frozen-facade check (C7) of fill ef-r23-regev. Run with `python3 -I`; reads git objects only.

  python3 -I frozen_check.py [--repo R] [--head REV] [--allow JSON] [--final] [--out DIR]   check + diff-stat
  python3 -I frozen_check.py [--repo R] [--head REV] [--allow JSON] --controls [--out DIR]  mutation controls

ORIGIN / ADAPTATIONS (tools-agent, sub-agent of fill ef-r23-regev, 2026-11-18). Adapted from
/home/user/ef-r23/tools/bb1m-evidence/headers/frozen/frozen_check_bb1m.py + frozen_controls_bb1m.py (fill
bb1-machine), whose method is kept: revert exactly the permitted edits in the head file and require the result to
equal the base file BYTE FOR BYTE; plus controls that mutate the head and must be caught. Adaptations:
  (1) the permitted edits are data, not code: an allow-list JSON (frozen-allow.json) gives, per changed existing
      file (the three facades), insertions placed directly after an exact base anchor line, each with exact
      `lines` or a first-line `pattern` + `max_lines` (for the series-3 facade whose wording is not fixed yet);
      kind `import` (import lines only) or `bullet` (inside the head's `## Contents` section; continuation lines
      indented by two spaces);
  (2) besides the byte-equality verdict, a line-by-line difflib comparison base vs head reports every hunk that
      is not a permitted insertion as ONE difference (a one-character change on one line = exactly one
      difference), and every permitted insertion absent from the head as MISSING;
  (3) declaration-by-declaration: the bb1m clash parser (clash/clash_core_bb1m.py, parse_decls) lists the
      declarations of base and head; the lists must be equal (the facades declare nothing);
  (4) head lines added by the fill must be at most `max_width` (100) characters;
  (5) `git diff --name-status <base> <head>` must list only the six allowed paths (EXTRA paths fail);
  (6) a facade unchanged at the head is PENDING (its insertions are absent) unless --final, where it FAILs;
  (7) controls per facade (the head file, or for a PENDING facade a synthetic head built from the allow-list,
      sample text for a pattern): M0 unmutated -> PASS, 0 differences; M1 one character altered in a base line
      away from the insertions -> exactly 1 difference, 0 missing; M2 one character altered inside the bullet ->
      1 difference + 1 missing; M3 one extra line elsewhere -> exactly 1 difference; M4 the import dropped ->
      0 differences + 1 missing; M5 the import moved to the start of the import block -> 1 difference + 1 missing;
      M6 one base line deleted -> exactly 1 difference; M7 a declaration added -> differences >= 1 and the
      declaration lists differ.
Exit status 0 iff PASS (check) or ALL_CONTROLS_OK True (controls).
"""
import difflib, importlib.util, json, os, re, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = '/home/user/ef-r23/repo'


def load_parser():
    sys.dont_write_bytecode = True
    p = os.path.join(os.path.dirname(HERE), 'clash', 'clash_core_bb1m.py')
    spec = importlib.util.spec_from_file_location('clash_core_bb1m', p)
    m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
    return m


cs = load_parser()


def git(repo, *a):
    return subprocess.run(['git', '-C', repo] + list(a), capture_output=True, check=True).stdout


def show(repo, rev, path):
    r = subprocess.run(['git', '-C', repo, 'show', f'{rev}:{path}'], capture_output=True)
    return r.stdout.decode('utf-8') if r.returncode == 0 else None


def contents_span(lines):
    """Indices [a, b) of the lines strictly inside the `## Contents` section (to the next `## ` or `-/`)."""
    a = [i for i, l in enumerate(lines) if l.rstrip() == '## Contents']
    if len(a) != 1:
        return None
    b = a[0] + 1
    while b < len(lines) and not lines[b].startswith('## ') and lines[b].strip() != '-/':
        b += 1
    return a[0] + 1, b


def match_ins(ins, block):
    """Length of the prefix of `block` that matches insertion `ins`, or 0."""
    if 'lines' in ins:
        n = len(ins['lines'])
        return n if block[:n] == ins['lines'] else 0
    if not block or not re.search(ins['pattern'], block[0]):
        return 0
    n = 1
    while n < len(block) and n < ins.get('max_lines', 1) and block[n].startswith('  ') and not block[n].lstrip().startswith('* '):
        n += 1
    return n


def check_file(path, base, head, allow, max_width):
    """Returns dict(differences=[...], missing=[...], used=[...], byte_equal=bool, decls_equal=bool, notes=[...])."""
    B, H = base.split('\n'), head.split('\n')
    res = dict(path=path, differences=[], missing=[], used=[], notes=[])
    anchors = {}
    for ins in allow:
        idx = [i for i, l in enumerate(B) if l == ins['after']]
        if len(idx) != 1:
            res['differences'].append(f'ALLOW-LIST anchor for {ins["id"]} occurs {len(idx)} times in the base')
        else:
            anchors[ins['id']] = idx[0]
    span = contents_span(H)
    sm = difflib.SequenceMatcher(None, B, H, autojunk=False)
    keep = []  # head line indices that are reverted (removed)
    used = set()
    for op, i1, i2, j1, j2 in sm.get_opcodes():
        if op == 'equal':
            continue
        if op == 'insert':
            # try to cover H[j1:j2] by permitted insertions anchored after base line i1-1
            # (difflib may shift an insertion within a run of equal lines; anchors are checked on the base index)
            j, ok, cov = j1, True, []
            while j < j2:
                hit = None
                for ins in allow:
                    if ins['id'] in used or anchors.get(ins['id']) != i1 - 1:
                        continue
                    n = match_ins(ins, H[j:j2])
                    if n:
                        hit = (ins, n); break
                if not hit:
                    ok = False; break
                ins, n = hit
                if ins['kind'] == 'import' and not all(l.startswith('import ') for l in H[j:j + n]):
                    ok = False; break
                if ins['kind'] == 'bullet' and not (span and span[0] <= j and j + n <= span[1]):
                    ok = False; break
                cov.append((ins['id'], j, n)); j += n
            if ok:
                for iid, jj, n in cov:
                    used.add(iid); keep.extend(range(jj, jj + n))
                    for k in range(jj, jj + n):
                        if len(H[k]) > max_width:
                            res['differences'].append(f'line {k + 1}: inserted line longer than {max_width} characters')
                continue
        res['differences'].append(
            f'{op} base {i1 + 1}-{i2} -> head {j1 + 1}-{j2}: '
            + ' | '.join([f'-{l!r}' for l in B[i1:i2]] + [f'+{l!r}' for l in H[j1:j2]])[:400])
    for ins in allow:
        if ins['id'] not in used:
            res['missing'].append(ins['id'])
    res['used'] = sorted(used)
    reverted = '\n'.join(l for k, l in enumerate(H) if k not in set(keep))
    res['byte_equal'] = reverted == base
    db = [(d['full'], d['kind']) for d in cs.parse_decls(base)]
    dh = [(d['full'], d['kind']) for d in cs.parse_decls(head)]
    res['decls_equal'] = db == dh
    res['decls'] = (len(db), len(dh))
    if not res['decls_equal']:
        res['notes'].append(f'declarations differ: base {db} head {dh}')
    return res


def verdict(r, final):
    if r['differences'] or not r['byte_equal'] or not r['decls_equal']:
        return 'FAIL'
    if r['missing']:
        return 'FAIL' if (final or r['used']) else 'PENDING'
    return 'PASS'


def fmt(r, final):
    v = verdict(r, final)
    s = [f'{v} {r["path"]}: differences {len(r["differences"])}, missing {r["missing"] or 0}, '
         f'insertions used {r["used"]}, reverted==base {r["byte_equal"]}, declarations base/head {r["decls"]} '
         f'equal {r["decls_equal"]}']
    s += ['    DIFF ' + d for d in r['differences']] + ['    NOTE ' + n for n in r['notes']]
    return v, s


def run_check(repo, head, allow, final):
    base = allow['base']
    hc = git(repo, 'rev-parse', head + '^{commit}').decode().strip()
    out, ok = [f'frozen_check.py base {base} head {hc}' + (' (final)' if final else '')], True
    ns = git(repo, 'diff', '--no-renames', '--name-status', base, hc).decode().splitlines()
    stat = git(repo, 'diff', '--stat=200', base, hc).decode().rstrip('\n').splitlines()
    out.append('git diff --stat %s %s:' % (base[:12], hc[:12]))
    out += ['    ' + l for l in stat]
    extra = [l for l in ns if l.split('\t')[-1] not in allow['allowed_paths']]
    changed = [l.split('\t')[-1] for l in ns]
    out.append(f'DIFF-STAT: {len(ns)} changed path(s); outside the six allowed: {len(extra)}'
               + (' ' + '; '.join(extra) if extra else ''))
    ok &= not extra
    for path in allow['allowed_paths']:
        st = [l.split('\t')[0] for l in ns if l.split('\t')[-1] == path]
        out.append(f'  allowed {path}: {st[0] if st else "unchanged"}'
                   + (' (facade)' if path in allow['facades'] else ''))
        if st and st[0] not in ('A', 'M'):
            ok = False; out.append(f'  FAIL unexpected status {st[0]} for {path}')
        if path in allow['facades'] and st and st[0] != 'M':
            ok = False; out.append(f'  FAIL facade {path} must be Modified, not {st[0]}')
        if path not in allow['facades'] and st and st[0] != 'A':
            ok = False; out.append(f'  FAIL new module {path} must be Added, not {st[0]}')
    for path, ins in allow['facades'].items():
        b, h = show(repo, base, path), show(repo, hc, path)
        if b is None or h is None:
            ok = False; out.append(f'FAIL {path}: missing at base or head'); continue
        r = check_file(path, b, h, ins, allow.get('max_width', 100))
        v, s = fmt(r, final)
        ok &= v in ('PASS', 'PENDING')
        out += s
    out.append(f'RESULT {"PASS" if ok else "FAIL"}')
    return ok, out


def synth_head(base, ins_list):
    """Apply the allow-list insertions to the base (pattern insertions get a sample bullet)."""
    B = base.split('\n')
    for ins in sorted(ins_list, key=lambda x: -B.index(x['after'])):
        i = B.index(ins['after'])
        lines = ins.get('lines') or ['* `Asymptotic`: SAMPLE bullet text for the controls (synthetic),', '  second line.']
        B = B[:i + 1] + lines + B[i + 1:]
    return '\n'.join(B)


def run_controls(repo, head, allow):
    base_rev = allow['base']; hc = git(repo, 'rev-parse', head + '^{commit}').decode().strip()
    out, ok_all = [f'frozen controls base {base_rev} head {hc}'], True
    mw = allow.get('max_width', 100)
    for path, ins in allow['facades'].items():
        b, h = show(repo, base_rev, path), show(repo, hc, path)
        src = 'head'
        if h == b:
            h, src = synth_head(b, ins), 'SYNTHETIC head (facade unchanged at head; insertions applied from the allow-list)'
        out.append(f'== {path} [{src}]')
        H = h.split('\n')
        imp = next(x for x in ins if x['kind'] == 'import'); bul = next(x for x in ins if x['kind'] == 'bullet')
        ins_lines = set()
        for x in ins:
            i = H.index(x['after']); n = match_ins(x, H[i + 1:]); ins_lines.update(range(i + 1, i + 1 + n))
        far = [k for k, l in enumerate(H) if k not in ins_lines and all(abs(k - m) > 2 for m in ins_lines)
               and re.search(r'[a-z]', l) and not l.startswith('import ') and l.count('\n') == 0]
        m1 = far[len(far) // 2]
        bline = sorted(x for x in ins_lines if H[x].startswith('* '))[-1]
        ic = H.index(imp['lines'][0]) if 'lines' in imp else None
        first_imp = min(k for k, l in enumerate(H) if l.startswith('import '))
        def alt(L, k):
            L = list(L); c = next(i for i, ch in enumerate(L[k]) if ch.isalpha()); L[k] = L[k][:c] + ('X' if L[k][c] != 'X' else 'Y') + L[k][c + 1:]; return L
        cases = {
            'M0 unmutated': (H, dict(diff=0, missing=0, verdict='PASS')),
            f'M1 one character altered at line {m1 + 1}': (alt(H, m1), dict(diff=1, missing=0)),
            f'M2 one character altered in the bullet line {bline + 1}': (alt(H, bline), dict(diff=1, missing=1)),
            f'M3 one extra line after line {m1 + 1}': (H[:m1 + 1] + ['-- extra'] + H[m1 + 1:], dict(diff=1, missing=0)),
            'M4 the import dropped': ([l for k, l in enumerate(H) if k != ic], dict(diff=0, missing=1)),
            'M5 the import moved to the start of the import block':
                (H[:first_imp] + [H[ic]] + [l for k, l in enumerate(H) if k >= first_imp and k != ic], dict(diff=1, missing=1)),
            f'M6 base line {m1 + 1} deleted': (H[:m1] + H[m1 + 1:], dict(diff=1, missing=0)),
            'M7 a declaration added at the end': (H + ['theorem frozenCtlExtra : True := trivial', ''], dict(diff_min=1, decls_equal=False)),
        }
        if ic is None or ic == first_imp:
            del cases['M5 the import moved to the start of the import block']
            out.append('    (M5 skipped: the permitted import is already first or is a pattern)')
        for name, (L, exp) in cases.items():
            r = check_file(path, b, '\n'.join(L), ins, mw)
            v = verdict(r, True)
            got = dict(diff=len(r['differences']), missing=len(r['missing']), verdict=v, decls_equal=r['decls_equal'])
            good = all((got['diff'] >= val) if k == 'diff_min' else got[k] == val for k, val in exp.items())
            if name != 'M0 unmutated':
                good = good and v == 'FAIL'
            ok_all &= good
            out.append(f'  {"OK " if good else "BAD"} {name}: verdict {v}, differences {got["diff"]}, missing {got["missing"]}, '
                       f'decls_equal {got["decls_equal"]} (expected {exp})')
            for d in r['differences'][:3]:
                out.append('        ' + d[:200])
    out.append(f'ALL_CONTROLS_OK {ok_all}')
    return ok_all, out


def main(argv):
    a = {'--repo': REPO, '--head': 'HEAD', '--allow': os.path.join(HERE, 'frozen-allow.json'), '--out': None}
    flags = set(); i = 1
    while i < len(argv):
        if argv[i] in ('--final', '--controls'):
            flags.add(argv[i]); i += 1
        elif argv[i] in a and i + 1 < len(argv):
            a[argv[i]] = argv[i + 1]; i += 2
        else:
            print(__doc__); return 2
    allow = json.load(open(a['--allow'], encoding='utf-8'))
    if '--controls' in flags:
        ok, out = run_controls(a['--repo'], a['--head'], allow); name = 'frozen-controls.out'
    else:
        ok, out = run_check(a['--repo'], a['--head'], allow, '--final' in flags); name = 'frozen-check.out'
    print('\n'.join(out))
    if a['--out']:
        os.makedirs(a['--out'], exist_ok=True)
        open(os.path.join(a['--out'], name), 'w', encoding='utf-8').write('\n'.join(out) + '\n')
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main(sys.argv))
