"""clash_scan.py -- name-clash scan for fill ef-r23-regev (run with `python3 -I`; reads git objects only, no Lean).

ORIGIN / ADAPTATIONS (tools-agent, sub-agent of fill ef-r23-regev, 2026-11-18). Adapted from
/home/user/ef-r23/tools/bb1m-evidence/clash/clash_scan.py and clash_controls.py (fill bb1-machine). The bb1m parser
core (comment/string blanking, namespace/section/mutual/end resolution incl. dotted and partial `end`, dotted
declaration names, `_root_`, `git cat-file --batch` index of every .lean file under TCSlib/ and audits/) is used
VERBATIM from clash_core_bb1m.py (a byte-identical copy, sha256 5e4cd3f4...; loaded by path). Adaptations:
  (1) the new names come from a FILE (the lead's StmtDump: text or TSV; per line, the first tab field that looks
      like a dotted name is taken; `#` lines and a header are skipped) instead of from `git diff`; the diff-derived
      set (bb1m's `new_decls`, base..head over the six fill paths) is computed as a cross-check and differences
      are listed (NAMES-ONLY / DIFF-ONLY);
  (2) full-name check against SEVERAL trees: (i) the IO base 5ed465f6..., (ii) PR #377 head 7563734a...,
      (iii) origin/cleanup/stage2-s2a, (iv) the head itself minus the six fill paths (a new name must be declared
      only in the fill's own files); any hit is CLASH (exit 1);
  (3) same-short-name report: every declaration in those trees whose last component equals a new name's short
      name, with path:line and full name (INFO, not a failure);
  (4) downstream unqualified-use report: at the head, the TCSlib/ + audits/ + TCSlib.lean modules that import any
      of the six fill modules (transitively, reverse import closure) and mention a reported short name
      UNQUALIFIED (identifier token not preceded by `.` and not part of a longer identifier, in code with comments
      and strings blanked), with path:line; fill files are marked [fill];
  (5) `--controls`: K1 a planted existing full name in the names list is CLASH in (i)-(iii); K2 a synthetic
      namespaced file whose `namespace ... / def encodeVector` resolves to an existing name is CLASH; K3 a fresh
      name is OK with no INFO; K4 a fresh full name with an existing short name (`encodeVector`) gets INFO rows;
      K5 the unqualified-use matcher counts `addMod` / `(addMod` and skips `x.addMod`, `Foo.addMod`, `addMod_eq`,
      `addMod'`, comments and strings; K6 the reverse import closure on a synthetic graph; K7 a head-tree clash
      planted outside the fill paths. Prints ALL_CONTROLS_OK True|False.
Not covered (as in bb1m): auto-generated names (structure fields, constructors, equation/simps lemmas), names made
by macros. Usage:
  python3 -I clash_scan.py [--repo R] [--head REV] --names FILE --out DIR
  python3 -I clash_scan.py [--repo R] [--head REV] --controls --out DIR
"""
import importlib.util, os, re, sys

REPO = '/home/user/ef-r23/repo'
BASE = '5ed465f62e4ae0f93ded1a1ba49e807591b589eb'
TREES = [('base', BASE), ('pr377', '7563734a8badba842223e0687c719b3b4692e9d2'),
         ('stage2-s2a', 'origin/cleanup/stage2-s2a')]
FILL = ['TCSlib/Cryptography/Encoding/ModularArithmetic.lean', 'TCSlib/Cryptography/Encoding.lean',
        'TCSlib/Cryptography/Encryption/Symmetric/Regev/Asymptotic.lean',
        'TCSlib/Cryptography/Encryption/Symmetric/Regev.lean',
        'TCSlib/Cryptography/Encryption/PublicKey/Regev/Asymptotic.lean',
        'TCSlib/Cryptography/Encryption/PublicKey/Regev.lean']
NAME_TOKEN = re.compile(r"^[^\s.]+(\.[^\s.]+)+$")


def load_core():
    sys.dont_write_bytecode = True
    here = os.path.dirname(os.path.abspath(__file__))
    spec = importlib.util.spec_from_file_location('clash_core_bb1m', os.path.join(here, 'clash_core_bb1m.py'))
    m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
    return m


cs = load_core()


def read_names(path):
    out = []
    for line in open(path, encoding='utf-8'):
        line = line.rstrip('\n')
        if not line.strip() or line.lstrip().startswith('#'):
            continue
        for f in line.split('\t'):
            f = f.strip()
            if NAME_TOKEN.match(f) and not f.endswith('.lean'):
                out.append(f[len('_root_.'):] if f.startswith('_root_.') else f)
                break
    seen, res = set(), []
    for n in out:
        if n not in seen:
            seen.add(n); res.append(n)
    return res


def mod_of(path):
    return path[:-len('.lean')].replace('/', '.')


def head_texts(repo, rev):
    paths = [p for p in cs.git(repo, 'ls-tree', '-r', '--name-only', rev, '--', 'TCSlib', 'audits', 'TCSlib.lean')
             .decode('utf-8').splitlines() if p.endswith('.lean')]
    return cs.cat_files(repo, rev, paths)


def index_of_texts(texts, exclude=()):
    full, short = {}, {}
    for p, t in texts.items():
        if p in exclude:
            continue
        for d in cs.parse_decls(t):
            loc = dict(d, path=p)
            full.setdefault(d['full'], []).append(loc); short.setdefault(d['short'], []).append(loc)
    return dict(full=full, short=short, nfiles=len(texts) - len([p for p in exclude if p in texts]),
                ndecls=sum(len(v) for v in full.values()))


IMPORT_RE = re.compile(r'^import\s+(.+)$')


def importers(texts, targets):
    """Reverse import closure: paths whose module imports (transitively) any module in `targets`."""
    mods = {mod_of(p): p for p in texts}
    rev = {}
    for p, t in texts.items():
        for code in cs.strip_code(t):
            m = IMPORT_RE.match(code.strip())
            if m:
                for imp in m.group(1).split():
                    rev.setdefault(imp, set()).add(mod_of(p))
    seen, stack = set(), list(targets)
    while stack:
        x = stack.pop()
        for y in rev.get(x, ()):
            if y not in seen:
                seen.add(y); stack.append(y)
    return sorted(mods[m] for m in seen if m in mods)


def unqualified_uses(text, short):
    pat = re.compile(r"(?<![\w.'!?₀-₉])" + re.escape(short) + r"(?![\w'!?₀-₉])")
    return [ln for ln, code in enumerate(cs.strip_code(text), 1) if pat.search(code)]


def fmt(locs, limit=40):
    s = ', '.join(f'{x["path"]}:{x["line"]} {x["full"]}' + (' [private]' if 'private' in x['flags'] else '')
                  for x in locs[:limit])
    return s + (f', ... (+{len(locs) - limit})' if len(locs) > limit else '')


def scan(repo, head, names, out, trees=None, head_override=None):
    trees = trees or TREES
    idx = {}
    for tag, rev in trees:
        c = cs.git(repo, 'rev-parse', rev + '^{commit}').decode().strip()
        idx[tag] = (c, cs.base_index(repo, c))
    hc = cs.git(repo, 'rev-parse', head + '^{commit}').decode().strip()
    htexts = head_override if head_override is not None else head_texts(repo, hc)
    hidx = index_of_texts(htexts, exclude=FILL)
    idx['head-minus-fill'] = (hc, hidx)
    fill_idx = index_of_texts({p: t for p, t in htexts.items() if p in FILL})
    fill_mods = [mod_of(p) for p in FILL if p in htexts]
    imps = importers(htexts, fill_mods)
    rows, lines = [], []
    nclash = 0
    for n in names:
        short = n.split('.')[-1]
        clashes = {t: v[1]['full'].get(n, []) for t, v in idx.items()}
        info = {t: [x for x in v[1]['short'].get(short, []) if x['full'] != n] for t, v in idx.items()}
        st = 'CLASH' if any(clashes.values()) else 'OK'
        nclash += st == 'CLASH'
        declared = fill_idx['full'].get(n, [])
        rows.append(dict(name=n, short=short, status=st, clashes=clashes, info=info, declared=declared))
    # downstream unqualified uses, per short name that has INFO somewhere
    shorts = sorted({r['short'] for r in rows if any(r['info'].values())})
    uses = {s: [(p, unqualified_uses(htexts[p], s)) for p in imps] for s in shorts}
    uses = {s: [(p, l) for p, l in v if l] for s, v in uses.items()}
    os.makedirs(out, exist_ok=True)
    with open(os.path.join(out, 'clash.tsv'), 'w', encoding='utf-8') as fh:
        fh.write('# clash_scan.py (ef-r23-regev) repo=%s head=%s\n' % (repo, hc))
        for t, (c, i) in idx.items():
            fh.write(f'# tree {t} = {c}: {i["nfiles"]} .lean files, {i["ndecls"]} declarations\n')
        fh.write('status\tname\tdeclared_in_fill\t' + '\t'.join(f'clash_{t}' for t in idx) + '\t'
                 + '\t'.join(f'same_short_{t}' for t in idx) + '\n')
        for r in rows:
            fh.write('\t'.join([r['status'], r['name'], fmt(r['declared']) or 'NOT-FOUND-IN-FILL']
                               + [fmt(r['clashes'][t]) or '-' for t in idx]
                               + [(f'{len(r["info"][t])}: ' + fmt(r['info'][t])) if r['info'][t] else '-' for t in idx]) + '\n')
    with open(os.path.join(out, 'downstream.tsv'), 'w', encoding='utf-8') as fh:
        fh.write(f'# head {hc}: {len(imps)} modules import (transitively) one of: {" ".join(fill_mods)}\n')
        fh.write('# ' + ' '.join(imps) + '\n')
        fh.write('short_name\tpath\tlines\tfill_file\n')
        for s in shorts:
            if not uses[s]:
                fh.write(f'{s}\t-\t-\t-\n')
            for p, l in uses[s]:
                fh.write(f'{s}\t{p}\t{",".join(map(str, l))}\t{"fill" if p in FILL else "downstream"}\n')
    lines.append(f'head {hc}; trees: ' + ', '.join(f'{t}={c[:12]} ({i["nfiles"]} files, {i["ndecls"]} decls)'
                                                  for t, (c, i) in idx.items()))
    lines.append(f'importers of the fill modules at head ({len(imps)}): ' + ' '.join(imps))
    for r in rows:
        if r['status'] != 'OK':
            lines.append(f'CLASH {r["name"]}: ' + '; '.join(f'{t}: {fmt(v)}' for t, v in r['clashes'].items() if v))
        if not r['declared']:
            lines.append(f'NOT-FOUND-IN-FILL {r["name"]} (not parsed as a declaration of the fill files at head)')
    for s in shorts:
        where = sorted({f'{x["path"]}:{x["line"]} {x["full"]}' for r in rows if r['short'] == s for v in r['info'].values() for x in v})
        lines.append(f'SAME-SHORT {s}: {len(where)} declaration(s) elsewhere: ' + '; '.join(where[:20]) + (' ...' if len(where) > 20 else ''))
        ds = [(p, l) for p, l in uses[s] if p not in FILL]
        lines.append(f'  unqualified uses in importing modules: fill files '
                     + (', '.join(f'{p}:{",".join(map(str, l))}' for p, l in uses[s] if p in FILL) or 'none')
                     + ' | downstream ' + (', '.join(f'{p}:{",".join(map(str, l))}' for p, l in ds) or 'none'))
    lines.append(f'RESULT: {len(names)} names, {nclash} clashes, {len(shorts)} short names also declared elsewhere')
    return rows, uses, lines, nclash, fill_idx


def cross_check(repo, head, names):
    """bb1m's diff-derived new declarations over the six fill paths, base..head."""
    hc = cs.git(repo, 'rev-parse', head + '^{commit}').decode().strip()
    news, files = cs.new_decls(repo, BASE, hc)
    d = {x['full'] for x in news if x['path'] in FILL}
    extra = [x['path'] for x in news if x['path'] not in FILL]
    return sorted(set(names) - d), sorted(d - set(names)), sorted(set(extra))


# ---------------------------------------------------------------- controls
K2_TEXT = '''/-! doc: def encodeVector inside a comment -/
namespace TCSlib.Cryptography.Encoding
namespace Modular
/-- `def encodeMatrix` in a docstring -/
def encodeVector : Nat := 0
def fakeFresh_regev_k2 : String := "def encodeVector"
end Modular
end TCSlib.Cryptography.Encoding
'''
K5_TEXT = '''import Foo
open TCSlib.Cryptography.Encoding.ModularArithmetic
theorem t1 : addMod = addMod := rfl
theorem t2 : (addMod []).length = 0 := sorry
-- addMod in a comment
def s : String := "addMod in a string"
theorem t3 : x.addMod = Foo.addMod := addMod_eq
theorem t4 : addMod' = 0 := rfl
/- addMod
   in a block comment -/
'''


def controls(repo, head, out):
    ok = True
    res = []
    planted = 'TCSlib.Cryptography.Encoding.Modular.encodeVector'
    fresh = 'TCSlib.Cryptography.Encoding.ModularArithmetic.fakeFresh_regev_k3'
    fresh_short = 'TCSlib.Cryptography.Encoding.ModularArithmetic.encodeVector'
    rows, uses, lines, k, _ = scan(repo, head, [planted, fresh, fresh_short], os.path.join(out, 'controls-scan'))
    r = {x['name']: x for x in rows}
    k1 = r[planted]['status'] == 'CLASH' and all(r[planted]['clashes'][t] for t, _ in TREES)
    res.append(('K1 planted existing full name -> CLASH in base/pr377/stage2-s2a', k1,
                '; '.join(f'{t}:{len(v)}' for t, v in r[planted]['clashes'].items())))
    k3 = r[fresh]['status'] == 'OK' and not any(r[fresh]['info'].values())
    res.append(('K3 fresh name -> OK, no same-short INFO', k3, r[fresh]['status']))
    k4 = r[fresh_short]['status'] == 'OK' and all(any(x['full'] == planted for x in r[fresh_short]['info'][t]) for t, _ in TREES)
    res.append(('K4 fresh full name with existing short name -> OK + INFO lists Modular.encodeVector', k4,
                '; '.join(f'{t}:{len(v)}' for t, v in r[fresh_short]['info'].items())))
    base_idx = cs.base_index(repo, BASE)
    k2rows = cs.classify(cs.added_decls(K2_TEXT, None, 'TCSlib/Cryptography/Encoding/FakeK2.lean', 'A'), base_idx)
    got = {x['full']: x['status'] for x in k2rows}
    k2 = got == {planted: 'CLASH', 'TCSlib.Cryptography.Encoding.Modular.fakeFresh_regev_k2': 'OK'}
    res.append(('K2 namespaced synthetic file resolves Modular.encodeVector -> CLASH, fresh -> OK', k2, str(got)))
    u = unqualified_uses(K5_TEXT, 'addMod')
    k5 = u == [3, 4]
    res.append(('K5 unqualified-use matcher: lines [3, 4] only', k5, str(u)))
    g = {'TCSlib/A.lean': 'import TCSlib.Cryptography.Encoding\n', 'TCSlib/B.lean': 'import TCSlib.A\nimport Mathlib\n',
         'TCSlib/C.lean': '-- import TCSlib.B\nimport Mathlib\n', 'TCSlib.lean': 'import TCSlib.B\n',
         'TCSlib/Cryptography/Encoding.lean': 'import TCSlib.Cryptography.Encoding.ModularArithmetic\n'}
    imps = importers(g, ['TCSlib.Cryptography.Encoding.ModularArithmetic'])
    k6 = imps == ['TCSlib.lean', 'TCSlib/A.lean', 'TCSlib/B.lean', 'TCSlib/Cryptography/Encoding.lean']
    res.append(('K6 reverse import closure (commented import ignored)', k6, str(imps)))
    hc = cs.git(repo, 'rev-parse', head + '^{commit}').decode().strip()
    ht = head_texts(repo, hc)
    victim = 'TCSlib/Cryptography/Encoding/Modular.lean'
    ht2 = dict(ht); ht2[victim] = ht[victim] + '\nnamespace TCSlib.Cryptography.Encoding.ModularArithmetic\ndef addMod : Nat := 0\nend TCSlib.Cryptography.Encoding.ModularArithmetic\n'
    rows7, _, _, _, _ = scan(repo, head, ['TCSlib.Cryptography.Encoding.ModularArithmetic.addMod'], os.path.join(out, 'controls-k7'),
                             trees=[TREES[0]], head_override=ht2)
    k7 = rows7[0]['status'] == 'CLASH' and [x['path'] for x in rows7[0]['clashes']['head-minus-fill']] == [victim] \
        and not rows7[0]['clashes']['base']
    res.append(('K7 planted head-tree duplicate outside the fill paths -> CLASH (head-minus-fill only)', k7,
                fmt(rows7[0]['clashes']['head-minus-fill'])))
    for name, good, detail in res:
        ok &= bool(good)
        print(f'{"OK " if good else "BAD"} {name} | {detail}')
    print('ALL_CONTROLS_OK', ok)
    return ok


def main(argv):
    a = {'--repo': REPO, '--head': 'HEAD', '--names': None, '--out': None}
    ctl = False
    i = 1
    while i < len(argv):
        if argv[i] == '--controls':
            ctl = True; i += 1
        elif argv[i] in a and i + 1 < len(argv):
            a[argv[i]] = argv[i + 1]; i += 2
        else:
            print(__doc__); return 2
    if not a['--out'] or (not ctl and not a['--names']):
        print(__doc__); return 2
    if ctl:
        return 0 if controls(a['--repo'], a['--head'], a['--out']) else 1
    names = read_names(a['--names'])
    rows, uses, lines, k, fill_idx = scan(a['--repo'], a['--head'], names, a['--out'])
    only_names, only_diff, extra = cross_check(a['--repo'], a['--head'], names)
    lines.insert(0, f'names file {a["--names"]}: {len(names)} distinct names')
    lines.append(f'CROSS-CHECK vs git diff {BASE[:12]}..{a["--head"]} over the six fill paths: '
                 f'{len(only_names)} NAMES-ONLY, {len(only_diff)} DIFF-ONLY'
                 + (f'; files with new declarations outside the fill paths: {extra}' if extra else ''))
    for n in only_names: lines.append(f'  NAMES-ONLY {n}')
    for n in only_diff: lines.append(f'  DIFF-ONLY {n}')
    with open(os.path.join(a['--out'], 'clash-scan.out'), 'w', encoding='utf-8') as fh:
        fh.write('\n'.join(lines) + '\n')
    print('\n'.join(lines))
    print('output:', os.path.join(a['--out'], 'clash.tsv'), os.path.join(a['--out'], 'downstream.tsv'))
    return 0 if k == 0 else 1


if __name__ == '__main__':
    sys.exit(main(sys.argv))
