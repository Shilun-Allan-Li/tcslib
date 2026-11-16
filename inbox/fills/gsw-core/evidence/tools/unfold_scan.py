"""Explicit-unfold scan for the gsw-core fill (python3 -I), Lean-resolved.

Step `prepare`: for each owned file, extract every identifier passed to `unfold`, `delta`,
`simp`/`simp_all`/`simpa`/`dsimp`/`rw`/`rwa`/`erw`/`nth_rw`/`simp_rw` selector lists (comments and
strings masked), with its line and enclosing declaration, and write a Lean probe that imports
the file's own module, re-enters its namespace and `open` lines, and resolves each token with
`Lean.resolveGlobalConst`, printing the kind, home module and reducibility of every candidate.
Step `report`: read the probe log and classify each site:
  * VIOLATION-FOREIGN-TCSLIB: a TCSlib definition (not a theorem) from another module;
  * VIOLATION-CORE-MATHLIB: a core/Mathlib/Batteries definition (not a theorem);
  * own: a definition of the file itself (allowed);
  * lemma: theorems (allowed); local: unresolved short names (hypotheses, locals).
Reducible abbreviations and structure projections are reported as `notation` (allowed).

usage: unfold_scan.py prepare OUTDIR ROOT FILE... [--rev REV]
       unfold_scan.py report OUTDIR
"""
import json, re, subprocess, sys
from pathlib import Path

SEL = re.compile(r'\b(?:unfold|delta)\s+([^\n;]+)|'
                 r'\b(?:simp_all|simp_rw|simpa|simp|dsimp|rwa|rw|erw|nth_rw\s+\d+(?:\s+\d+)*)'
                 r'\s*(?:(?:only|!|\?)\s*)*\[([^\]]*)\]', re.S)
IDENT = re.compile(r'[A-Za-z_À-ɏͰ-Ͽ][A-Za-z_0-9À-ɏͰ-Ͽ'
                   r'₀-₉⁰-ₜ!?\']*(?:\.[A-Za-z_Ͱ-Ͽ][A-Za-z_0-9'
                   r'Ͱ-Ͽ₀-₉!?\']*)*')


def mask(src):
    out, i, n = [], 0, len(src)
    while i < n:
        if src.startswith('/-', i):
            depth, j = 0, i
            while j < n:
                if src.startswith('/-', j):
                    depth += 1; j += 2
                elif src.startswith('-/', j):
                    depth -= 1; j += 2
                    if depth == 0:
                        break
                else:
                    j += 1
            out.append(re.sub(r'[^\n]', ' ', src[i:j])); i = j
        elif src.startswith('--', i):
            j = src.find('\n', i); j = n if j < 0 else j
            out.append(' ' * (j - i)); i = j
        elif src[i] == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == '\\' else 1
            out.append(' ' * (j + 1 - i)); i = j + 1
        else:
            out.append(src[i]); i += 1
    return ''.join(out)


def tokens(body, kind_unfold):
    if kind_unfold:
        body = re.split(r'\bat\b', body, maxsplit=1)[0]
        return IDENT.findall(body)
    pieces, start, depth = [], 0, 0
    for k, ch in enumerate(body):
        if ch in '([{⟨':
            depth += 1
        elif ch in ')]}⟩':
            depth -= 1
        elif ch == ',' and depth == 0:
            pieces.append(body[start:k]); start = k + 1
    pieces.append(body[start:])
    res = []
    for p in pieces:
        p = p.strip().removeprefix('←').removeprefix('<-').strip()
        if p.startswith('-') or not p:
            continue
        m = IDENT.match(p)
        if m and m[0] not in {'show', 'by', 'fun', 'if', 'this'}:
            res.append(m[0])
    return res


def sites(src):
    masked = mask(src)
    decl_re = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable)\s+)*'
                         r'(?:theorem|lemma|def|abbrev|instance|structure)\s+(\S+)', re.M)
    decls = [(masked.count('\n', 0, m.start()) + 1, m.group(1)) for m in decl_re.finditer(masked)]
    out = []
    for m in SEL.finditer(masked):
        line = masked.count('\n', 0, m.start()) + 1
        decl = next((d for l, d in reversed(decls) if l <= line), '')
        for t in tokens(m[1] if m[1] is not None else m[2], m[1] is not None):
            out.append(dict(line=line, decl=decl, token=t, selector=' '.join(m[0].split())[:160]))
    return out


def prepare(outdir, root, files, rev):
    out = Path(root) / outdir
    out.mkdir(parents=True, exist_ok=True)
    allsites = {}
    for path in files:
        src = subprocess.check_output(['git', '-C', root, 'show', f'{rev}:{path}'], text=True) \
            if rev else (Path(root) / path).read_text()
        st = sites(src)
        allsites[path] = st
        module = path[:-5].replace('/', '.')
        opens = [l for l in src.splitlines() if re.match(r'^(namespace|open)\s', l)]
        toks = sorted({s['token'] for s in st})
        stem = Path(path).stem
        lean = [f'import {module}', 'import Lean', ''] + opens + ['', 'run_cmd do']
        lean.append(f'  let home := `{module}')
        lean.append('  let env ← Lean.getEnv')
        lean.append('  for tok in [' + ', '.join(json.dumps(t) for t in toks) + '] do')
        lean.append('    let id := Lean.mkIdent (tok.toName)')
        lean.append('    let cs ← (Lean.Elab.Command.liftCoreM (Lean.resolveGlobalConst id)) <|> '
                    'pure []')
        lean.append('    if cs.isEmpty then Lean.logInfo m!"UNFOLDSCAN {tok} UNRESOLVED"')
        lean.append('    for c in cs do')
        lean.append('      let some ci := env.find? c | continue')
        lean.append('      let kind := match ci with')
        lean.append('        | .thmInfo _ => "thm" | .defnInfo _ => "def" | .axiomInfo _ => "axiom"')
        lean.append('        | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot"')
        lean.append('        | .inductInfo _ => "induct" | .ctorInfo _ => "ctor" | .recInfo _ => "rec"')
        lean.append('      let mod := match env.getModuleIdxFor? c with')
        lean.append('        | some i => (env.header.moduleNames[i.toNat]!).toString')
        lean.append('        | none => home.toString')
        lean.append('      let red := (Lean.getReducibilityStatusCore env c).toAttrString')
        lean.append('      let proj := env.isProjectionFn c')
        lean.append('      let matcher := Lean.Meta.isMatcherCore env c')
        lean.append('      Lean.logInfo m!"UNFOLDSCAN {tok} {c} {kind} {mod} red={red} '
                    'proj={proj} matcher={matcher}"')
        lean.append('')
        (out / f'UnfoldScan{stem}.lean').write_text('\n'.join(lean))
        (out / f'UnfoldScan{stem}.sites.json').write_text(json.dumps(dict(path=path, module=module,
                                                                          sites=st), indent=1))
    print(f'prepared {len(files)} probes in {out}')


def report(outdir):
    out = Path(outdir)
    total_v = 0
    for sj in sorted(out.glob('UnfoldScan*.sites.json')):
        info = json.loads(sj.read_text())
        log = sj.with_name(sj.name.replace('.sites.json', '.log'))
        res = {}
        text = log.read_text() if log.exists() else ''
        for m in re.finditer(r'UNFOLDSCAN (\S+) (.*)', text):
            res.setdefault(m[1], []).append(m[2])
        errs = re.findall(r'^\S+\.lean:\d+:\d+: error[:(].*$', text, re.M)
        print(f'== {info["path"]}: {len(info["sites"])} selector tokens, probe errors {len(errs)}')
        for e in errs:
            print('   PROBE ERROR ' + e)
        counts = {}
        for s in info['sites']:
            rows = res.get(s['token'])
            if rows is None:
                cls = 'NOT-QUERIED'
            elif rows == ['UNRESOLVED']:
                cls = 'local'
            else:
                cls = 'lemma'
                for r in rows:
                    c, kind, mod, red, proj, matcher = r.split()[:6]
                    if kind in ('def', 'opaque') or matcher == 'matcher=true':
                        if red == 'red=[reducible]' or proj == 'proj=true':
                            cls = 'notation'
                        elif mod == info['module']:
                            cls = 'own'
                        elif mod.startswith('TCSlib'):
                            cls = 'VIOLATION-FOREIGN-TCSLIB'
                        else:
                            cls = 'VIOLATION-CORE-MATHLIB'
                        s['resolved'] = r
            counts[cls] = counts.get(cls, 0) + 1
            if cls.startswith('VIOLATION') or cls in ('NOT-QUERIED', 'notation', 'own'):
                print(f'   {cls} line {s["line"]} in {s["decl"]}: {s["token"]} -> '
                      f'{s.get("resolved", rows)} :: {s["selector"]}')
            total_v += cls.startswith('VIOLATION') or cls == 'NOT-QUERIED'
        print(f'   classes: {counts}')
    print(f'EXPLICIT UNFOLD SCAN {"PASS" if total_v == 0 else "REVIEW"}: {total_v} flagged site(s)')
    return 1 if total_v else 0


if __name__ == '__main__':
    a = sys.argv[1:]
    if a[0] == 'prepare':
        rev = a[a.index('--rev') + 1] if '--rev' in a else None
        files = [x for x in a[3:] if x != '--rev' and x != rev]
        prepare(a[1], a[2], files, rev)
    else:
        sys.exit(report(a[1]))
