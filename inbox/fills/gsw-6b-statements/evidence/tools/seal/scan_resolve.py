r"""scan_resolve.py <worktree> <outdir> <tree> <path>... (gsw-6b-statements sub-agent `seal`, new; a supplement to
scan_unfold.py, which resolves names against TCSlib definitions only).
Rule 10's second half: core/Mathlib definitions may reduce in rfl/decide/show but are never passed to
simp/rw/unfold. For every listed file it takes exactly scan_unfold.py's hits (every identifier inside the `[...]`
of simp/simp only/simp_all/dsimp/simp?/rw/rwa/rewrite/nth_rewrite/nth_rw/erw/simp_rw, `←`/`@` stripped, and every
identifier after unfold/delta/unfold_let; comments and strings blanked), then RESOLVES each identifier in Lean, in
the file's own name context: a probe `import <module>` + `namespace <the file's first namespace>` + the file's
top-level `open` lines (a trailing ` in` removed) + one `run_cmd` calling `Lean.ResolveName.resolveGlobalName` on
every identifier (exact matches only: no remaining field components). The probe runs as `lean -DmaxErrors=0`
under the shared pool (runner_pool.py), no -o. Each hit is classified:
  LOCAL        no global resolution (a hypothesis, a let-bound or private name of the file, or field notation);
  THEOREM      every candidate is a theorem (or an axiom);
  OWN-DEF      a definition of the file's own module (allowed: a file may unfold its own definitions);
  NOTATION     a TCSlib definition elsewhere that is reducible/abbrev or PolyExpr.eval (notation);
  FOREIGN-UNFOLD   a TCSlib definition of another module that is not notation (Rule 10 breach);
  CORE-DEF     a core/Mathlib/Batteries definition (defnInfo, not a matcher), with its reducibility status,
               instance and projection flags (a Rule 10 breach unless it is reducible notation; listed for triage);
  CTOR/INDUCT/REC/QUOT/OPAQUE  other constant kinds (listed for triage).
Writes <outdir>/scan-resolve.tsv (file:line, tactic, identifier, class, candidates) and <outdir>/scan-resolve.log
and prints the counts per class."""
import sys, os, re, json, subprocess
wt, outdir, tree = sys.argv[1:4]; paths = sys.argv[4:]
outdir = os.path.abspath(outdir); os.makedirs(outdir, exist_ok=True)
T = os.path.dirname(os.path.abspath(__file__))
sub = 'evidence-scratch/rule10/resolve-' + os.path.basename(os.path.dirname(outdir)) + '-' + os.path.basename(outdir)
os.makedirs(os.path.join(wt, sub), exist_ok=True)
def blank(s):  # scan_unfold.py's blanking, verbatim
    out = []; i = 0; depth = 0
    while i < len(s):
        if s.startswith('/-', i): depth += 1; out.append('  '); i += 2; continue
        if depth and s.startswith('-/', i): depth -= 1; out.append('  '); i += 2; continue
        if depth: out.append('\n' if s[i] == '\n' else ' '); i += 1; continue
        if s.startswith('--', i):
            j = s.find('\n', i); j = len(s) if j < 0 else j; out.append(' ' * (j - i)); i = j; continue
        if s[i] == '"':
            j = i + 1
            while j < len(s) and s[j] != '"': j += 2 if s[j] == '\\' else 1
            out.append(' ' * (j + 1 - i)); i = j + 1; continue
        out.append(s[i]); i += 1
    return ''.join(out)
TAC = re.compile(r'\b(simp_all|simp_rw|simp\?|simp|dsimp|rwa|rw|rewrite|nth_rewrite|nth_rw|erw)\b(\s+only)?[^\[\n]*?\[')
def hits_of(s):  # scan_unfold.py's hit extraction, verbatim
    hits = []
    for m in TAC.finditer(s):
        i = m.end(); d = 1; j = i
        while j < len(s) and d:
            if s[j] == '[': d += 1
            elif s[j] == ']': d -= 1
            j += 1
        for a in s[i:j - 1].split(','):
            a = a.strip().lstrip('←').strip()
            mm = re.match(r"^@?([A-Za-z_][\w.'₀-₉]*)", a)
            if mm: hits.append((s[:i].count('\n') + 1, m.group(1), mm.group(1)))
    for m in re.finditer(r'\b(unfold|delta|unfold_let)\s+([^\n]*)', s):
        for a in m.group(2).split():
            if re.match(r"^[A-Za-z_][\w.']*$", a) and a not in ('at', 'in'):
                hits.append((s[:m.start()].count('\n') + 1, m.group(1), a))
    return hits
probes, filehits = [], {}
for p in paths:
    mod = p[:-5].replace('/', '.'); s = blank(open(os.path.join(wt, p), encoding='utf8').read())
    hits = hits_of(s); filehits[p] = (mod, hits)
    ns = re.search(r'^namespace\s+(\S+)', s, re.M)
    opens = [re.sub(r'\s+in\s*$', '', l.strip()) for l in re.findall(r'^open\s+[^\n]*', s, re.M)]
    idents = sorted({h[2] for h in hits})
    src = f'import {mod}\n' + (f'namespace {ns.group(1)}\n' if ns else '') + ''.join(o + '\n' for o in opens)
    src += 'open Lean in\nrun_cmd do\n  let env ← getEnv\n  let cns ← Lean.getCurrNamespace\n  let ods ← Lean.getOpenDecls\n'
    src += '  for s in (' + json.dumps(idents, ensure_ascii=False).replace('[', '[', 1) + ' : List String) do\n'
    src += '''    let id := s.toName
    let cands := (Lean.ResolveName.resolveGlobalName env (← Lean.getOptions) cns ods id).filter (·.2.isEmpty) |>.map (·.1)
    let mut arr : Array Json := #[]
    for n in cands do
      let some ci := env.find? n | continue
      let kind := match ci with
        | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "theorem" | .opaqueInfo _ => "opaque"
        | .quotInfo _ => "quotient" | .inductInfo _ => "inductive" | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"
      let home := match env.getModuleIdxFor? n with
        | some mi => env.header.moduleNames[mi.toNat]!.toString | none => "<this file>"
      let st := match Lean.getReducibilityStatusCore env n with
        | .reducible => "reducible" | .semireducible => "semireducible" | .irreducible => "irreducible"
      let abbrevFlag := match ci with
        | .defnInfo d => match d.hints with | .abbrev => true | _ => false
        | _ => false
      arr := arr.push (Json.mkObj [("name", toJson n.toString), ("kind", toJson kind), ("home", toJson home),
        ("status", toJson st), ("abbrev", toJson abbrevFlag), ("instance", toJson (Lean.Meta.isInstanceCore env n)),
        ("matcher", toJson (Lean.Meta.isMatcherCore env n)), ("projection", toJson (env.isProjectionFn n))])
    IO.println ("RESOLVE " ++ (Json.mkObj [("ident", toJson s), ("cands", Json.arr arr)]).compress)
'''
    tag = mod.split('.', 1)[1].replace('.', '_'); m = f'{sub}/Resolve_{tag}'
    open(os.path.join(wt, m + '.lean'), 'w', encoding='utf8').write(src)
    open(os.path.join(outdir, f'Resolve_{tag}.lean'), 'w', encoding='utf8').write(src)
    probes.append((p, m))
order = os.path.join(outdir, 'order-resolve.txt'); open(order, 'w').write('\n'.join(m for _, m in probes) + '\n')
rd = os.path.join(outdir, 'run-resolve'); subprocess.run(['rm', '-rf', rd])
subprocess.run(['python3', '-I', os.path.join(T, 'xr', 'runner_pool.py'), wt, order, tree, rd, '3'], check=True)
res = {}
for l in open(os.path.join(rd, 'results.jsonl')):
    x = json.loads(l)
    if 'module' in x: res[x['module']] = x
counts = {}; rows = []; bad = []
for p, m in probes:
    mod, hits = filehits[p]
    x = res[m]
    if x['rc'] != 0 or x['errors']: bad.append((p, x)); continue
    txt = open(os.path.join(rd, 'mods', m.replace('/', '_') + '.log'), encoding='utf8').read()
    R = {}
    for l in txt.splitlines():
        if l.startswith('RESOLVE '):
            r = json.loads(l[8:]); R[r['ident']] = r['cands']
    for line, tac, ident in hits:
        cs = R.get(ident)
        assert cs is not None, (p, ident)
        def cls(c):
            if c['kind'] in ('theorem', 'axiom'): return 'THEOREM'
            if c['kind'] == 'def':
                if c['home'] == mod: return 'OWN-DEF'
                if c['home'].startswith('TCSlib'):
                    return 'NOTATION' if (c['abbrev'] or c['status'] == 'reducible' or c['name'] == 'Complexity.PolyExpr.eval') else 'FOREIGN-UNFOLD'
                return 'CORE-DEF'
            return {'constructor': 'CTOR', 'inductive': 'INDUCT', 'recursor': 'REC', 'quotient': 'QUOT', 'opaque': 'OPAQUE'}[c['kind']]
        k = 'LOCAL' if not cs else '/'.join(sorted({cls(c) for c in cs}))
        counts[k] = counts.get(k, 0) + 1
        rows.append((f'{p}:{line}', tac, ident, k, json.dumps(cs, ensure_ascii=False)))
with open(os.path.join(outdir, 'scan-resolve.tsv'), 'w') as f:
    f.write('location\ttactic\tidentifier\tclass\tcandidates\n')
    for r in rows: f.write('\t'.join(r) + '\n')
summary = [f'files={len(paths)} hits={len(rows)} probe_failures={len(bad)}'] + [f'{k}\t{v}' for k, v in sorted(counts.items())]
summary += [f'PROBE-FAILED\t{p}\trc={x["rc"]}\terrors={x["errors"]}' for p, x in bad]
summary += [f'{r[3]}\t{r[0]}\t{r[1]}\t{r[2]}' for r in rows if r[3] not in ('THEOREM', 'LOCAL', 'OWN-DEF')]
open(os.path.join(outdir, 'scan-resolve.log'), 'w').write('\n'.join(summary) + '\n')
print('\n'.join(summary))
