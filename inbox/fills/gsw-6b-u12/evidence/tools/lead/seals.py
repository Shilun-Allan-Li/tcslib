#!/usr/bin/env python3
"""Whole-file Rule-10 seals (gsw-6b-u12; my sc-compose tool, adapted: paths, `-DmaxErrors=0`, the
optional liveness pair appended to the probe, the unsealed pretest; resumable).

usage: seals.py TAG ROOT FILE... [--live LIVEFILE] (TAG = base | cp1 | final; ROOT = a directory holding
the sources under their repository paths; LIVEFILE = Lean text appended to every probe, with
`-- NEG` / `-- POS` marker lines, whose errors are reported per marker)

For each FILE (a .lean path relative to ROOT):
1. census: scratch/seal/TAG/Census_<key>.lean has exactly the file's imports and prints one `CAT` line
   per constant of a TCSlib module of its import closure (name, home module, kind, reducibility,
   instance, matcher, private). Every module of the closure is foreign to the file.
2. requests, per variant (as the maintainer's mkseals_ab / mkseals_coe): every TCSlib definition of the
   closure that is a matcher or not reducible (reducible abbreviations are notation); variant A exempts
   `Complexity.PolyExpr.eval` (notation, Q1), variant B seals it too; the `strict` variants seal
   projection coercions as well, the `coe` variants exempt them (the `CoeFun`/`Coe` instances whose
   body is a structure projection: `TCSlib.InformationTheory.FinDist.instCoeFunForallReal`, Seyoon's
   ruling 2026-11-14).
3. probe: a byte-for-byte copy of the file with `import Lean` prepended and, after its imports, a
   `run_cmd` harness that makes every requested constant `local irreducible` (found by its exact
   name in the environment) and, at the end of the file, a harness that checks every request is still
   irreducible (`SEAL-VERIFY`).
4. run: `lean` on the probe (one process at a time); errors counted with
   `^\\S+\\.lean:\\d+:\\d+: error[:(]` and attributed to the enclosing declaration of the original file.
Results: evidence/seals/TAG/results.jsonl (one line per file and variant); raw logs beside it.
"""
import json, os, re, subprocess, sys, time

argv = sys.argv[1:]
LIVE = None
if '--live' in argv:
    k = argv.index('--live'); LIVE = open(argv[k + 1]).read(); del argv[k:k + 2]
TAG, ROOT, FILES = argv[0], argv[1], argv[2:]
R = '/workspace/gsw/repo'
OUT = f'/workspace/gsw/evidence/rule10/{TAG}'
SRC = f'{R}/scratch/seal/{TAG}'
os.makedirs(OUT, exist_ok=True)
os.makedirs(SRC, exist_ok=True)
EVAL = 'Complexity.PolyExpr.eval'
COE = {'TCSlib.InformationTheory.FinDist.instCoeFunForallReal'}
VARIANTS = {'strict-A': (False, False), 'strict-B': (True, False),
            'coe-A': (False, True), 'coe-B': (True, True)}
if LIVE:
    VARIANTS = {'unsealed': (None, None), **VARIANTS}
CHUNK = 400
LP = f'{R}/.lake/tcslib-check-oleans:' + ':'.join(
    f'{R}/.lake/packages/{d}/.lake/build/lib/lean' for d in sorted(os.listdir(R + '/.lake/packages')))
ENV = dict(os.environ, LEAN_PATH=LP, PATH=os.path.expanduser('~/.elan/bin') + ':' + os.environ['PATH'])
ERR = re.compile(r'^\S+\.lean:(\d+):\d+: error[:(]', re.M)
DECL = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec)\s+)*'
                  r'(theorem|lemma|def|abbrev|instance|structure|inductive|example)\b\s*([^\s:({\[]*)')

CENSUS = '''
open Lean Elab Command Meta

/-! Seal census (sc-compose, %s) for `%s`: the file's own imports; one `CAT` line per constant of a
TCSlib module of the import closure (all foreign to the file). -/

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut out : Array String := #[]
  for (c, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? c | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless (`TCSlib).isPrefixOf mod do continue
    let kind := match ci with
      | .defnInfo _ => "def" | .thmInfo _ => "thm" | .opaqueInfo _ => "opaque"
      | .axiomInfo _ => "axiom" | .inductInfo _ => "induct" | .ctorInfo _ => "ctor"
      | .recInfo _ => "rec" | .quotInfo _ => "quot"
    let st := match getReducibilityStatusCore env c with
      | .reducible => "reducible" | .semireducible => "semireducible"
      | .irreducible => "irreducible"
    let inst := isInstanceCore env c
    let matcher := (Match.Extension.getMatcherInfo? env c).isSome
    out := out.push s!"CAT\\t{c}\\t{mod}\\t{kind}\\t{st}\\t{inst}\\t{matcher}\\t{isPrivateName c}"
  for s in out.qsort (· < ·) do IO.println s
  IO.println s!"TOTAL {out.size}"
'''

HARNESS = '''
set_option maxHeartbeats 0 in
run_cmd do
  let payload : String := %s
  let want : List String := if payload.isEmpty then [] else payload.splitOn "\\n"
  let env ← Lean.getEnv
  let mut byName : Std.HashMap String Lean.Name := {}
  for (n, _) in env.constants.toList do
    byName := byName.insert n.toString n
  let mut count : Nat := 0
  for s in want do
    let some n := byName[s]? | throwError "SEAL-HARNESS unknown constant {s}"
    let st ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
    if %s then
      unless st == .irreducible do throwError "SEAL-VERIFY not irreducible: {s}"
    else
      unless st == .irreducible do
        Lean.Elab.Command.elabCommand
          (← `(command| attribute [local irreducible] $(Lean.mkIdent n):ident))
    count := count + 1
  Lean.logInfo m!"%s {count}"
'''


def run(path, log):
    t = time.time()
    p = subprocess.run(['lean', '-DmaxErrors=0', path], cwd=R, env=ENV, capture_output=True, text=True)
    open(log, 'w').write(p.stdout + p.stderr + f'\nEXIT {p.returncode}\n')
    return p.returncode, p.stdout + p.stderr, round(time.time() - t, 1)


def decl_at(lines, ln):
    for i in range(min(ln, len(lines)) - 1, -1, -1):
        m = DECL.match(lines[i])
        if m:
            return m.group(2) or m.group(1)
    return '?'


def harness(rows, verify, label):
    out = ''
    for i in range(0, max(len(rows), 1), CHUNK):
        part = rows[i:i + CHUNK]
        out += HARNESS % (json.dumps('\n'.join(part)), 'true' if verify else 'false',
                          f'SEAL-{"VERIFY" if verify else "INSTALL"} {label} part {i // CHUNK + 1}:')
    return out


res = f'{OUT}/results.jsonl'
done = set()
if os.path.exists(res):
    for l in open(res):
        d = json.loads(l)
        done.add((d['file'], d['variant']))
t0 = time.time()
for f in FILES:
    key = f[len('TCSlib/'):-len('.lean')].replace('/', '_')
    if all((f, v) in done for v in VARIANTS):
        continue
    src = open(os.path.join(ROOT, f), encoding='utf-8').read()
    lines = src.split('\n')
    imps = [i for i, l in enumerate(lines) if l.startswith('import ')]
    clog = f'{OUT}/census-{key}.log'
    if not os.path.exists(clog) or 'TOTAL' not in open(clog).read():
        cpath = f'{SRC}/Census_{key}.lean'
        open(cpath, 'w').write('\n'.join(lines[i] for i in imps) + '\n' + CENSUS % (TAG, f))
        rc, _, _ = run(cpath, clog)
        if rc:
            print('CENSUS FAILED', f)
            sys.exit(1)
    cat = [l.rstrip('\n').split('\t') for l in open(clog) if l.startswith('CAT\t')]
    base_rows = sorted(c[1] for c in cat if c[3] == 'def' and (c[6] == 'true' or c[4] != 'reducible'))
    for var, (seal_eval, coe) in VARIANTS.items():
        if (f, var) in done:
            continue
        if time.time() - t0 > 230:
            print('PAUSE')
            sys.exit(0)
        rows = [r for r in base_rows if (seal_eval or r != EVAL) and not (coe and r in COE)]
        if seal_eval is None:  # the unsealed pretest of the liveness pair
            rows = []
        last = imps[-1] + 1
        label = f'{TAG}/{key}/{var}'
        prefix = 'import Lean\n' + '\n'.join(lines[:last]) + '\n' + (harness(rows, False, label)
                                                                       if rows else '')
        body_end = (prefix + '\n'.join(lines[last:]) + '\n').count('\n')
        live = (LIVE + '\n') if LIVE else ''
        probe = prefix + '\n'.join(lines[last:]) + '\n' + live + (harness(rows, True, label)
                                                                  if rows else '')
        shift = prefix.count('\n') - last
        ppath = f'{SRC}/Seal_{key}_{var.replace("-", "")}.lean'
        open(ppath, 'w').write(probe)
        log = f'{OUT}/seal-{key}-{var}.log'
        rc, text, dt = run(ppath, log)
        errs = []
        live_errs = {}
        lmarks = [(body_end + i + 1, l.strip('- ').strip()) for i, l in enumerate(live.split('\n'))
                  if l.startswith('-- NEG') or l.startswith('-- POS')]
        for m in ERR.finditer(text):
            pl = int(m.group(1))
            if LIVE and pl > body_end:
                lab = max([mk for mk in lmarks if mk[0] <= pl], default=(0, 'LIVE?'))[1]
                live_errs[lab] = live_errs.get(lab, 0) + 1
                continue
            ol = pl - 1 if pl - 1 <= last else pl - shift
            ol = ol if ol <= len(lines) else len(lines) + 1
            errs.append(decl_at(lines, ol))
        installed = len(re.findall(r'SEAL-INSTALL', text))
        verified = len(re.findall(r'SEAL-VERIFY \S+ part', text))
        rec = dict(file=f, variant=var, exit=rc, seconds=dt, requests=len(rows),
                   eval_sealed=seal_eval, coe_exempt=coe, errors=len(errs),
                   failing=sorted(set(errs)), harness_install_parts=installed,
                   harness_verify_parts=verified)
        if LIVE:
            rec['live_errors_by_marker'] = {mk[1]: live_errs.get(mk[1], 0) for mk in lmarks}
        open(res, 'a').write(json.dumps(rec) + '\n')
        print(var, key, 'exit', rc, 'errors', len(errs), sorted(set(errs)), 'requests', len(rows), dt)
print('DONE')
