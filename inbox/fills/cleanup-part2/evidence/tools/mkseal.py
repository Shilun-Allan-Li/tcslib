#!/usr/bin/env python3
"""Build a whole-file sealed probe source for one owned module (cleanup-part2).

python3 -I mkseal.py <closure-log> <module> <source-file> <out.lean>
The seal block is inserted immediately after the header's last `import` line (before any other
command, namespace or option). Requests are constant-AST Names built from the exact components
printed by `#cp2closure`; each is checked for existence, home module and kind before
`attribute [local irreducible]` is elaborated; installed status is verified for every request;
already-irreducible names are counted separately. An `CP2-EOF` marker command is appended."""
import sys, re, json
log, module, srcf, out = sys.argv[1:5]
rows = []
for line in open(log):
    if not line.startswith('CLOSURE\t'): continue
    _, aud, name, home, kind, status, comps = line.rstrip('\n').split('\t')
    if aud != module: continue
    rows.append((name, home, kind, eval(comps.replace('[', '["').replace(']', '"]').replace(', ', '", "')) if comps != '[]' else []))
def term(comps):
    t = 'Lean.Name.anonymous'
    for c in comps:
        k, v = c.split(':', 1)
        if k == 's': t = f'(Lean.Name.str {t} {json.dumps(v, ensure_ascii=False)})'
        else: t = f'(Lean.Name.num {t} {int(v)})'
    return t
chunks = [rows[k:k + 200] for k in range(0, len(rows), 200)] or [[]]
parts = [f'-- CP2 WHOLE-FILE SEAL (evidence probe; not library source): {len(rows)} requests for {module}']
for ci_, ch in enumerate(chunks):
    reqs = ',\n    '.join(f'({term(c)}, {json.dumps(home)}, {json.dumps(kind)})' for _, home, kind, c in ch)
    parts.append(f'''run_cmd do
  let env ← Lean.getEnv
  let reqs : Array (Lean.Name × String × String) := #[
    {reqs}]
  let mut active : Nat := 0
  let mut already : Nat := 0
  for (n, home, kind) in reqs do
    let some ci := env.find? n | throwError "CP2-SEAL missing {{n}}"
    let some mi := env.getModuleIdxFor? n | throwError "CP2-SEAL no home {{n}}"
    unless (env.header.moduleNames[mi.toNat]!).toString == home do throwError "CP2-SEAL wrong home {{n}}"
    let k := match ci with | .defnInfo _ => "def" | .opaqueInfo _ => "opaque" | _ => "other"
    unless kind.startsWith k do throwError "CP2-SEAL wrong kind {{n}}"
    let before ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
    if before == .irreducible then
      already := already + 1
    else
      let id := Lean.mkIdent n
      Lean.Elab.Command.elabCommand (← `(command| attribute [local irreducible] $id:ident))
      active := active + 1
    let after ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
    unless after == .irreducible do throwError "CP2-SEAL not installed {{n}}"
  Lean.logInfo m!"CP2-SEAL chunk={ci_} requested={{reqs.size}} active={{active}} already={{already}}"''')
parts.append('-- CP2 END SEAL')
block = '\n'.join(parts) + '\n'
L = open(srcf).read().split('\n')
last = max(i for i, l in enumerate(L) if re.match(r'^import\s', l))
L.insert(last + 1, block)
text = '\n'.join(L)
if not text.endswith('\n'): text += '\n'
text += '\nrun_cmd Lean.logInfo "CP2-EOF"\n'
open(out, 'w').write(text)
print(module, len(rows), 'requests; seal inserted after line', last + 1)
