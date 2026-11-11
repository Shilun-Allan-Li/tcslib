"""Build the adaptive-cpa seal files from the reference census (refs-final.log).

For each changed file, the seal copies the file's body into a probe module and makes every
semireducible foreign candidate of that file `local irreducible` (instance-aware: an instance is
replaced by a local reducible alias, as in the earlier fills) right after the file's `open` line,
so the whole body is checked under the seal. A control that unfolds one sealed definition by
`rfl` is generated before and after the seal.
Usage: python3 -I make_seal2.py <clone> <refs-log> <evidence-dir> <controls.json>
"""
import json
import sys
from pathlib import Path

clone, refs, evid, ctl = Path(sys.argv[1]), Path(sys.argv[2]), Path(sys.argv[3]), Path(sys.argv[4])
EXEMPT = {'Complexity.PolyExpr.eval': 'notation explicitly exempted by the issued brief'}
B = 'TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA'
ANCHOR = {
    B + '.Hybrid': 'open Complexity TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp ChallengeSim\n',
    B + '.Handler': 'open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games\n',
    B + '.Games': 'open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp\n',
    B + '.Reduction': 'open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp ChallengeSim\n',
    B: 'open Complexity Turing TCSlib.Cryptography.Games\n',
}
controls = json.loads(ctl.read_text())
rows = {}
for line in refs.read_text().splitlines():
    if 'CANDIDATE|' not in line:
        continue
    own, name, home, status, inst, proj = line.split('CANDIDATE|', 1)[1].split('|')[:6]
    rows.setdefault((own, name), dict(file=own, name=name, home=home, status=status,
        instance=inst == 'instance=true', projection=proj.strip() == 'projection=true'))
for r in rows.values():
    if r['name'] in EXEMPT:
        r['skipped'] = EXEMPT[r['name']]
    elif r['status'].endswith('.reducible'):
        r['skipped'] = ('primitive structure projection (reducible)' if r['projection']
                        else 'abbreviation (reducible)')
    else:
        r['skipped'] = None
table = sorted(rows.values(), key=lambda r: (r['file'], r['name']))
(evid / 'seal-candidates.json').write_text(json.dumps(table, indent=2) + '\n')

def seal_cmd(names, tag):
    lst = ',\n    '.join(json.dumps(n) for n in names)
    return f'''run_cmd do
  let names : Array String := #[
    {lst}]
  for index in [:names.size] do
    let name := names[index]!.toName
    let some ci := (← Lean.getEnv).find? name | throwError "Missing seal candidate {{name}}"
    unless ci.isDefinition do throwError "Nondefinition seal candidate {{name}}"
    if Lean.Meta.isInstanceCore (← Lean.getEnv) name then
      Lean.Elab.Command.elabCommand (← `(command| attribute [-instance] $(Lean.mkIdent name):ident))
      let aliasName := ("{tag}SealInstance" ++ toString index).toName
      Lean.Elab.Command.liftCoreM <| Lean.addDecl (.defnDecl {{
        name := aliasName, levelParams := ci.levelParams, type := ci.type,
        value := Lean.mkConst name (ci.levelParams.map Lean.Level.param),
        hints := .abbrev, safety := .safe }})
      Lean.Elab.Command.elabCommand (← `(command| attribute [local instance] $(Lean.mkIdent aliasName):ident))
      Lean.logInfo m!"INSTANCE_ALIAS|{{name}}|{{aliasName}}"
    Lean.Elab.Command.elabCommand (← `(command| attribute [local irreducible] $(Lean.mkIdent name):ident))
    let status ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus name
    unless status == .irreducible do throwError "Seal not installed for {{name}}"
    Lean.logInfo m!"SEALED|{{name}}|{{repr status}}"
'''

out = clone / 'AcpaProbe'
for mod, anchor in ANCHOR.items():
    tag = 'Owned' if mod == B else mod.split('.')[-1]
    names = [r['name'] for r in table if r['file'] == mod and not r['skipped']]
    src = (clone / (mod.replace('.', '/') + '.lean')).read_text(encoding='utf-8')
    imports = [l for l in src.splitlines() if l.startswith('import ')]
    header = 'import Lean\n' + '\n'.join(imports) + '\n\n'
    body = src[src.index('set_option maxHeartbeats'):]
    cmd = seal_cmd(names, tag)
    assert body.count(anchor) == 1, mod
    (out / f'Seal{tag}.lean').write_text(header + body.replace(anchor, anchor + '\n' + cmd),
                                         encoding='utf-8')
    c = controls[tag]
    (out / f'Control{tag}Before.lean').write_text(header + c, encoding='utf-8')
    (out / f'Control{tag}After.lean').write_text(header + cmd + '\n' + c, encoding='utf-8')
    print(mod, 'sealed:', len(names))
    for n in names:
        print('  ', n)
