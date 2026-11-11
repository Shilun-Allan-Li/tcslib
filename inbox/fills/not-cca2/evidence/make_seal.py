"""Build a replay seal from the elaborated type-and-value reference census."""
import json
from pathlib import Path
import sys

log = Path(sys.argv[1]).read_text()
rows = {}
for line in log.splitlines():
    if 'CANDIDATE|' not in line:
        continue
    name, home, status, instance, *extra = line.split('CANDIDATE|', 1)[1].split('|')
    projection = 'projection=true' in extra
    reason = 'abbreviation' if status.endswith('.reducible') and instance != 'instance=true' else None
    if reason and projection:
        reason = 'primitive structure projection (reducible)'
    if name == 'Complexity.PolyExpr.eval':
        reason = 'notation explicitly exempted by issued brief'
    rows[name] = dict(name=name, home=home, status=status,
                      instance=instance == 'instance=true', primitive_projection=projection, skipped=reason)
rows = [rows[name] for name in sorted(rows)]
Path('../not-cca2/evidence/seal-candidates.json').write_text(json.dumps(rows, indent=2) + '\n')
active = [row for row in rows if not row['skipped']]
header = 'import Lean\nimport TCSlib.Cryptography.Encryption.PrivateKey.OracleSecurity\nimport TCSlib.Cryptography.Encryption.PrivateKey.FromPRF\nimport Mathlib.Tactic.Simps.Basic\n\n'
names = ',\n    '.join(json.dumps(row['name']) for row in active)
seal = '''run_cmd do
  let names : Array String := #[
    %s]
  for index in [:names.size] do
    let spelling := names[index]!
    let name := spelling.toName
    let some ci := (← Lean.getEnv).find? name | throwError "Missing seal candidate {name}"
    unless ci.isDefinition do throwError "Nondefinition seal candidate {name}"
    if Lean.Meta.isInstanceCore (← Lean.getEnv) name then
      Lean.Elab.Command.elabCommand (← `(command| attribute [-instance] $(Lean.mkIdent name):ident))
      let aliasName := ("notCca2SealInstance" ++ toString index).toName
      Lean.Elab.Command.liftCoreM <| Lean.addDecl (.defnDecl {
        name := aliasName, levelParams := ci.levelParams, type := ci.type,
        value := Lean.mkConst name (ci.levelParams.map Lean.Level.param),
        hints := .abbrev, safety := .safe })
      Lean.Elab.Command.elabCommand (← `(command| attribute [local instance] $(Lean.mkIdent aliasName):ident))
      unless !(Lean.Meta.isInstanceCore (← Lean.getEnv) name) do
        throwError "Original instance remains registered: {name}"
      Lean.logInfo m!"INSTANCE_ALIAS|{name}|{aliasName}"
    Lean.Elab.Command.elabCommand (← `(command| attribute [local irreducible] $(Lean.mkIdent name):ident))
    let status ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus name
    unless status == .irreducible do throwError "Seal not installed for {name}"
    Lean.logInfo m!"SEALED|{name}|{repr status}"
''' % names
source = Path('TCSlib/Cryptography/Encryption/PrivateKey/OracleFromPRF.lean').read_text()
body = source[source.index('set_option maxHeartbeats'):]
control = '''example (z : List Bool) : Complexity.NUPPT.inArg z =
    Complexity.pairSndD (Complexity.pairFstD (Complexity.pairFstD z)) := by
  rfl
'''
out = Path('../not-cca2/evidence')
(out / 'Seal.lean').write_text(header + seal + '\n' + body)
(out / 'ControlBefore.lean').write_text(header + control)
(out / 'ControlAfter.lean').write_text(header + seal + '\n' + control)
print('Candidates:', len(rows), 'active:', len(active), 'instances:', sum(r['instance'] for r in active))
for row in rows:
    print(row['name'], row['skipped'] or 'SEALED')
