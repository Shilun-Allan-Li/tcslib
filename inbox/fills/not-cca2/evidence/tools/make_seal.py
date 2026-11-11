"""Build the r2 seal files from the reference census (refs-final.log).

For each changed file, the seal copies the file's body into a probe module and makes every
semireducible foreign candidate `local irreducible` (instance-aware, as round 1) in a section
around the touched declarations (the whole body for OracleFromPRF). A control that unfolds one
sealed definition by `rfl` is generated before and after the seal.
Usage: python3 -I make_seal.py <clone> <refs-log> <evidence-dir>
"""
import json
import sys
from pathlib import Path

clone, refs, evid = Path(sys.argv[1]), Path(sys.argv[2]), Path(sys.argv[3])
EXEMPT = {'Complexity.PolyExpr.eval': 'notation explicitly exempted by the issued brief'}
EXTRA = {  # sealed in addition to the census (definitions reached only through readers)
    'TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF': [
        'TCSlib.Cryptography.Games.bitCodec', 'TCSlib.Cryptography.prfDecWF',
        'Complexity.NUPPT.inCoins']}
FILES = {
    'TCSlib.Cryptography.Encryption.PrivateKey.FromPRF': dict(
        start='/-- The decryption machine of `prfScheme F E hE hFE` is',
        stop='      NUPPT.ofPolyTimeUniform (polyTimeComputable_prfDecFun hE) (.const 0) := rfl\n',
        control='example (x a : List Bool) :\n    Turing.pairEncode x a = (x.flatMap fun b => [b, b]) ++ [false, true] ++ a := by\n  rfl\n'),
    'TCSlib.Cryptography.Encryption.PrivateKey.OracleSecurity': dict(
        start='/-- The decryption oracle accepts a ciphertext at the fixed ciphertext width:',
        stop='  simpa only [cast_eq] using S.indImpl_challenge_none atk b n k mm\n',
        control='example (d : ℕ) (j : Fin d) : TCSlib.Cryptography.Games.zeroBits d j = false := by\n  rfl\n'),
    'TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF': dict(
        start=None, stop=None,
        control='example (S : TCSlib.Cryptography.Composability.FixedLengthScheme) (n : ℕ) :\n    S.inLens n 2 = n + n := by\n  rfl\n'),
}
rows = {}
for line in refs.read_text().splitlines():
    if 'CANDIDATE|' not in line:
        continue
    own, name, home, status, inst, proj = line.split('CANDIDATE|', 1)[1].split('|')[:6]
    r = rows.setdefault((own, name), dict(file=own, name=name, home=home, status=status,
        instance=inst == 'instance=true', projection=proj.strip() == 'projection=true'))
for own, extra in EXTRA.items():
    for name in extra:
        rows.setdefault((own, name), dict(file=own, name=name, home='(extra)', status='extra',
            instance=False, projection=False))
for r in rows.values():
    if r['name'] in EXEMPT:
        r['skipped'] = EXEMPT[r['name']]
    elif r['status'].endswith('.reducible'):
        r['skipped'] = 'primitive structure projection (reducible)' if r['projection'] else 'abbreviation (reducible)'
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

out = clone / 'NotCca2Probe'
for mod, spec in FILES.items():
    tag = mod.split('.')[-1]
    names = [r['name'] for r in table if r['file'] == mod and not r['skipped']]
    src = (clone / (mod.replace('.', '/') + '.lean')).read_text()
    imports = [l for l in src.splitlines() if l.startswith('import ')]
    header = 'import Lean\n' + '\n'.join(imports) + '\n\n'
    body = src[src.index('set_option maxHeartbeats'):]
    cmd = seal_cmd(names, tag)
    if spec['start'] is None:
        anchor = 'open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games\n'
        assert body.count(anchor) == 1
        sealed = body.replace(anchor, anchor + '\n' + cmd)
    else:
        i = body.index(spec['start']); j = body.index(spec['stop'], i) + len(spec['stop'])
        sealed = body[:i] + 'section NotCca2Seal\n\n' + cmd + '\n' + body[i:j] + '\nend NotCca2Seal\n' + body[j:]
    (out / f'Seal{tag}.lean').write_text(header + sealed)
    (out / f'Control{tag}Before.lean').write_text(header + spec['control'])
    (out / f'Control{tag}After.lean').write_text(header + cmd + '\n' + spec['control'])
    print(mod, 'sealed:', len(names))
    for n in names:
        print('  ', n)
