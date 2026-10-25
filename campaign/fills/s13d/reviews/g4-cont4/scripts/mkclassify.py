import sys, json
calls = json.load(open(sys.argv[1]))
decls = set(json.load(open(sys.argv[2]))['all'])
ids = {}
for c in calls:
    for i in c['ids']:
        ids.setdefault(i, c['line'])
own = sorted(i for i in ids if i in decls or i.split('.')[0] in decls)
rest = sorted(i for i in ids if i not in own)
hdr = '''import TCSlib.Complexity.TuringMachine.Build.ZoneTape
import TCSlib.Complexity.TuringMachine.Build.Contract.Basic
import TCSlib.Complexity.TuringMachine.Build.Contract.Catalog
import TCSlib.Complexity.TuringMachine.Build.Contract.Seam
import TCSlib.Complexity.TuringMachine.Build.ZoneRebalance

open Lean Elab Command Meta in
elab "#rv_kind " s:str : command => liftTermElabM do
  let str := s.getString
  let n := str.toName
  let env ← getEnv
  let cands ← resolveGlobalName n
  let exact := cands.filter (fun (_, fs) => fs.isEmpty)
  let pick := if exact.isEmpty then cands else exact
  if pick.isEmpty then
    logInfo m!"RVK {str} | unresolved"
  else
    for (c, fs) in pick do
      let modName := match env.getModuleIdxFor? c with
        | some i => (env.header.moduleNames[i]?).getD `none
        | none => `this
      let kind := match env.find? c with
        | some (.thmInfo _) => "thm" | some (.defnInfo _) => "def" | some (.inductInfo _) => "induct"
        | some (.ctorInfo _) => "ctor" | some (.recInfo _) => "rec" | some (.axiomInfo _) => "axiom"
        | some (.opaqueInfo _) => "opaque" | some (.quotInfo _) => "quot" | none => "?"
      let red := match getReducibilityStatusCore env c with
        | .reducible => "reducible" | .semireducible => "semireducible" | .irreducible => "irreducible"
      let simps ← Meta.getSimpTheorems
      let su := simps.isDeclToUnfold c
      let sl := simps.isLemma (.decl c)
      let proj := env.isProjectionFn c
      let inst := Meta.isInstanceCore env c
      let sp := (Simp.getSimprocDeclKeys? env c).isSome
      logInfo m!"RVK {str} | {c} | fields {fs} | {modName} | {kind} | {red} | proj={proj} | inst={inst} | simpUnfold={su} | simpLemma={sl} | simproc={sp}"

namespace Turing

'''
body = ''.join(f'#rv_kind "{i}"\n' for i in rest)
open(sys.argv[3], 'w', encoding='utf-8').write(hdr + body + '\nend Turing\n')
json.dump({'own': own, 'rest': rest, 'first_line': ids}, open(sys.argv[4], 'w'), ensure_ascii=False, indent=0)
print('distinct', len(ids), 'own-file', len(own), 'to classify', len(rest))
