"""Generate chunked, source-bound native statement/axiom census; starts no Lean."""
from pathlib import Path
import json,sys,hashlib,math
snap=Path(sys.argv[1]);out=Path(sys.argv[2]);mods=(snap/'modules.txt').read_text().splitlines()
log=(snap/'collector-run/mods/.lake_io-phfe-rule10_Collect.log').read_text()
count=sum(l.startswith('ROOT ') for l in log.splitlines())
source='import Lean\n'+''.join('import '+m+'\n' for m in mods)+'''
set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option pp.all true
set_option pp.maxSteps 100000000
open Lean Elab Command

def censusOwners : List Name := [
'''+',\n'.join('  `'+m for m in mods)+''']


def censusOwned (env : Environment) : Array (Name × ConstantInfo) :=
  (env.constants.toList.toArray.filter fun (n, _) =>
    match env.getModuleIdxFor? n with
    | none => false
    | some i => censusOwners.contains env.header.moduleNames[i.toNat]!).qsort
      (fun a b => a.1.toString < b.1.toString)

def censusAxioms (cache : IO.Ref (Std.HashMap Name (Array Name))) (n : Name) : CommandElabM (Array Name) := do
  if let some ax := (← cache.get)[n]? then return ax
  let ax ← Lean.collectAxioms n
  cache.modify (·.insert n ax)
  return ax

def censusTrace (cache : IO.Ref (Std.HashMap Name (Array Name))) (n : Name) : CommandElabM (List Name) := do
  let env ← getEnv
  let mut seen : Std.HashSet Name := {}
  let mut stack : List (Name × List Name) := [(n, [n])]
  while !stack.isEmpty do
    let (a, path) := stack.head!
    stack := stack.tail!
    if seen.contains a then continue
    seen := seen.insert a
    if a == ``sorryAx then return path.reverse
    if let some c := env.find? a then
      let mut refs := c.type.getUsedConstants ++
        ((c.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[]
      if let .inductInfo v := c then refs := refs ++ v.ctors.toArray
      if refs.contains ``sorryAx then return (``sorryAx :: path).reverse
      for b in refs do
        unless seen.contains b do
          if (← censusAxioms cache b).contains ``sorryAx then
            stack := (b, b :: path) :: stack
  throwError "sorryAx dependency had no path: {n}"

def censusChunk (start amount : Nat) : CommandElabM Unit := do
  let env ← getEnv
  let cache ← IO.mkRef ({} : Std.HashMap Name (Array Name))
  let mut count := 0
  let mut sorryCount := 0
  let mut badCount := 0
  for (n, ci) in ((censusOwned env).toList.drop start).take amount do
    let typ ← liftTermElabM <| Lean.Meta.ppExpr ci.type
    IO.println ("PHFE_STMT " ++ (Json.mkObj [("name", toJson n.toString),
      ("module", toJson env.header.moduleNames[(env.getModuleIdxFor? n).get!.toNat]!.toString),
      ("type", toJson typ.pretty)]).compress)
    let ax ← censusAxioms cache n
    let bad := ax.filter fun a => !([``propext, ``Classical.choice, ``Quot.sound].contains a)
    let admitted := ax.contains ``sorryAx
    sorryCount := sorryCount + admitted.toNat
    badCount := badCount + (!bad.isEmpty).toNat
    IO.println ("PHFE_AXIOMS " ++ (Json.mkObj [("name", toJson n.toString),
      ("axioms", toJson (ax.map (·.toString))),
      ("nonstandard", toJson (bad.map (·.toString)))]).compress)
    elabCommand (← `(command| #print axioms $(mkIdent n)))
    if admitted then
      let trace ← censusTrace cache n
      IO.println ("PHFE_SORRY_TRACE " ++ (Json.mkObj [("name", toJson n.toString),
        ("path", toJson (trace.map (·.toString)))]).compress)
    count := count + 1
  IO.println ("PHFE_CENSUS_CHUNK " ++ (Json.mkObj [("start", toJson start),
    ("count", toJson count), ("sorryAx_dependent", toJson sorryCount),
    ("nonstandard_dependent", toJson badCount)]).compress)
'''
starts=range(0,count,50) if len(sys.argv)<4 else [int(x) for x in sys.argv[3].split(',')]
for start in starts:source+=f'\nrun_cmd censusChunk {start} 50\n'
source+='''
run_cmd do
  let expected := (censusOwned (← getEnv)).size
  IO.println ("PHFE_CENSUS_DONE " ++ (Json.mkObj [("stored", toJson expected)]).compress)
'''
marker={'head':json.loads((snap/'snapshot.json').read_text())['head_at_snapshot'],'snapshot_sha256':hashlib.sha256((snap/'snapshot.json').read_bytes()).hexdigest()}
source+='\nrun_cmd IO.println '+json.dumps('PHFE_SNAPSHOT '+json.dumps(marker))+'\n'
out.parent.mkdir(parents=True,exist_ok=True);out.write_text(source)
print('generated',out,'stored',count,'chunks',math.ceil(count/50))
