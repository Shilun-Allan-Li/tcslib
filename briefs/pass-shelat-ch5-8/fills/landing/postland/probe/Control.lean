import TCSlib.Cryptography.Asymptotic
import TCSlib.Cryptography.ZeroKnowledge
import TCSlib.Cryptography.ZeroKnowledge.NP
import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring
open Lean Meta Elab Command

def C : Name := `TCSlib.Cryptography.Candidates
def TC : Name := `TCSlib.Cryptography.ZeroKnowledge.ThreeColoring
def sweepMods : List Name :=
  [`TCSlib.Cryptography.Asymptotic.Universal, `TCSlib.Cryptography.Asymptotic.UniversalPadding]

/-- The declarations in a constant's closure whose own type or value mentions `sorryAx`. -/
def sorrySources (env : Environment) (root : Name) : Array Name := Id.run do
  let mut seen : NameSet := {}
  let mut todo := #[root]
  let mut out := #[]
  while !todo.isEmpty do
    let c := todo.back!
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    let some ci := env.find? c | continue
    let used := ci.type.getUsedConstants ++ (ci.value?.map (·.getUsedConstants) |>.getD #[])
    if used.contains ``sorryAx then out := out.push c
    for u in used do
      if !seen.contains u then todo := todo.push u
  return out

elab "#axsweep" : command => do
  let env ← getEnv
  let std : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut tot : Nat := 0
  let mut totPub : Nat := 0
  let mut totBad : Nat := 0
  for mn in sweepMods do
    let some idx := env.getModuleIdx? mn | do logInfo m!"MISSING MODULE {mn}"; continue
    let mut ours : Array Name := #[]
    for (n, _) in env.constants.map₁.toList do
      if env.getModuleIdxFor? n == some idx then ours := ours.push n
    let mut bad : Nat := 0
    let mut pub : Nat := 0
    for n in ours.qsort (fun a b => a.toString < b.toString) do
      if !isPrivateName n && !n.isInternal then pub := pub + 1
      let ax ← liftCoreM <| Lean.collectAxioms n
      let nonstd := ax.filter (fun a => !std.contains a)
      if nonstd.size > 0 then
        bad := bad + 1
        logInfo m!"AX-NONSTD {n} (private={isPrivateName n}): {ax.toList} SORRYSRC {sorrySources env n}"
    tot := tot + ours.size; totPub := totPub + pub; totBad := totBad + bad
    logInfo m!"SWEEP {mn}: {ours.size} constants ({pub} public, non-internal), non-standard: {bad}"
  logInfo m!"SWEEP TOTAL: {tot} constants ({totPub} public), non-standard: {totBad}"

#axsweep
