open Lean Meta Elab Command

/-- user-facing name of a constant (private prefix removed) -/
def userStr (n : Name) : String := ((privateToUserName? n).getD n).toString

def matchesTouched (ts : List String) (n : Name) : Bool :=
  let s := userStr n
  ts.any fun t => s == t || s.endsWith ("." ++ t) ||
    (s.splitOn (t ++ ".")).length > 1 && (s.startsWith (t ++ ".") || (s.splitOn ("." ++ t ++ ".")).length > 1)

def isTCS (env : Environment) (c : Name) : Option Name :=
  match env.getModuleIdxFor? c with
  | some mi => let m := env.header.moduleNames[mi.toNat]!; if (`TCSlib).isPrefixOf m then some m else none
  | none => none

syntax (name := collectCmd) "#collect " ident "[" str,* "]" : command

@[command_elab collectCmd] def elabCollect : CommandElab := fun stx => do
  let modN := stx[1].getId
  let ts : List String := (stx[3].getSepArgs.map fun s => s.isStrLit?.getD "").toList
  let env ← getEnv
  let some modIdx := env.getModuleIdx? modN | throwError "no module {modN}"
  let mut ours : Array Name := #[]
  for (n, _) in env.constants.map₁.toList do
    if env.getModuleIdxFor? n == some modIdx && matchesTouched ts n then ours := ours.push n
  -- every touched name must be found
  for t in ts do
    unless ours.any (fun n => userStr n == t || (userStr n).endsWith ("." ++ t)) do
      logWarning m!"TOUCHED-NOT-FOUND {t}"
  -- wide pass: types of all constants reached; values of own-module definitions, transitively
  let mut cs : NameSet := {}
  let mut seen : NameSet := {}
  let mut stack : List Name := []
  for n in ours do
    let some ci := env.find? n | continue
    stack := stack ++ ci.type.getUsedConstants.toList ++ (ci.value?.map (·.getUsedConstants.toList) |>.getD [])
  while !stack.isEmpty do
    let c := stack.head!
    stack := stack.tail!
    if seen.contains c then continue
    seen := seen.insert c
    cs := cs.insert c
    let some cc := env.find? c | continue
    if env.getModuleIdxFor? c == some modIdx then
      stack := stack ++ cc.type.getUsedConstants.toList
      if cc.isDefinition then
        stack := stack ++ (cc.value?.map (·.getUsedConstants.toList) |>.getD [])
  let mut rows : Array String := #[]
  let mut reds : Array String := #[]
  for c in cs.toList do
    let some m := isTCS env c | continue
    if m == modN then continue
    let some cinfo := env.find? c | continue
    unless cinfo.isDefinition do continue
    if isInstanceCore env c then continue
    let isM := (Match.Extension.getMatcherInfo? env c).isSome
    let st ← liftCoreM <| getReducibilityStatus c
    if !isM && st == .reducible then
      reds := reds.push s!"REDUCIBLE {c} | {m}"
      continue
    rows := rows.push s!"SEALROW {modN} | {c} | {m} | matcher={isM} | {repr st}"
  logInfo m!"MODULE {modN}: touched {ts.length}, constants {ours.size}, reached {cs.size}"
  for r in rows.qsort (· < ·) do logInfo m!"{r}"
  for r in reds.qsort (· < ·) do logInfo m!"{r}"

syntax (name := axsCmd) "#axs " ident "[" str,* "]" : command

/-- axioms of every touched top-level declaration of a module (private ones included) -/
@[command_elab axsCmd] def elabAxs : CommandElab := fun stx => do
  let modN := stx[1].getId
  let ts : List String := (stx[3].getSepArgs.map fun s => s.isStrLit?.getD "").toList
  let env ← getEnv
  let some modIdx := env.getModuleIdx? modN | throwError "no module {modN}"
  for t in ts do
    let mut found := false
    for (n, _) in env.constants.map₁.toList do
      if env.getModuleIdxFor? n == some modIdx then
        let s := userStr n
        if s == t || s.endsWith ("." ++ t) then
          found := true
          let axs ← liftCoreM <| collectAxioms n
          let axs := axs.qsort (fun a b => a.toString < b.toString)
          logInfo m!"AXIOMS {modN} | {s} | {axs.toList}"
    unless found do logWarning m!"AXIOMS-NOT-FOUND {t}"
