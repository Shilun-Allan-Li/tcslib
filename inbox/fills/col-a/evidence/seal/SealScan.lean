import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.Protocol
open Lean Elab Command Meta

/-- The foreign TCSlib definitions read by the new declarations of col-a: every constant in the
type or value of a new declaration (recursing into auxiliary declarations: matchers, `proof_`,
`_private` helpers of the same modules), kept when it is a definition of a TCSlib module other
than the module of the declaration being scanned. -/
def owned : Array Name := #[`TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.ColRepWitness,
  `TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.ColRepSound,
  `TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.Protocol]

def isNew (n : Name) : Bool :=
  let s := n.toString
  (s.splitOn "ColRep.").length > 1 || (s.splitOn "colRep_").length > 1 ||
    (s.splitOn "R3COL_witnessRelation").length > 1

#eval show CommandElabM Unit from do
  let env ← getEnv
  let modOf (c : Name) : Option Name := (env.getModuleIdxFor? c).map fun i => env.header.moduleNames[i.toNat]!
  let mut roots : Array Name := #[]
  for (c, _) in env.constants.toList do
    if let some m := modOf c then
      if owned.contains m && isNew c then roots := roots.push c
  let mut seen : NameSet := {}
  let mut todo := roots
  let mut foreign : Std.HashMap Name (Array Name) := {}
  while !todo.isEmpty do
    let c := todo.back!
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    let some ci := env.find? c | continue
    let some mc := modOf c | continue
    let used := ci.type.getUsedConstants ++ (ci.value?.map (·.getUsedConstants) |>.getD #[])
    for u in used do
      let some mu := modOf u | continue
      if mu == mc then
        -- same module: follow auxiliary declarations of new code (and new private defs)
        if !seen.contains u && (isNew u || u.isInternal || (u.toString.splitOn "match_").length > 1 ||
            (u.toString.splitOn "_proof_").length > 1 || (u.toString.splitOn "_private").length > 1 ||
            (u.toString.splitOn "badVertex").length > 1 || (u.toString.splitOn "badEntry").length > 1 ||
            (u.toString.splitOn "scanTest").length > 1 || (u.toString.splitOn "wf_iff").length > 1 ||
            (u.toString.splitOn "enc_iff").length > 1 || (u.toString.splitOn "proper_iff").length > 1 ||
            (u.toString.splitOn "eq_of_xor").length > 1) then
          todo := todo.push u
      else if (mu.toString.startsWith "TCSlib") then
        if let some ui := env.find? u then
          if ui matches .defnInfo _ then
            foreign := foreign.insert u ((foreign.getD u #[]).push c)
  let rs ← liftCoreM <| foreign.toList.mapM fun (u, cs) => do
    let st := getReducibilityStatusCore env u
    let tag := match st with | .reducible => "reducible" | .irreducible => "irreducible" | _ => "regular"
    let proj := (env.getProjectionFnInfo? u).isSome
    let inst := isInstanceCore env u
    let mu := (modOf u).getD .anonymous
    let ownedMod := owned.contains mu
    return s!"{u} | {mu} | {tag}{if proj then " projection" else ""}{if inst then " instance" else ""}{if ownedMod then " OWNED" else ""} | used by {cs.size}"
  for r in rs.toArray.qsort (· < ·) do
    IO.println r
  IO.println s!"roots: {roots.size}, scanned: {seen.toList.length}"
