
/- ===== gate 07 statement sweep: seal-candidate collector (appended to the statement-only copy) =====
Walks every constant declared in this file (the current module of the statement-only copy, in which
every theorem/lemma/example value is `sorry`): the TYPE of every constant (theorems, definitions,
instances, structures and their fields/constructors/recursors, auxiliaries), and the VALUE of every
definition/instance/abbreviation/opaque (theorem values are `sorry`, so proofs contribute nothing).
Every TCSlib constant declared in another module that occurs there is classified:
* `def` (a plain, non-instance, non-reducible, non-projection, non-auxiliary, non-private
  definition): a seal candidate. Its value and its type are walked further (`deep` tier).
* instance / `@[reducible]` (incl. `abbrev`) / private / auxiliary (matcher, `_unary`, …):
  transparent or unnameable, so not sealed; recorded, and their values and types are walked.
* any other constant (theorem, structure, inductive, constructor, projection, axiom, …): its TYPE is
  walked (using a constant can make the elaborator reduce its type), it is not sealed.
`direct` = occurs in this file's types/values; `deep` = reached only through a foreign constant.
Output: SWEEP_OUT.cands.tsv, SWEEP_OUT.uses.tsv, SWEEP_OUT.transparent.tsv -/
namespace SweepCollect
open Lean
def numSuffix (s pre : String) : Bool :=
  s.startsWith pre && (s.drop pre.length).length > 0 && (s.drop pre.length).all Char.isDigit
def isAuxComp (s : String) : Bool :=
  s.startsWith "_" || numSuffix s "match_" || numSuffix s "proof_" || numSuffix s "eq_" ||
    s == "eq_def" || s == "eq_unfold"
def isAuxName : Name → Bool
  | .str p s => isAuxComp s || isAuxName p
  | .num _ _ => true
  | .anonymous => false
end SweepCollect

open Lean Meta in
run_cmd do
  let env ← getEnv
  let outBase : String := SWEEP_OUT_PATH
  let modNames := env.header.moduleNames
  let isTCS (j : ModuleIdx) : Bool := (modNames[j.toNat]!).getRoot == `TCSlib
  let kindOf (n : Name) : String :=
    match env.find? n with
    | some (.defnInfo _) =>
      if isPrivateName n then "private"
      else if SweepCollect.isAuxName n || isMatcherCore env n || isAuxRecursor env n || isNoConfusion env n then "aux"
      else if env.isProjectionFn n then "proj"
      else if isInstanceCore env n then "instance"
      else if getReducibilityStatusCore env n == .reducible then "reducible"
      else if getReducibilityStatusCore env n == .irreducible then "irreducible"
      else "def"
    | some (.thmInfo _) => "thm"
    | some (.axiomInfo _) => "axiom"
    | some (.opaqueInfo _) => "opaque"
    | some (.inductInfo _) => "inductive"
    | some (.ctorInfo _) => "ctor"
    | some (.recInfo _) => "rec"
    | some (.quotInfo _) => "quot"
    | none => "none"
  -- local constants of this file
  let locals := env.constants.map₂.toList.filter fun (n, _) => !(n.components.contains `SweepCollect)
  -- candidate ↦ (tier, via set, owners)
  let mut cands : Std.HashMap Name (String × NameSet × NameSet) := {}
  let mut transp : Std.HashMap Name (String × NameSet) := {}
  let mut uses : Array String := #[]
  for (ln, ci) in locals do
    -- owner: strip auxiliary components / private prefix
    let owner := (privateToUserName? ln).getD ln
    let roots : Array (Name × String) :=
      (ci.type.getUsedConstantsAsSet.toArray.map (·, "T")) ++
      (match ci with
       | .defnInfo dv => dv.value.getUsedConstantsAsSet.toArray.map (·, "V")
       | .opaqueInfo ov => ov.value.getUsedConstantsAsSet.toArray.map (·, "V")
       | .thmInfo tv => tv.value.getUsedConstantsAsSet.toArray.map (·, "V")
       | _ => #[])
    -- worklist: (constant, region T/V, via (anonymous = direct))
    let mut work : Array (Name × String × Name) := roots.map fun (n, r) => (n, r, Name.anonymous)
    let mut seen : Std.HashSet (Name × String) := {}
    let mut found : Array String := #[]
    while !work.isEmpty do
      let (u, r, via) := work.back!
      work := work.pop
      if seen.contains (u, r) then continue
      seen := seen.insert (u, r)
      let some j := env.getModuleIdxFor? u | continue   -- local or unknown: locals are walked as roots
      unless isTCS j do continue
      let some cu := env.find? u | continue
      let k := kindOf u
      let via' := if via.isAnonymous then u else via
      if k == "def" then
        let tier := if via.isAnonymous then "direct" else "deep"
        let (t0, vs, os) := cands.getD u (tier, {}, {})
        let t1 := if t0 == "direct" || tier == "direct" then "direct" else "deep"
        cands := cands.insert u (t1, if via.isAnonymous then vs else vs.insert via, os.insert owner)
        if via.isAnonymous then found := found.push s!"{u}@{r}"
      else if k == "instance" || k == "reducible" || k == "private" || k == "aux" || k == "proj" then
        let (m0, os) := transp.getD u (k, {})
        transp := transp.insert u (m0, os.insert owner)
      -- walk further: the type always; the value of definitions (sealed or transparent)
      for v in cu.type.getUsedConstantsAsSet.toArray do
        unless seen.contains (v, r) do work := work.push (v, r, via')
      if let .defnInfo dv := cu then
        for v in dv.value.getUsedConstantsAsSet.toArray do
          unless seen.contains (v, r) do work := work.push (v, r, via')
    if !found.isEmpty then
      uses := uses.push s!"{owner}\t{ln}\t{" ".intercalate found.toList}"
  let mut cl : Array String := #[]
  for (n, (t, vs, os)) in cands.toArray.qsort (fun a b => Name.lt a.1 b.1) do
    let some j := env.getModuleIdxFor? n | continue
    let vsT := ", ".intercalate ((vs.toArray.qsort Name.lt).toList.take 3 |>.map toString)
    cl := cl.push s!"{n}\t{modNames[j.toNat]!}\t{t}\t{vsT}\t{os.size}"
  IO.FS.writeFile (outBase ++ ".cands.tsv") ("\n".intercalate cl.toList ++ "\n")
  IO.FS.writeFile (outBase ++ ".uses.tsv") ("\n".intercalate uses.toList ++ "\n")
  let mut tl : Array String := #[]
  for (n, (k, os)) in transp.toArray.qsort (fun a b => Name.lt a.1 b.1) do
    let some j := env.getModuleIdxFor? n | continue
    tl := tl.push s!"{n}\t{k}\t{modNames[j.toNat]!}\t{os.size}"
  IO.FS.writeFile (outBase ++ ".transparent.tsv") ("\n".intercalate tl.toList ++ "\n")
  -- own-file dependency graph (for the minimiser's cascade/masking rule): for every local constant,
  -- its declaration line and the declaration lines of the local constants its type/value mentions
  let lineOf (n : Name) : Lean.Elab.Command.CommandElabM Int := do
    let mut cur := n
    for _ in [0:8] do
      if let some r ← Lean.findDeclarationRanges? cur then return (r.range.pos.line : Int)
      if let some u := privateToUserName? cur then
        if let some r ← Lean.findDeclarationRanges? u then return (r.range.pos.line : Int)
      match cur with
      | .str p _ => cur := p
      | .num p _ => cur := p
      | .anonymous => return -1
    return -1
  let localSet : NameSet := locals.foldl (fun s (n, _) => s.insert n) {}
  let mut dl : Array String := #[]
  for (ln, ci) in locals do
    -- theorem values included: top-level theorem values are `sorry` here, but the auxiliary
    -- theorems `D.proof_N` abstracted from a definition's body carry that body's proofs
    let refs := ci.type.getUsedConstantsAsSet.toArray ++
      (match ci with
       | .defnInfo dv => dv.value.getUsedConstantsAsSet.toArray
       | .opaqueInfo ov => ov.value.getUsedConstantsAsSet.toArray
       | .thmInfo tv => tv.value.getUsedConstantsAsSet.toArray
       | _ => #[])
    let mut ls : Array Int := #[]
    for v in refs do
      if localSet.contains v && v != ln then
        let l ← lineOf v
        unless ls.contains l do ls := ls.push l
    let l0 ← lineOf ln
    dl := dl.push s!"{l0}\t{ln}\t{" ".intercalate (ls.toList.map toString)}"
  IO.FS.writeFile (outBase ++ ".deps.tsv") ("\n".intercalate dl.toList ++ "\n")
