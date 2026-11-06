/- Rule-10 seal candidate collector (gate 04 round 4).
For each target module F: walk every constant declared in F's module (type and value), and keep the
constants that are definitions (`ConstantInfo.defnInfo`) declared in a different module under
`TCSlib`, excluding instances, `@[reducible]` declarations, structure projections, auxiliary
recursors / `noConfusion`, matchers and internal or generated auxiliaries (`match_N`, `proof_N`,
`eq_N`, `eq_def`, `eq_unfold`, `_`-components).
A foreign instance or reducible declaration is transparent, so it is not sealed itself; its value is
walked (transitively, foreign `TCSlib` only) and the definitions found there are kept with
`via <instance/abbrev>`.
Also reported: references to the generated equation lemmas (`X.eq_N`, `X.eq_def`, `X.eq_unfold`)
of a foreign `TCSlib` definition `X` from F's declarations, i.e. explicit unfolds visible in
proof terms. -/
open Lean Meta

namespace G04R4Collect

def numSuffix (s pre : String) : Bool :=
  s.startsWith pre && (s.drop pre.length).length > 0 && (s.drop pre.length).all Char.isDigit

def isGenEqnStr (s : String) : Bool := numSuffix s "eq_" || s == "eq_def" || s == "eq_unfold"

def genEqnParent? : Name → Option Name
  | .str p s => if isGenEqnStr s then some p else none
  | _ => none

def isAuxComp (s : String) : Bool :=
  s.startsWith "_" || numSuffix s "match_" || numSuffix s "proof_" || isGenEqnStr s

def isAuxName : Name → Bool
  | .str p s => isAuxComp s || isAuxName p
  | .num _ _ => true
  | .anonymous => false

partial def ownerOf (n : Name) : Name :=
  let n := (privateToUserName? n).getD n
  go n
where
  go : Name → Name
    | n@(.str p s) =>
      if isAuxComp s || ["induct", "mutual_induct", "eq_spec"].contains s then go p else n
    | .num p _ => go p
    | n => n

def kindOf (env : Environment) (n : Name) : String :=
  match env.find? n with
  | some (.defnInfo _) =>
    if isAuxName n || isMatcherCore env n || isAuxRecursor env n || isNoConfusion env n then "def-aux"
    else if env.isProjectionFn n then "def-proj"
    else if isInstanceCore env n then "def-instance"
    else if getReducibilityStatusCore env n == .reducible then "def-reducible"
    else if isPrivateName n then "def-private"
    else if getReducibilityStatusCore env n == .irreducible then "def-irreducible"
    else "def"
  | some (.thmInfo _) => "thm"
  | some (.axiomInfo _) => "axiom"
  | some (.opaqueInfo _) => "opaque"
  | some (.quotInfo _) => "quot"
  | some (.inductInfo _) => "inductive"
  | some (.ctorInfo _) => "ctor"
  | some (.recInfo _) => "rec"
  | none => "none"

structure St where
  cands : Std.HashMap Name (String × Array Name × NameSet) := {}  -- cand ↦ (module, vias, owners)
  usesBy : Std.HashMap Name NameSet := {}                         -- owner ↦ candidates
  eqnHits : Array (Name × Name × Name) := #[]                     -- (owner, decl, eqn lemma)
  transp : NameSet := {}                                          -- foreign instances/abbrevs walked
  privs : NameSet := {}
  nsrc : Nat := 0

end G04R4Collect

open G04R4Collect in
run_cmd do
  let env ← getEnv
  let mods := targetMods
  let modNames := env.header.moduleNames
  let isTCS (j : ModuleIdx) : Bool := (modNames[j.toNat]!).getRoot == `TCSlib
  -- constant table of every imported TCSlib constant (for the source scan)
  let mut table : Array String := #[]
  for j in [0:modNames.size] do
    if (modNames[j]!).getRoot == `TCSlib then
      let d := env.header.moduleData[j]!
      for c in d.constNames do
        table := table.push s!"{c}\t{kindOf env c}\t{modNames[j]!}"
  IO.FS.writeFile (outDir / "tcslib-constants.tsv") ("\n".intercalate table.toList ++ "\n")
  let mut summary : Array String := #[]
  for m in mods do
    let some idx := env.getModuleIdx? m | throwError "module {m} not imported"
    let data := env.header.moduleData[idx.toNat]!
    let mut st : St := {}
    for ci in data.constants do
      st := { st with nsrc := st.nsrc + 1 }
      let owner := ownerOf ci.name
      let selfIsEqn := (genEqnParent? ci.name).isSome
      -- worklist of (constant, via)
      let mut work : Array (Name × Option Name) := ci.getUsedConstantsAsSet.toArray.map (·, none)
      let mut seen : NameSet := {}
      while !work.isEmpty do
        let (u, via) := work.back!
        work := work.pop
        if seen.contains u then continue
        seen := seen.insert u
        -- generated equation lemma of a foreign TCSlib definition (the lemma itself may live anywhere)
        if via.isNone && !selfIsEqn then
          if let some p := genEqnParent? u then
            if let some jp := env.getModuleIdxFor? p then
              if jp != idx && isTCS jp then
                if let some (.defnInfo _) := env.find? p then
                  st := { st with eqnHits := st.eqnHits.push (owner, ci.name, u) }
        let some j := env.getModuleIdxFor? u | continue
        if j == idx || !isTCS j then continue
        let k := kindOf env u
        if k == "def" || k == "def-irreducible" then
          let (md, vias, owners) := st.cands.getD u (toString modNames[j.toNat]!, #[], {})
          let vias := match via with
            | some v => if vias.contains v then vias else vias.push v
            | none => if vias.contains `direct then vias else vias.push `direct
          st := { st with cands := st.cands.insert u (md, vias, owners.insert owner),
                          usesBy := st.usesBy.insert owner ((st.usesBy.getD owner {}).insert u) }
        else if k == "def-instance" || k == "def-reducible" then
          st := { st with transp := st.transp.insert u }
          if let some (.defnInfo dv) := env.find? u then
            for v in dv.value.getUsedConstantsAsSet.toArray do
              unless seen.contains v do work := work.push (v, some (via.getD u))
        else if k == "def-private" then
          st := { st with privs := st.privs.insert u }
    -- write the candidate file
    let mut lines : Array String := #[s!"# seal candidates for {m} ({st.nsrc} constants walked)",
      "# format: <candidate>\t<defining module>\t<direct|via instance/abbrev>\t<declarations of the file using it>"]
    let keys := st.cands.toArray.qsort (fun a b => Name.lt a.1 b.1)
    let nIrr := (keys.filter fun (n, _) => kindOf env n == "def-irreducible").size
    lines := lines.push s!"# {keys.size - nIrr} candidates sealed by the seal line; {nIrr} already `[irreducible]` globally (sealed by construction, listed as `# already-irreducible:`)"
    for (n, (md, vias, owners)) in keys do
      let os := owners.toArray.qsort Name.lt
      let osTxt := ", ".intercalate (os.toList.take 12 |>.map toString) ++
        (if os.size > 12 then s!", … (+{os.size - 12})" else "")
      let pre := if kindOf env n == "def-irreducible" then "# already-irreducible: " else ""
      lines := lines.push s!"{pre}{n}\t{md}\t{", ".intercalate (vias.toList.map toString)}\t{osTxt}"
    IO.FS.writeFile (outDir / s!"{m}.txt") ("\n".intercalate lines.toList ++ "\n")
    -- per-declaration uses
    let mut ul : Array String := #[]
    for (o, s) in st.usesBy.toArray.qsort (fun a b => Name.lt a.1 b.1) do
      ul := ul.push s!"{o}: {" ".intercalate ((s.toArray.qsort Name.lt).toList.map toString)}"
    IO.FS.writeFile (outDir / s!"{m}.uses.txt") ("\n".intercalate ul.toList ++ "\n")
    -- equation-lemma hits
    let mut el : Array String := #[]
    for (o, d, e) in st.eqnHits do
      el := el.push s!"{m}\t{o}\t{d}\t{e}"
    IO.FS.writeFile (outDir / s!"{m}.eqn.txt") ("\n".intercalate el.toList ++ (if el.isEmpty then "" else "\n"))
    let tr := ", ".intercalate ((st.transp.toArray.qsort Name.lt).toList.map toString)
    let pv := ", ".intercalate ((st.privs.toArray.qsort Name.lt).toList.map toString)
    summary := summary.push s!"{m}\tcandidates={keys.size}\talreadyIrreducible={nIrr}\teqnHits={st.eqnHits.size}\ttransparent=[{tr}]\tprivateForeign=[{pv}]"
  IO.FS.writeFile (outDir / "summary.tsv") ("\n".intercalate summary.toList ++ "\n")
