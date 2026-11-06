import TCSlib.Cryptography.Asymptotic.MultiMessage
import TCSlib.Cryptography.Asymptotic.MultiMessageLemmas
import TCSlib.Cryptography.Asymptotic.PRF
import TCSlib.Cryptography.Asymptotic.PRFLemmas
import TCSlib.Cryptography.Foundations.Experiments
import TCSlib.Cryptography.Foundations.Probability
import TCSlib.Cryptography.Games.Advantage
import TCSlib.Cryptography.Games.BitCodec
import TCSlib.Cryptography.Games.Bridges
import TCSlib.Cryptography.Games.Bridges.Experiments
import TCSlib.Cryptography.Games.Bridges.Machines
import TCSlib.Cryptography.Games.Bridges.QueryTree
import TCSlib.Cryptography.Games.Bridges.Strategies
import TCSlib.Cryptography.Games.Efficiency
import TCSlib.Cryptography.Games.Hopping
import TCSlib.Cryptography.Games.Machines
import TCSlib.Cryptography.Games.OracleComp
import TCSlib.Cryptography.Games.Probability
import TCSlib.Cryptography.Games.Protocols
import TCSlib.Cryptography.Games.Simulate
import TCSlib.Cryptography.Pseudorandom.Functions.Defs
import TCSlib.Cryptography.Pseudorandom.Functions.GGM
import TCSlib.Cryptography.Pseudorandom.Functions.LazySampling
import TCSlib.Cryptography.Pseudorandom.Functions.OracleAdversary
import TCSlib.Cryptography.Pseudorandom.Functions.SubHybrids
import TCSlib.Cryptography.ZeroKnowledge.Interaction

open Lean in
def targetMods : Array Name := #[`TCSlib.Cryptography.Asymptotic.MultiMessage, `TCSlib.Cryptography.Asymptotic.MultiMessageLemmas, `TCSlib.Cryptography.Asymptotic.PRF, `TCSlib.Cryptography.Asymptotic.PRFLemmas, `TCSlib.Cryptography.Foundations.Experiments, `TCSlib.Cryptography.Foundations.Probability, `TCSlib.Cryptography.Games.Advantage, `TCSlib.Cryptography.Games.BitCodec, `TCSlib.Cryptography.Games.Bridges, `TCSlib.Cryptography.Games.Bridges.Experiments, `TCSlib.Cryptography.Games.Bridges.Machines, `TCSlib.Cryptography.Games.Bridges.QueryTree, `TCSlib.Cryptography.Games.Bridges.Strategies, `TCSlib.Cryptography.Games.Efficiency, `TCSlib.Cryptography.Games.Hopping, `TCSlib.Cryptography.Games.Machines, `TCSlib.Cryptography.Games.OracleComp, `TCSlib.Cryptography.Games.Probability, `TCSlib.Cryptography.Games.Protocols, `TCSlib.Cryptography.Games.Simulate, `TCSlib.Cryptography.Pseudorandom.Functions.Defs, `TCSlib.Cryptography.Pseudorandom.Functions.GGM, `TCSlib.Cryptography.Pseudorandom.Functions.LazySampling, `TCSlib.Cryptography.Pseudorandom.Functions.OracleAdversary, `TCSlib.Cryptography.Pseudorandom.Functions.SubHybrids, `TCSlib.Cryptography.ZeroKnowledge.Interaction]
def outDir : System.FilePath := "/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/g04r5/candidates-base"

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
    if isPrivateName n && !isAuxName ((privateToUserName? n).getD n) then "def-private"
    else if isAuxName n || isMatcherCore env n || isAuxRecursor env n || isNoConfusion env n then "def-aux"
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
  cands : Std.HashMap Name (String × Array String × NameSet) := {}  -- cand ↦ (module, vias, owners)
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
    -- source tier: TCSlib lemmas named in the file's simp/rw lemma lists (from the source scan),
    -- whose statements' definitions can enter goals with no trace in the proof term
    let srcFile := outDir / "srclemmas" / s!"{m}.txt"
    let mut srcPairs : Array (Name × Name) := #[]
    if (← srcFile.pathExists) then
      for l in (← IO.FS.readFile srcFile).splitOn "\n" do
        match l.splitOn "\t" with
        | [o, t] => srcPairs := srcPairs.push (o.toName, t.toName)
        | _ => pure ()
    let mut srcConsts : Array ConstantInfo := #[]
    for (o, t) in srcPairs do
      if let some ti := env.find? t then
        let tv : TheoremVal := { name := o, levelParams := [], type := ti.type, value := mkConst t, all := [o] }
        srcConsts := srcConsts.push (.thmInfo tv)
    for (ci, isSrc) in data.constants.map (·, false) ++ srcConsts.map (·, true) do
      st := { st with nsrc := st.nsrc + 1 }
      let owner := ownerOf ci.name
      let selfIsEqn := (genEqnParent? ci.name).isSome
      -- worklist of (constant, via)
      -- worklist of (constant, how it was reached: none = occurs in the declaration,
      -- `inst:I` = in the body of the transparent instance/abbreviation I, `stmt:T` = in the statement
      -- of the TCSlib lemma T that the declaration uses)
      let mut work : Array (Name × Option String) :=
        if isSrc then
          match ci.value? with
          | some (.const t _) => ci.type.getUsedConstantsAsSet.toArray.map (·, some s!"src:{t}")
          | _ => #[]
        else ci.getUsedConstantsAsSet.toArray.map (·, none)
      let mut seen : NameSet := {}
      let mut seenD : NameSet := {}
      while !work.isEmpty do
        let (u, via) := work.back!
        work := work.pop
        if (via.isNone && seenD.contains u) || (via.isSome && seen.contains u) then continue
        let firstTime := !seen.contains u
        seen := seen.insert u
        if via.isNone then seenD := seenD.insert u
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
          let tag := via.getD "direct"
          let vias := if vias.contains tag then vias else vias.push tag
          st := { st with cands := st.cands.insert u (md, vias, owners.insert owner),
                          usesBy := st.usesBy.insert owner ((st.usesBy.getD owner {}).insert u) }
        else if !firstTime then continue
        else if k == "def-instance" || k == "def-reducible" then
          st := { st with transp := st.transp.insert u }
          if let some (.defnInfo dv) := env.find? u then
            for v in dv.value.getUsedConstantsAsSet.toArray do
              unless seen.contains v do work := work.push (v, some (via.getD s!"inst:{u}"))
        else if k == "thm" && via.isNone then
          -- one level: the definitions a used lemma's statement mentions can appear in the goals
          -- that rewriting with it produces (simp applies rfl-lemmas without a proof-term trace)
          if let some ti := env.find? u then
            for v in ti.type.getUsedConstantsAsSet.toArray do
              unless seen.contains v do work := work.push (v, some s!"stmt:{u}")
        else if k == "def-private" || k == "def-aux" then
          -- unsealable helpers (private definitions, matchers, `_unary`/`proof_` auxiliaries, …):
          -- walk their bodies (transitively, foreign TCSlib only) so that a definition they reach
          -- is collected, tagged `aux:<helper>`
          if k == "def-private" then st := { st with privs := st.privs.insert u }
          if let some (.defnInfo dv) := env.find? u then
            for v in dv.value.getUsedConstantsAsSet.toArray do
              unless seen.contains v do work := work.push (v, some (via.getD s!"aux:{u}"))
    -- write the candidate file
    let mut lines : Array String := #[s!"# seal candidates for {m} ({st.nsrc} constants walked)",
      "# format: <candidate>\t<defining module>\t<direct | inst:<transparent instance/abbrev> | stmt:<used lemma, statement> | src:<lemma named in a simp/rw list, statement> | aux:<unsealable helper, body>>\t<declarations of the file using it>"]
    let keys := st.cands.toArray.qsort (fun a b => Name.lt a.1 b.1)
    let nIrr := (keys.filter fun (n, _) => kindOf env n == "def-irreducible").size
    lines := lines.push s!"# {keys.size - nIrr} candidates sealed by the seal line; {nIrr} already `[irreducible]` globally (sealed by construction, listed as `# already-irreducible:`)"
    for (n, (md, vias, owners)) in keys do
      let os := owners.toArray.qsort Name.lt
      let osTxt := ", ".intercalate (os.toList.take 12 |>.map toString) ++
        (if os.size > 12 then s!", … (+{os.size - 12})" else "")
      let pre := if kindOf env n == "def-irreducible" then "# already-irreducible: " else ""
      lines := lines.push s!"{pre}{n}\t{md}\t{", ".intercalate (vias.toList.take 4) ++ (if vias.size > 4 then s!", … (+{vias.size - 4})" else "")}\t{osTxt}"
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
