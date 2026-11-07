import TCSlib.Cryptography.Candidates

/-! S2 Rule-10 collector (evidence probe; not library source). Adapted from the Gate 08 round-2
collectors (`CollectExpanded`, `CollectConservative`, same exclusions):
* `#s2closure M [deps]` — conservative list: every ordinary definition (instances and reducible
  non-matchers excluded, matchers included; `Complexity.PolyExpr.eval` and
  `TCSlib.Cryptography.glNeed` as documented) of the TCSlib modules in `M`'s import closure.
* `#s2collect M [names]` — elaborated reads: constants reached from the types and values of the
  named declarations of `M` (private and generated helpers included: every constant of `M` whose
  user name is a touched name or extends one), transitively through `M`'s own definitions; the
  foreign TCSlib definitions among them (`SEALROW`), reducible ones listed separately.
  With the name list `["*"]` every constant of `M` is a root.
* `#s2axs M [names]` — axioms of every constant of `M` with a touched user name. -/
open Lean Meta Elab Command

def s2UserStr (n : Name) : String := ((privateToUserName? n).getD n).toString

def s2Touched (ts : List String) (n : Name) : Bool :=
  ts.contains "*" ||
  let s := s2UserStr n
  ts.any fun t => s == t || s.endsWith ("." ++ t) || s.startsWith (t ++ ".") ||
    (s.splitOn ("." ++ t ++ ".")).length > 1

syntax (name := s2closureCmd) "#s2closure " ident "[" ident,* "]" : command
@[command_elab s2closureCmd] def s2closure : CommandElab := fun stx => do
  let audited := stx[1].getId
  let deps := stx[3].getSepArgs.map Syntax.getId
  let env ← getEnv
  for dep in deps do
    unless (env.getModuleIdx? dep).isSome do throwError "missing dependency {dep}"
  let mut rows : Array String := #[]
  for (n, ci) in env.constants.map₁.toList do
    let some mi := env.getModuleIdxFor? n | continue
    let home := env.header.moduleNames[mi.toNat]!
    unless deps.contains home do continue
    unless ci.isDefinition do continue
    if isInstanceCore env n then continue
    let matcher := (Match.Extension.getMatcherInfo? env n).isSome
    let status ← liftCoreM <| getReducibilityStatus n
    if !matcher && status == .reducible then continue
    if n == `Complexity.PolyExpr.eval || n == `TCSlib.Cryptography.glNeed then continue
    rows := rows.push s!"CLOSUREROW {audited} | {n} | {home}"
  for row in rows.qsort (· < ·) do logInfo m!"{row}"

syntax (name := s2collectCmd) "#s2collect " ident "[" str,* "]" : command
@[command_elab s2collectCmd] def s2collect : CommandElab := fun stx => do
  let modN := stx[1].getId
  let ts : List String := (stx[3].getSepArgs.map fun s => s.isStrLit?.getD "").toList
  let env ← getEnv
  let some modIdx := env.getModuleIdx? modN | throwError "no module {modN}"
  let mut ours : Array Name := #[]
  for (n, _) in env.constants.map₁.toList do
    if env.getModuleIdxFor? n == some modIdx && s2Touched ts n then ours := ours.push n
  for t in ts do
    unless t == "*" || ours.any (fun n => s2UserStr n == t || (s2UserStr n).endsWith ("." ++ t)) do
      logWarning m!"TOUCHED-NOT-FOUND {t}"
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
    let some cc := env.find? c | continue
    stack := stack ++ cc.type.getUsedConstants.toList
    if env.getModuleIdxFor? c == some modIdx && cc.isDefinition then
      stack := stack ++ (cc.value?.map (·.getUsedConstants.toList) |>.getD [])
  let mut rows : Array String := #[]
  let mut reds : Array String := #[]
  for c in seen.toList do
    let some mi := env.getModuleIdxFor? c | continue
    let m := env.header.moduleNames[mi.toNat]!
    unless (`TCSlib).isPrefixOf m do continue
    if m == modN then continue
    let some cinfo := env.find? c | continue
    unless cinfo.isDefinition do continue
    if isInstanceCore env c then continue
    let isM := (Match.Extension.getMatcherInfo? env c).isSome
    let st ← liftCoreM <| getReducibilityStatus c
    if !isM && st == .reducible then
      reds := reds.push s!"REDUCIBLE {modN} | {c} | {m}"
      continue
    rows := rows.push s!"SEALROW {modN} | {c} | {m} | matcher={isM} | {repr st}"
  logInfo m!"MODULE {modN}: names {ts.length}, constants {ours.size}, reached {seen.size}"
  for r in rows.qsort (· < ·) do logInfo m!"{r}"
  for r in reds.qsort (· < ·) do logInfo m!"{r}"

syntax (name := s2axsCmd) "#s2axs " ident "[" str,* "]" : command
@[command_elab s2axsCmd] def s2axs : CommandElab := fun stx => do
  let modN := stx[1].getId
  let ts : List String := (stx[3].getSepArgs.map fun s => s.isStrLit?.getD "").toList
  let env ← getEnv
  let some modIdx := env.getModuleIdx? modN | throwError "no module {modN}"
  let mut rows : Array String := #[]
  for (n, _) in env.constants.map₁.toList do
    if env.getModuleIdxFor? n == some modIdx && s2Touched ts n then
      let axs ← liftCoreM <| collectAxioms n
      let axs := axs.qsort (fun a b => a.toString < b.toString)
      rows := rows.push s!"AXIOMS {modN} | {s2UserStr n} | {axs.toList}"
  for r in rows.qsort (· < ·) do logInfo m!"{r}"

syntax (name := s2kindCmd) "#s2kind " ident "[" str,* "]" : command
/-- Resolve each identifier in the current scope (namespace and `open`s as in the owned file):
its declaration kind, reducibility and home module; `UNRESOLVED` for locals/own private names. -/
@[command_elab s2kindCmd] def s2kind : CommandElab := fun stx => do
  let modN := stx[1].getId
  let ids : List String := (stx[3].getSepArgs.map fun s => s.isStrLit?.getD "").toList
  let env ← getEnv
  for s in ids do
    let id := mkIdent (s.toName)
    let r ← liftCoreM <| (do
      let ns ← realizeGlobalConstWithInfos id
      pure (some ns)) <|> pure none
    match r with
    | none => logInfo m!"KIND {modN} | {s} | UNRESOLVED"
    | some ns =>
      for n in ns do
        let some ci := env.find? n | continue
        let k := match ci with
          | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .axiomInfo _ => "axiom"
          | .opaqueInfo _ => "opaque" | .ctorInfo _ => "ctor" | .recInfo _ => "rec"
          | .inductInfo _ => "inductive" | .quotInfo _ => "quot"
        let home := match env.getModuleIdxFor? n with
          | some mi => env.header.moduleNames[mi.toNat]!.toString | none => "<current>"
        let st ← liftCoreM <| getReducibilityStatus n
        logInfo m!"KIND {modN} | {s} | {n} | {k} | {repr st} | {home}"

#s2closure TCSlib.Cryptography.Candidates.Concrete [TCSlib.Complexity.ClassNP.CoNP, TCSlib.Complexity.ClassNP.CounterProgPolyTime, TCSlib.Complexity.ClassNP.NP, TCSlib.Complexity.ClassNP.PClosure, TCSlib.Complexity.ClassNP.PolyTime, TCSlib.Complexity.ClassNP.PolyTimeBlockLoop, TCSlib.Complexity.ClassNP.PolyTimeBlockMajority, TCSlib.Complexity.ClassNP.PolyTimeBlockTests, TCSlib.Complexity.ClassNP.PolyTimePairing, TCSlib.Complexity.ClassNP.PolyTimePrefix, TCSlib.Complexity.ClassP.DTIME, TCSlib.Complexity.ClassP.P, TCSlib.Complexity.ClassP.TimeConstructible, TCSlib.Complexity.PolyHierarchy.Padding, TCSlib.Complexity.Randomized.Build.IterateFind, TCSlib.Complexity.Randomized.Build.IterateFindHost, TCSlib.Complexity.Randomized.Build.PairSplit, TCSlib.Complexity.Randomized.Build.StateLoop, TCSlib.Complexity.Randomized.Build.StringLoops, TCSlib.Complexity.Randomized.Build.UnaryMul, TCSlib.Complexity.Randomized.Closure, TCSlib.Complexity.Randomized.PPT, TCSlib.Complexity.Randomized.PolyExpr, TCSlib.Complexity.Randomized.Primitives, TCSlib.Complexity.Randomized.Repetition, TCSlib.Complexity.TuringMachine.Build.Convention, TCSlib.Complexity.TuringMachine.Build.Embed, TCSlib.Complexity.TuringMachine.Build.EmitIterBody, TCSlib.Complexity.TuringMachine.Build.EmitIterEmbed, TCSlib.Complexity.TuringMachine.Build.Loop, TCSlib.Complexity.TuringMachine.Build.ModuleHost, TCSlib.Complexity.TuringMachine.Build.Primitives, TCSlib.Complexity.TuringMachine.Build.Wrappers, TCSlib.Complexity.TuringMachine.Composition, TCSlib.Complexity.TuringMachine.Configuration, TCSlib.Complexity.TuringMachine.CounterProg, TCSlib.Complexity.TuringMachine.CounterProgInput, TCSlib.Complexity.TuringMachine.CounterProgRun, TCSlib.Complexity.TuringMachine.Deterministic, TCSlib.Complexity.TuringMachine.Encoding, TCSlib.Complexity.TuringMachine.Finite, TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction, TCSlib.Complexity.TuringMachine.Robustness.SingleTape, TCSlib.Complexity.TuringMachine.Simulation, TCSlib.Complexity.TuringMachine.StateRenaming, TCSlib.Complexity.TuringMachine.Sweep, TCSlib.Complexity.TuringMachine.UnaryTape, TCSlib.Cryptography.Asymptotic.Adversary, TCSlib.Cryptography.Asymptotic.CollectionsHelpers, TCSlib.Cryptography.Asymptotic.Sampling, TCSlib.Cryptography.Candidates.Arithmetic, TCSlib.Cryptography.Foundations.Experiments, TCSlib.Cryptography.Foundations.Probability, TCSlib.Cryptography.HardcoreBit.Basic, TCSlib.Cryptography.NumberTheory.Chebyshev, TCSlib.Cryptography.NumberTheory.Primality, TCSlib.Cryptography.NumberTheory.Units, TCSlib.Cryptography.OneWayFunctions.Amplification, TCSlib.Cryptography.OneWayFunctions.Basic, TCSlib.InformationTheory.FinDist, TCSlib.InformationTheory.StatisticalDistance]
#s2closure TCSlib.Cryptography.Candidates.DiscreteLog [TCSlib.Complexity.CircuitComplexity.Advice, TCSlib.Complexity.CircuitComplexity.Basic, TCSlib.Complexity.CircuitComplexity.DAGCircuit, TCSlib.Complexity.CircuitComplexity.DAGFanin, TCSlib.Complexity.CircuitComplexity.DAGTransform, TCSlib.Complexity.CircuitComplexity.LayeredCircuit, TCSlib.Complexity.CircuitComplexity.LayeredDAG, TCSlib.Complexity.CircuitComplexity.LayeredPPoly, TCSlib.Complexity.CircuitComplexity.PPoly, TCSlib.Complexity.CircuitComplexity.SizeClasses, TCSlib.Complexity.CircuitComplexity.TreeDAG, TCSlib.Complexity.ClassNP.CoNP, TCSlib.Complexity.ClassNP.CounterProgPolyTime, TCSlib.Complexity.ClassNP.NP, TCSlib.Complexity.ClassNP.PClosure, TCSlib.Complexity.ClassNP.PolyTime, TCSlib.Complexity.ClassNP.PolyTimeBlockLoop, TCSlib.Complexity.ClassNP.PolyTimeBlockMajority, TCSlib.Complexity.ClassNP.PolyTimeBlockTests, TCSlib.Complexity.ClassNP.PolyTimePairing, TCSlib.Complexity.ClassNP.PolyTimePrefix, TCSlib.Complexity.ClassP.DTIME, TCSlib.Complexity.ClassP.P, TCSlib.Complexity.ClassP.TimeConstructible, TCSlib.Complexity.PolyHierarchy.Padding, TCSlib.Complexity.Randomized.Build.IterateFind, TCSlib.Complexity.Randomized.Build.IterateFindHost, TCSlib.Complexity.Randomized.Build.PairSplit, TCSlib.Complexity.Randomized.Build.StateLoop, TCSlib.Complexity.Randomized.Build.StringLoops, TCSlib.Complexity.Randomized.Build.UnaryMul, TCSlib.Complexity.Randomized.Closure, TCSlib.Complexity.Randomized.NonUniform, TCSlib.Complexity.Randomized.PPT, TCSlib.Complexity.Randomized.PolyExpr, TCSlib.Complexity.Randomized.Primitives, TCSlib.Complexity.Randomized.Repetition, TCSlib.Complexity.TuringMachine.Build.Convention, TCSlib.Complexity.TuringMachine.Build.Embed, TCSlib.Complexity.TuringMachine.Build.EmitIterBody, TCSlib.Complexity.TuringMachine.Build.EmitIterEmbed, TCSlib.Complexity.TuringMachine.Build.Loop, TCSlib.Complexity.TuringMachine.Build.ModuleHost, TCSlib.Complexity.TuringMachine.Build.Primitives, TCSlib.Complexity.TuringMachine.Build.Wrappers, TCSlib.Complexity.TuringMachine.Composition, TCSlib.Complexity.TuringMachine.Configuration, TCSlib.Complexity.TuringMachine.CounterProg, TCSlib.Complexity.TuringMachine.CounterProgInput, TCSlib.Complexity.TuringMachine.CounterProgRun, TCSlib.Complexity.TuringMachine.Deterministic, TCSlib.Complexity.TuringMachine.Encoding, TCSlib.Complexity.TuringMachine.Finite, TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction, TCSlib.Complexity.TuringMachine.Robustness.SingleTape, TCSlib.Complexity.TuringMachine.Simulation, TCSlib.Complexity.TuringMachine.StateRenaming, TCSlib.Complexity.TuringMachine.Sweep, TCSlib.Complexity.TuringMachine.UnaryTape, TCSlib.Cryptography.Asymptotic.Adversary, TCSlib.Cryptography.Asymptotic.Collections, TCSlib.Cryptography.Asymptotic.CollectionsHelpers, TCSlib.Cryptography.Asymptotic.CollectionsLemmas, TCSlib.Cryptography.Asymptotic.OneWay, TCSlib.Cryptography.Asymptotic.OneWayLemmas, TCSlib.Cryptography.Asymptotic.OneWayYao, TCSlib.Cryptography.Asymptotic.Sampling, TCSlib.Cryptography.Candidates.Arithmetic, TCSlib.Cryptography.Candidates.Concrete, TCSlib.Cryptography.Foundations.Experiments, TCSlib.Cryptography.Foundations.Negligible, TCSlib.Cryptography.Foundations.Probability, TCSlib.Cryptography.HardcoreBit.Basic, TCSlib.Cryptography.NumberTheory.Chebyshev, TCSlib.Cryptography.NumberTheory.Primality, TCSlib.Cryptography.NumberTheory.Units, TCSlib.Cryptography.OneWayFunctions.Amplification, TCSlib.Cryptography.OneWayFunctions.Basic, TCSlib.InformationTheory.FinDist, TCSlib.InformationTheory.StatisticalDistance]
#s2closure TCSlib.Cryptography.Candidates.ElGamal [TCSlib.Complexity.CircuitComplexity.Advice, TCSlib.Complexity.CircuitComplexity.Basic, TCSlib.Complexity.CircuitComplexity.DAGCircuit, TCSlib.Complexity.CircuitComplexity.DAGFanin, TCSlib.Complexity.CircuitComplexity.DAGTransform, TCSlib.Complexity.CircuitComplexity.LayeredCircuit, TCSlib.Complexity.CircuitComplexity.LayeredDAG, TCSlib.Complexity.CircuitComplexity.LayeredPPoly, TCSlib.Complexity.CircuitComplexity.PPoly, TCSlib.Complexity.CircuitComplexity.SizeClasses, TCSlib.Complexity.CircuitComplexity.TreeDAG, TCSlib.Complexity.ClassNP.CoNP, TCSlib.Complexity.ClassNP.CounterProgPolyTime, TCSlib.Complexity.ClassNP.NP, TCSlib.Complexity.ClassNP.PClosure, TCSlib.Complexity.ClassNP.PolyTime, TCSlib.Complexity.ClassNP.PolyTimeBlockLoop, TCSlib.Complexity.ClassNP.PolyTimeBlockMajority, TCSlib.Complexity.ClassNP.PolyTimeBlockTests, TCSlib.Complexity.ClassNP.PolyTimePairing, TCSlib.Complexity.ClassNP.PolyTimePrefix, TCSlib.Complexity.ClassP.DTIME, TCSlib.Complexity.ClassP.P, TCSlib.Complexity.ClassP.TimeConstructible, TCSlib.Complexity.PolyHierarchy.Padding, TCSlib.Complexity.Randomized.Build.IterateFind, TCSlib.Complexity.Randomized.Build.IterateFindHost, TCSlib.Complexity.Randomized.Build.PairSplit, TCSlib.Complexity.Randomized.Build.StateLoop, TCSlib.Complexity.Randomized.Build.StringLoops, TCSlib.Complexity.Randomized.Build.UnaryMul, TCSlib.Complexity.Randomized.Closure, TCSlib.Complexity.Randomized.NonUniform, TCSlib.Complexity.Randomized.PPT, TCSlib.Complexity.Randomized.PolyExpr, TCSlib.Complexity.Randomized.Primitives, TCSlib.Complexity.Randomized.Repetition, TCSlib.Complexity.TuringMachine.Build.Convention, TCSlib.Complexity.TuringMachine.Build.Embed, TCSlib.Complexity.TuringMachine.Build.EmitIterBody, TCSlib.Complexity.TuringMachine.Build.EmitIterEmbed, TCSlib.Complexity.TuringMachine.Build.Loop, TCSlib.Complexity.TuringMachine.Build.ModuleHost, TCSlib.Complexity.TuringMachine.Build.Primitives, TCSlib.Complexity.TuringMachine.Build.Wrappers, TCSlib.Complexity.TuringMachine.Composition, TCSlib.Complexity.TuringMachine.Configuration, TCSlib.Complexity.TuringMachine.CounterProg, TCSlib.Complexity.TuringMachine.CounterProgInput, TCSlib.Complexity.TuringMachine.CounterProgRun, TCSlib.Complexity.TuringMachine.Deterministic, TCSlib.Complexity.TuringMachine.Encoding, TCSlib.Complexity.TuringMachine.Finite, TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction, TCSlib.Complexity.TuringMachine.Robustness.SingleTape, TCSlib.Complexity.TuringMachine.Simulation, TCSlib.Complexity.TuringMachine.StateRenaming, TCSlib.Complexity.TuringMachine.Sweep, TCSlib.Complexity.TuringMachine.UnaryTape, TCSlib.Cryptography.Asymptotic.Adversary, TCSlib.Cryptography.Asymptotic.Collections, TCSlib.Cryptography.Asymptotic.CollectionsHelpers, TCSlib.Cryptography.Asymptotic.CollectionsLemmas, TCSlib.Cryptography.Asymptotic.Ensembles, TCSlib.Cryptography.Asymptotic.EnsemblesLemmas, TCSlib.Cryptography.Asymptotic.OneWay, TCSlib.Cryptography.Asymptotic.OneWayLemmas, TCSlib.Cryptography.Asymptotic.OneWayYao, TCSlib.Cryptography.Asymptotic.Sampling, TCSlib.Cryptography.Candidates.Arithmetic, TCSlib.Cryptography.Candidates.Concrete, TCSlib.Cryptography.Candidates.DiscreteLog, TCSlib.Cryptography.Foundations.Experiments, TCSlib.Cryptography.Foundations.Negligible, TCSlib.Cryptography.Foundations.Probability, TCSlib.Cryptography.HardcoreBit.Basic, TCSlib.Cryptography.HardcoreBit.PairwiseIndependence, TCSlib.Cryptography.NumberTheory.Chebyshev, TCSlib.Cryptography.NumberTheory.Primality, TCSlib.Cryptography.NumberTheory.QuadraticResidues, TCSlib.Cryptography.NumberTheory.Units, TCSlib.Cryptography.OneWayFunctions.Amplification, TCSlib.Cryptography.OneWayFunctions.Basic, TCSlib.Cryptography.Pseudorandom.GeneratorFromPermutation, TCSlib.Cryptography.Pseudorandom.Generators, TCSlib.Cryptography.Pseudorandom.Indistinguishability, TCSlib.InformationTheory.FinDist, TCSlib.InformationTheory.StatisticalDistance]
#s2closure TCSlib.Cryptography.Candidates.RSA [TCSlib.Complexity.ClassNP.CoNP, TCSlib.Complexity.ClassNP.CounterProgPolyTime, TCSlib.Complexity.ClassNP.NP, TCSlib.Complexity.ClassNP.PClosure, TCSlib.Complexity.ClassNP.PolyTime, TCSlib.Complexity.ClassNP.PolyTimeBlockLoop, TCSlib.Complexity.ClassNP.PolyTimeBlockMajority, TCSlib.Complexity.ClassNP.PolyTimeBlockTests, TCSlib.Complexity.ClassNP.PolyTimePairing, TCSlib.Complexity.ClassNP.PolyTimePrefix, TCSlib.Complexity.ClassP.DTIME, TCSlib.Complexity.ClassP.P, TCSlib.Complexity.ClassP.TimeConstructible, TCSlib.Complexity.PolyHierarchy.Padding, TCSlib.Complexity.Randomized.Build.IterateFind, TCSlib.Complexity.Randomized.Build.IterateFindHost, TCSlib.Complexity.Randomized.Build.PairSplit, TCSlib.Complexity.Randomized.Build.StateLoop, TCSlib.Complexity.Randomized.Build.StringLoops, TCSlib.Complexity.Randomized.Build.UnaryMul, TCSlib.Complexity.Randomized.Closure, TCSlib.Complexity.Randomized.PPT, TCSlib.Complexity.Randomized.PolyExpr, TCSlib.Complexity.Randomized.Primitives, TCSlib.Complexity.Randomized.Repetition, TCSlib.Complexity.TuringMachine.Build.Convention, TCSlib.Complexity.TuringMachine.Build.Embed, TCSlib.Complexity.TuringMachine.Build.EmitIterBody, TCSlib.Complexity.TuringMachine.Build.EmitIterEmbed, TCSlib.Complexity.TuringMachine.Build.Loop, TCSlib.Complexity.TuringMachine.Build.ModuleHost, TCSlib.Complexity.TuringMachine.Build.Primitives, TCSlib.Complexity.TuringMachine.Build.Wrappers, TCSlib.Complexity.TuringMachine.Composition, TCSlib.Complexity.TuringMachine.Configuration, TCSlib.Complexity.TuringMachine.CounterProg, TCSlib.Complexity.TuringMachine.CounterProgInput, TCSlib.Complexity.TuringMachine.CounterProgRun, TCSlib.Complexity.TuringMachine.Deterministic, TCSlib.Complexity.TuringMachine.Encoding, TCSlib.Complexity.TuringMachine.Finite, TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction, TCSlib.Complexity.TuringMachine.Robustness.SingleTape, TCSlib.Complexity.TuringMachine.Simulation, TCSlib.Complexity.TuringMachine.StateRenaming, TCSlib.Complexity.TuringMachine.Sweep, TCSlib.Complexity.TuringMachine.UnaryTape, TCSlib.Cryptography.Asymptotic.Adversary, TCSlib.Cryptography.Asymptotic.Collections, TCSlib.Cryptography.Asymptotic.CollectionsHelpers, TCSlib.Cryptography.Asymptotic.CollectionsLemmas, TCSlib.Cryptography.Asymptotic.OneWay, TCSlib.Cryptography.Asymptotic.OneWayLemmas, TCSlib.Cryptography.Asymptotic.OneWayYao, TCSlib.Cryptography.Asymptotic.Sampling, TCSlib.Cryptography.Candidates.Arithmetic, TCSlib.Cryptography.Candidates.Concrete, TCSlib.Cryptography.Candidates.Factoring, TCSlib.Cryptography.Foundations.Experiments, TCSlib.Cryptography.Foundations.Negligible, TCSlib.Cryptography.Foundations.Probability, TCSlib.Cryptography.HardcoreBit.Basic, TCSlib.Cryptography.NumberTheory.Chebyshev, TCSlib.Cryptography.NumberTheory.Primality, TCSlib.Cryptography.NumberTheory.Units, TCSlib.Cryptography.OneWayFunctions.Amplification, TCSlib.Cryptography.OneWayFunctions.Basic, TCSlib.InformationTheory.FinDist, TCSlib.InformationTheory.StatisticalDistance]
#s2closure TCSlib.Cryptography.Candidates.Rabin [TCSlib.Complexity.ClassNP.CoNP, TCSlib.Complexity.ClassNP.CounterProgPolyTime, TCSlib.Complexity.ClassNP.NP, TCSlib.Complexity.ClassNP.PClosure, TCSlib.Complexity.ClassNP.PolyTime, TCSlib.Complexity.ClassNP.PolyTimeBlockLoop, TCSlib.Complexity.ClassNP.PolyTimeBlockMajority, TCSlib.Complexity.ClassNP.PolyTimeBlockTests, TCSlib.Complexity.ClassNP.PolyTimePairing, TCSlib.Complexity.ClassNP.PolyTimePrefix, TCSlib.Complexity.ClassP.DTIME, TCSlib.Complexity.ClassP.P, TCSlib.Complexity.ClassP.TimeConstructible, TCSlib.Complexity.PolyHierarchy.Padding, TCSlib.Complexity.Randomized.Build.IterateFind, TCSlib.Complexity.Randomized.Build.IterateFindHost, TCSlib.Complexity.Randomized.Build.PairSplit, TCSlib.Complexity.Randomized.Build.StateLoop, TCSlib.Complexity.Randomized.Build.StringLoops, TCSlib.Complexity.Randomized.Build.UnaryMul, TCSlib.Complexity.Randomized.Closure, TCSlib.Complexity.Randomized.PPT, TCSlib.Complexity.Randomized.PolyExpr, TCSlib.Complexity.Randomized.Primitives, TCSlib.Complexity.Randomized.Repetition, TCSlib.Complexity.TuringMachine.Build.Convention, TCSlib.Complexity.TuringMachine.Build.Embed, TCSlib.Complexity.TuringMachine.Build.EmitIterBody, TCSlib.Complexity.TuringMachine.Build.EmitIterEmbed, TCSlib.Complexity.TuringMachine.Build.Loop, TCSlib.Complexity.TuringMachine.Build.ModuleHost, TCSlib.Complexity.TuringMachine.Build.Primitives, TCSlib.Complexity.TuringMachine.Build.Wrappers, TCSlib.Complexity.TuringMachine.Composition, TCSlib.Complexity.TuringMachine.Configuration, TCSlib.Complexity.TuringMachine.CounterProg, TCSlib.Complexity.TuringMachine.CounterProgInput, TCSlib.Complexity.TuringMachine.CounterProgRun, TCSlib.Complexity.TuringMachine.Deterministic, TCSlib.Complexity.TuringMachine.Encoding, TCSlib.Complexity.TuringMachine.Finite, TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction, TCSlib.Complexity.TuringMachine.Robustness.SingleTape, TCSlib.Complexity.TuringMachine.Simulation, TCSlib.Complexity.TuringMachine.StateRenaming, TCSlib.Complexity.TuringMachine.Sweep, TCSlib.Complexity.TuringMachine.UnaryTape, TCSlib.Cryptography.Asymptotic.Adversary, TCSlib.Cryptography.Asymptotic.Collections, TCSlib.Cryptography.Asymptotic.CollectionsHelpers, TCSlib.Cryptography.Asymptotic.CollectionsLemmas, TCSlib.Cryptography.Asymptotic.OneWay, TCSlib.Cryptography.Asymptotic.OneWayLemmas, TCSlib.Cryptography.Asymptotic.OneWayYao, TCSlib.Cryptography.Asymptotic.Sampling, TCSlib.Cryptography.Candidates.Arithmetic, TCSlib.Cryptography.Candidates.Concrete, TCSlib.Cryptography.Candidates.Factoring, TCSlib.Cryptography.Candidates.RSA, TCSlib.Cryptography.Foundations.Experiments, TCSlib.Cryptography.Foundations.Negligible, TCSlib.Cryptography.Foundations.Probability, TCSlib.Cryptography.HardcoreBit.Basic, TCSlib.Cryptography.NumberTheory.Chebyshev, TCSlib.Cryptography.NumberTheory.Primality, TCSlib.Cryptography.NumberTheory.QuadraticResidues, TCSlib.Cryptography.NumberTheory.Units, TCSlib.Cryptography.OneWayFunctions.Amplification, TCSlib.Cryptography.OneWayFunctions.Basic, TCSlib.InformationTheory.FinDist, TCSlib.InformationTheory.StatisticalDistance]
#s2collect TCSlib.Cryptography.Candidates.Concrete ["polyTimeComputable_rejectBlocksL", "rbl_step", "rbl_block", "rbl_acc", "rbl_out", "rbl_loop", "rbl_step_poly", "rbl_block_poly", "rbl_acc_poly", "rbl_out_poly", "rbl_step_iterate", "rbl_length_step_le", "rbl_length_step_step_le", "rbl_length_step_iterate_le", "rbl_loop_poly", "rbl_loop_spec"]
#s2collect TCSlib.Cryptography.Candidates.Concrete ["*"]
#s2axs TCSlib.Cryptography.Candidates.Concrete ["polyTimeComputable_rejectBlocksL", "rbl_step", "rbl_block", "rbl_acc", "rbl_out", "rbl_loop", "rbl_step_poly", "rbl_block_poly", "rbl_acc_poly", "rbl_out_poly", "rbl_step_iterate", "rbl_length_step_le", "rbl_length_step_step_le", "rbl_length_step_iterate_le", "rbl_loop_poly", "rbl_loop_spec"]
#s2collect TCSlib.Cryptography.Candidates.DiscreteLog ["polyTimeComputable_expSampleRaw", "dla_belowAcc", "dla_belowAcc_poly", "dla_belowAcc_spec"]
#s2collect TCSlib.Cryptography.Candidates.DiscreteLog ["*"]
#s2axs TCSlib.Cryptography.Candidates.DiscreteLog ["polyTimeComputable_expSampleRaw", "dla_belowAcc", "dla_belowAcc_poly", "dla_belowAcc_spec"]
#s2collect TCSlib.Cryptography.Candidates.ElGamal ["dlc_numPoly_sample", "dlc_belowAcc", "dlc_belowAcc_spec", "polyTimeComputable_egGenRaw", "polyTimeComputable_egEncRaw"]
#s2collect TCSlib.Cryptography.Candidates.ElGamal ["*"]
#s2axs TCSlib.Cryptography.Candidates.ElGamal ["dlc_numPoly_sample", "dlc_belowAcc", "dlc_belowAcc_spec", "polyTimeComputable_egGenRaw", "polyTimeComputable_egEncRaw"]
#s2collect TCSlib.Cryptography.Candidates.RSA ["rsa_ptc_unitSampleStr", "rsa_unitAcc", "rsa_unitAcc_poly", "rsa_unitAcc_spec", "polyTimeComputable_unitSampleStr"]
#s2collect TCSlib.Cryptography.Candidates.RSA ["*"]
#s2axs TCSlib.Cryptography.Candidates.RSA ["rsa_ptc_unitSampleStr", "rsa_unitAcc", "rsa_unitAcc_poly", "rsa_unitAcc_spec", "polyTimeComputable_unitSampleStr"]
#s2collect TCSlib.Cryptography.Candidates.Rabin ["rabin_spOut", "rabin_spOut_eq", "rabin_spOut_poly", "rabin_genCore_poly", "rabin_genCore_eq", "polyTimeComputable_oddGenRaw", "polyTimeComputable_blumGenRaw"]
#s2collect TCSlib.Cryptography.Candidates.Rabin ["*"]
#s2axs TCSlib.Cryptography.Candidates.Rabin ["rabin_spOut", "rabin_spOut_eq", "rabin_spOut_poly", "rabin_genCore_poly", "rabin_genCore_eq", "polyTimeComputable_oddGenRaw", "polyTimeComputable_blumGenRaw"]

namespace TCSlib.Cryptography.Candidates
open Complexity Turing Finset TCSlib.Cryptography.OneWay NumberTheory
#s2kind TCSlib.Cryptography.Candidates.Concrete ["Function.comp_apply", "Function.iterate_succ_apply'", "Function.iterate_zero_apply", "List.drop_drop", "List.drop_eq_nil_iff", "List.drop_zero", "List.length_drop", "List.length_nil", "List.singleton_append", "List.tail_cons", "List.tail_nil", "Nat.succ_mul", "Nat.zero_mul", "Option.elim_none", "Option.elim_some", "Option.map_none", "Option.map_some", "PolyExpr.eval_add", "PolyExpr.eval_const", "PolyExpr.eval_mul", "PolyExpr.eval_var", "decide_eq_false", "decide_eq_true", "h", "hblock", "hfind", "hspec", "hx0", "if_neg", "if_pos", "ih", "length_pairEncode", "pairFstD_pairEncode", "pairSndD_pairEncode", "rbl_acc", "rbl_block", "rbl_loop", "rbl_out", "rbl_step", "rbl_step_iterate", "rejectBlocksL_eq_find?", "show"]
end TCSlib.Cryptography.Candidates

namespace TCSlib.Cryptography.Candidates
open Complexity Turing NumberTheory Finset
#s2kind TCSlib.Cryptography.Candidates.DiscreteLog ["Function.comp_apply", "List.tail_nil", "Nat.not_le", "Nat.sub_self", "PolyExpr.eval_var", "decide_eq_decide", "decide_not", "dlM_eq", "dlW", "dla_belowAcc", "expSampleRaw", "he", "length_sizeStr", "listToNat_nil", "natToList_zero_append_drop", "pairFstD_pairEncode", "pairSndD_pairEncode", "sampleBelowL_eq_rejectBlocksL", "show", "subStr_pairEncode"]
end TCSlib.Cryptography.Candidates

namespace TCSlib.Cryptography.Candidates
open Complexity Turing NumberTheory Finset
#s2kind TCSlib.Cryptography.Candidates.ElGamal ["Function.comp_apply", "List.tail_nil", "Nat.not_le", "PolyExpr.eval_add", "PolyExpr.eval_mul", "PolyExpr.eval_var", "decide_eq_decide", "decide_not", "dlc_belowAcc", "he", "hmM", "length_sizeStr", "listToNat_nil", "pairFstD_pairEncode", "pairSndD_pairEncode", "sampleBelowL_eq_rejectBlocksL", "show"]
end TCSlib.Cryptography.Candidates

namespace TCSlib.Cryptography.Candidates
open Complexity Turing NumberTheory Finset
#s2kind TCSlib.Cryptography.Candidates.RSA ["List.length_replicate", "Nat.mod_eq_of_lt", "Option.getD_none", "Option.getD_some", "decide_eq_true_eq", "divModStr_pairEncode", "hsz", "if_neg", "if_pos", "length_sizeStr", "listToNat_singleton_true", "pairFstD_pairEncode", "pairSndD_pairEncode", "rsa_unitAcc", "rsa_unitTest_eq", "sampleUnitL_eq", "unitSampleStr_eq", "xgcdStr_pairEncode"]
end TCSlib.Cryptography.Candidates

namespace TCSlib.Cryptography.Candidates
open Complexity Turing NumberTheory Finset
#s2kind TCSlib.Cryptography.Candidates.Rabin ["Bool.false_eq_true", "Bool.not_false", "Bool.not_true", "DistinctPrimes.p_eq", "DistinctPrimes.q_eq", "List.length_replicate", "Option.getD_none", "Option.getD_some", "decide_eq_true_eq", "decide_false", "decide_true", "e", "encodeDistinctPrimes_eq", "h", "h1", "h2", "hP", "hQ", "hRp", "hRq", "hUl", "hne", "hpE", "hqE", "hr", "hs", "hsp", "hspec", "hsq", "if_false", "if_neg", "if_pos", "if_true", "mulStr_natToList", "ne_eq", "not_false_eq_true", "not_true_eq_false", "pairFstD_pairEncode", "pairSndD_pairEncode", "rabinGenOut", "rabinGenParams", "rabinGenRaw", "rabinIndexOf", "rabin_gA", "rabin_gB", "rabin_gC1", "rabin_gC2", "rabin_gP", "rabin_gQ", "rabin_gU_eq", "rabin_gValid", "rabin_genCore", "rabin_listToNat_five", "rabin_listToNat_seven", "rabin_listToNat_three", "rabin_pad_eq", "rabin_spOut", "rabin_spOut_eq", "rejectBlocksL_eq_find?", "samplePrimePL", "two_mul"]
end TCSlib.Cryptography.Candidates
