import Lean
import TCSlib.Cryptography.Games.Probability
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option maxHeartbeats 0

set_option maxHeartbeats 0
run_cmd do
  let label : String := "FinalR2Averaging_ControlANegative"
  let payload : String := "TCSlib.Cryptography.Games.OracleComp.AllOutputs\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp.AllOutputs._sunfold\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp.AllOutputs._unsafe_rec\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp.CostBoundedBy\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp.CostBoundedBy._sunfold\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp.CostBoundedBy._unsafe_rec\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp.CostBoundedBy.match_1\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp._sizeOf_1\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp.bind\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp.bind._sunfold\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp.bind._unsafe_rec\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp.bind.match_1\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp.call\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp.liftLeft\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp.liftLeft._sunfold\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp.liftLeft._unsafe_rec\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp.liftLeft.match_1\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp.liftRight\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp.liftRight._sunfold\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp.liftRight._unsafe_rec\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleSpec._sizeOf_1\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleSpec.mk._flat_ctor\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.ProbComp.dist\tTCSlib.Cryptography.Games.Probability\nTCSlib.Cryptography.Games.ProbComp.expect\tTCSlib.Cryptography.Games.Probability\nTCSlib.Cryptography.Games.ProbComp.expect._sunfold\tTCSlib.Cryptography.Games.Probability\nTCSlib.Cryptography.Games.ProbComp.expect.match_1\tTCSlib.Cryptography.Games.Probability\nTCSlib.Cryptography.Games.ProbComp.prob\tTCSlib.Cryptography.Games.Probability\nTCSlib.Cryptography.Games.ProbComp.sample\tTCSlib.Cryptography.Games.Probability\nTCSlib.Cryptography.Games.ProbComp.sampleFin\tTCSlib.Cryptography.Games.Probability\nTCSlib.InformationTheory.FinDist.HasMinEntropy\tTCSlib.InformationTheory.FinDist\nTCSlib.InformationTheory.FinDist._sizeOf_1\tTCSlib.InformationTheory.FinDist\nTCSlib.InformationTheory.FinDist.collision\tTCSlib.InformationTheory.FinDist\nTCSlib.InformationTheory.FinDist.map\tTCSlib.InformationTheory.FinDist\nTCSlib.InformationTheory.FinDist.mk._flat_ctor\tTCSlib.InformationTheory.FinDist\nTCSlib.InformationTheory.FinDist.probTrue\tTCSlib.InformationTheory.FinDist\nTCSlib.InformationTheory.FinDist.prod\tTCSlib.InformationTheory.FinDist\nTCSlib.InformationTheory.FinDist.uniform\tTCSlib.InformationTheory.FinDist\n_private.TCSlib.Cryptography.Games.OracleComp.0.TCSlib.Cryptography.Games.OracleComp.liftLeft.match_1.splitter\tTCSlib.Cryptography.Games.OracleComp"
  let lines := if payload.isEmpty then [] else payload.splitOn "\n"
  unless lines.length == 38 do throwError "LAMP-HARNESS bad serialized count"
  let env ← Lean.getEnv
  let mut catalog : Std.HashMap String (Array Lean.Name) := {}
  for (n, _) in env.constants.map₁.toList do
    let some mi := env.getModuleIdxFor? n | continue
    unless (`TCSlib).isPrefixOf env.header.moduleNames[mi.toNat]! do continue
    catalog := catalog.insert n.toString (((catalog[n.toString]?).getD #[]).push n)
  let mut count : Nat := 0
  for row in lines do
    let [spelling, home] := row.splitOn "\t" | throwError "LAMP-HARNESS malformed row"
    let ns := (catalog[spelling]?).getD #[]
    unless ns.size == 1 do throwError "LAMP-HARNESS absent/ambiguous {spelling}"
    let n := ns[0]!
    let some mi := env.getModuleIdxFor? n | throwError "LAMP-HARNESS no home {spelling}"
    unless env.header.moduleNames[mi.toNat]!.toString == home do
      throwError "LAMP-HARNESS wrong home {spelling}"
    let some ci := env.find? n | throwError "LAMP-HARNESS no constant {spelling}"
    unless ci.isDefinition do throwError "LAMP-HARNESS not definition {spelling}"
    let before ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
    unless before == .irreducible do
      let id := Lean.mkIdent n
      Lean.Elab.Command.elabCommand (← `(command| attribute [local irreducible] $id:ident))
    let after ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
    unless after == .irreducible do throwError "LAMP-HARNESS unsealed {spelling}"
    Lean.logInfo m!"LAMP-SEAL-NAME\t{label}\tINSTALL\t{spelling}\t{home}"
    count := count + 1
  unless count == 38 do throwError "LAMP-HARNESS wrong verified count"
  Lean.logInfo m!"LAMP-SEAL-INSTALL\t{label}\t{count}"

example (x : ℝ) : TCSlib.Cryptography.Games.ProbComp.expect (.pure x) (fun y => y) = x := by
  rfl

set_option maxHeartbeats 0
run_cmd do
  let label : String := "FinalR2Averaging_ControlANegative"
  let payload : String := "TCSlib.Cryptography.Games.OracleComp.AllOutputs\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp.AllOutputs._sunfold\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp.AllOutputs._unsafe_rec\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp.CostBoundedBy\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp.CostBoundedBy._sunfold\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp.CostBoundedBy._unsafe_rec\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp.CostBoundedBy.match_1\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp._sizeOf_1\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp.bind\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp.bind._sunfold\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp.bind._unsafe_rec\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp.bind.match_1\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp.call\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp.liftLeft\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp.liftLeft._sunfold\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp.liftLeft._unsafe_rec\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp.liftLeft.match_1\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp.liftRight\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp.liftRight._sunfold\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp.liftRight._unsafe_rec\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleSpec._sizeOf_1\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleSpec.mk._flat_ctor\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.ProbComp.dist\tTCSlib.Cryptography.Games.Probability\nTCSlib.Cryptography.Games.ProbComp.expect\tTCSlib.Cryptography.Games.Probability\nTCSlib.Cryptography.Games.ProbComp.expect._sunfold\tTCSlib.Cryptography.Games.Probability\nTCSlib.Cryptography.Games.ProbComp.expect.match_1\tTCSlib.Cryptography.Games.Probability\nTCSlib.Cryptography.Games.ProbComp.prob\tTCSlib.Cryptography.Games.Probability\nTCSlib.Cryptography.Games.ProbComp.sample\tTCSlib.Cryptography.Games.Probability\nTCSlib.Cryptography.Games.ProbComp.sampleFin\tTCSlib.Cryptography.Games.Probability\nTCSlib.InformationTheory.FinDist.HasMinEntropy\tTCSlib.InformationTheory.FinDist\nTCSlib.InformationTheory.FinDist._sizeOf_1\tTCSlib.InformationTheory.FinDist\nTCSlib.InformationTheory.FinDist.collision\tTCSlib.InformationTheory.FinDist\nTCSlib.InformationTheory.FinDist.map\tTCSlib.InformationTheory.FinDist\nTCSlib.InformationTheory.FinDist.mk._flat_ctor\tTCSlib.InformationTheory.FinDist\nTCSlib.InformationTheory.FinDist.probTrue\tTCSlib.InformationTheory.FinDist\nTCSlib.InformationTheory.FinDist.prod\tTCSlib.InformationTheory.FinDist\nTCSlib.InformationTheory.FinDist.uniform\tTCSlib.InformationTheory.FinDist\n_private.TCSlib.Cryptography.Games.OracleComp.0.TCSlib.Cryptography.Games.OracleComp.liftLeft.match_1.splitter\tTCSlib.Cryptography.Games.OracleComp"
  let lines := if payload.isEmpty then [] else payload.splitOn "\n"
  unless lines.length == 38 do throwError "LAMP-HARNESS bad serialized count"
  let env ← Lean.getEnv
  let mut catalog : Std.HashMap String (Array Lean.Name) := {}
  for (n, _) in env.constants.map₁.toList do
    let some mi := env.getModuleIdxFor? n | continue
    unless (`TCSlib).isPrefixOf env.header.moduleNames[mi.toNat]! do continue
    catalog := catalog.insert n.toString (((catalog[n.toString]?).getD #[]).push n)
  let mut count : Nat := 0
  for row in lines do
    let [spelling, home] := row.splitOn "\t" | throwError "LAMP-HARNESS malformed row"
    let ns := (catalog[spelling]?).getD #[]
    unless ns.size == 1 do throwError "LAMP-HARNESS absent/ambiguous {spelling}"
    let n := ns[0]!
    let some mi := env.getModuleIdxFor? n | throwError "LAMP-HARNESS no home {spelling}"
    unless env.header.moduleNames[mi.toNat]!.toString == home do
      throwError "LAMP-HARNESS wrong home {spelling}"
    let some ci := env.find? n | throwError "LAMP-HARNESS no constant {spelling}"
    unless ci.isDefinition do throwError "LAMP-HARNESS not definition {spelling}"
    let after ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
    unless after == .irreducible do throwError "LAMP-HARNESS unsealed {spelling}"
    Lean.logInfo m!"LAMP-SEAL-NAME\t{label}\tEOF\t{spelling}\t{home}"
    count := count + 1
  unless count == 38 do throwError "LAMP-HARNESS wrong verified count"
  Lean.logInfo m!"LAMP-SEAL-EOF\t{label}\t{count}"

