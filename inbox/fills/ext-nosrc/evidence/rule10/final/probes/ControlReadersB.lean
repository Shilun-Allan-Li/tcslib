import Lean
import TCSlib.Cryptography.Asymptotic.Adversary

set_option maxHeartbeats 0
run_cmd do
  let label : String := "ControlReadersB"
  let phase : String := "install"
  let payload : String := "TCSlib.Cryptography.padFin\tTCSlib.Cryptography.Asymptotic.Adversary\nComplexity.NUPPT.runAtL\tTCSlib.Complexity.Randomized.PPT\nComplexity.PolyExpr.eval\tTCSlib.Complexity.Randomized.PolyExpr"
  let expected : Nat := 3
  let env ← Lean.getEnv
  let mut catalog : Std.HashMap String (Array Lean.Name) := {}
  for (n, _) in env.constants.map₁.toList do
    let group := (catalog[n.toString]?).getD #[]
    catalog := catalog.insert n.toString (group.push n)
  let lines := if payload.isEmpty then [] else payload.splitOn "\n"
  let mut verified : Nat := 0
  for line in lines do
    let [spelling, expectedHome] := line.splitOn "\t" |
      throwError "FILL-HARNESS {label}: malformed request"
    let names := (catalog[spelling]?).getD #[]
    unless names.size == 1 do throwError "FILL-HARNESS {label}: absent/ambiguous name {spelling}"
    let n := names[0]!
    let some mi := env.getModuleIdxFor? n | throwError "FILL-HARNESS {label}: missing home {spelling}"
    let home := env.header.moduleNames[mi.toNat]!
    unless home.toString == expectedHome do throwError "FILL-HARNESS {label}: home mismatch {spelling}"
    let some ci := env.find? n | throwError "FILL-HARNESS {label}: missing constant {spelling}"
    unless ci.isDefinition do throwError "FILL-HARNESS {label}: nondefinition {spelling}"
    let before ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
    unless before == .irreducible do
      let id := Lean.mkIdent n
      Lean.Elab.Command.elabCommand (← `(command| attribute [local irreducible] $id:ident))
    let installed ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
    unless installed == .irreducible do throwError "FILL-HARNESS {label}: seal inactive at {phase} for {spelling}"
    let row := Lean.Json.mkObj [
      ("label", Lean.toJson label), ("phase", Lean.toJson phase),
      ("name", Lean.toJson n.toString), ("home", Lean.toJson home.toString)]
    Lean.logInfo m!"FILL_SEAL_NAME {row.compress}"
    verified := verified + 1
  unless verified == expected do throwError "FILL-HARNESS {label}: count mismatch {verified} vs {expected}"
  Lean.logInfo m!"FILL_SEAL_DONE {label} {phase} {expected} {verified}"

open Complexity Turing TCSlib.Cryptography
example (w : List Bool) : padFin 1 w 0 = w.getD 0 false := by exact padFin_apply 1 w 0
example (A : NUPPT) (n : Nat) (y r : List Bool) :
    A.runAtL n y r = A.output (pairEncode (pairEncode (NUPPT.advInput n y) (A.advice n)) r) :=
  by exact NUPPT.runAtL_eq A n y r
example (n : Nat) : PolyExpr.eval .var n = n := by exact PolyExpr.eval_var n

set_option maxHeartbeats 0
run_cmd do
  let label : String := "ControlReadersB"
  let phase : String := "eof"
  let payload : String := "TCSlib.Cryptography.padFin\tTCSlib.Cryptography.Asymptotic.Adversary\nComplexity.NUPPT.runAtL\tTCSlib.Complexity.Randomized.PPT\nComplexity.PolyExpr.eval\tTCSlib.Complexity.Randomized.PolyExpr"
  let expected : Nat := 3
  let env ← Lean.getEnv
  let mut catalog : Std.HashMap String (Array Lean.Name) := {}
  for (n, _) in env.constants.map₁.toList do
    let group := (catalog[n.toString]?).getD #[]
    catalog := catalog.insert n.toString (group.push n)
  let lines := if payload.isEmpty then [] else payload.splitOn "\n"
  let mut verified : Nat := 0
  for line in lines do
    let [spelling, expectedHome] := line.splitOn "\t" |
      throwError "FILL-HARNESS {label}: malformed request"
    let names := (catalog[spelling]?).getD #[]
    unless names.size == 1 do throwError "FILL-HARNESS {label}: absent/ambiguous name {spelling}"
    let n := names[0]!
    let some mi := env.getModuleIdxFor? n | throwError "FILL-HARNESS {label}: missing home {spelling}"
    let home := env.header.moduleNames[mi.toNat]!
    unless home.toString == expectedHome do throwError "FILL-HARNESS {label}: home mismatch {spelling}"
    let some ci := env.find? n | throwError "FILL-HARNESS {label}: missing constant {spelling}"
    unless ci.isDefinition do throwError "FILL-HARNESS {label}: nondefinition {spelling}"
    let installed ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
    unless installed == .irreducible do throwError "FILL-HARNESS {label}: seal inactive at {phase} for {spelling}"
    let row := Lean.Json.mkObj [
      ("label", Lean.toJson label), ("phase", Lean.toJson phase),
      ("name", Lean.toJson n.toString), ("home", Lean.toJson home.toString)]
    Lean.logInfo m!"FILL_SEAL_NAME {row.compress}"
    verified := verified + 1
  unless verified == expected do throwError "FILL-HARNESS {label}: count mismatch {verified} vs {expected}"
  Lean.logInfo m!"FILL_SEAL_DONE {label} {phase} {expected} {verified}"
