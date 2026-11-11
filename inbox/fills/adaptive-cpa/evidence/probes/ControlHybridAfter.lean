import Lean
import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity.ChallengeSim

run_cmd do
  let names : Array String := #[
    "Complexity.NUPPT.toCompOn",
    "TCSlib.Cryptography.Games.OracleComp.bind",
    "TCSlib.Cryptography.Games.ProbComp.expect",
    "TCSlib.Cryptography.Games.ProbComp.sample",
    "TCSlib.Cryptography.Games.bitCodec",
    "TCSlib.Cryptography.Games.simulate",
    "TCSlib.Cryptography.Games.zeroBits",
    "TCSlib.Cryptography.padFin"]
  for index in [:names.size] do
    let name := names[index]!.toName
    let some ci := (← Lean.getEnv).find? name | throwError "Missing seal candidate {name}"
    unless ci.isDefinition do throwError "Nondefinition seal candidate {name}"
    if Lean.Meta.isInstanceCore (← Lean.getEnv) name then
      Lean.Elab.Command.elabCommand (← `(command| attribute [-instance] $(Lean.mkIdent name):ident))
      let aliasName := ("HybridSealInstance" ++ toString index).toName
      Lean.Elab.Command.liftCoreM <| Lean.addDecl (.defnDecl {
        name := aliasName, levelParams := ci.levelParams, type := ci.type,
        value := Lean.mkConst name (ci.levelParams.map Lean.Level.param),
        hints := .abbrev, safety := .safe })
      Lean.Elab.Command.elabCommand (← `(command| attribute [local instance] $(Lean.mkIdent aliasName):ident))
      Lean.logInfo m!"INSTANCE_ALIAS|{name}|{aliasName}"
    Lean.Elab.Command.elabCommand (← `(command| attribute [local irreducible] $(Lean.mkIdent name):ident))
    let status ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus name
    unless status == .irreducible do throwError "Seal not installed for {name}"
    Lean.logInfo m!"SEALED|{name}|{repr status}"

example (ℓ : ℕ) (w : List Bool) (i : Fin ℓ) :
    TCSlib.Cryptography.padFin ℓ w i = w.getD i false := by
  rfl
