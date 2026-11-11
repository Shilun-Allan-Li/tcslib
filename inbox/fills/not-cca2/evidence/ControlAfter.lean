import Lean
import TCSlib.Cryptography.Encryption.PrivateKey.OracleSecurity
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF
import Mathlib.Tactic.Simps.Basic

run_cmd do
  let names : Array String := #[
    "Complexity.NUPPT.advInput",
    "Complexity.NUPPT.coinLen",
    "Complexity.NUPPT.coinsEquiv_ofPolyTimeUniform",
    "Complexity.NUPPT.inArg",
    "Complexity.NUPPT.inParam",
    "Complexity.NUPPT.ofPolyTimeUniform",
    "Complexity.NUPPT.runAt",
    "Complexity.NUPPT.runAtL",
    "Complexity.PolyTimeComputable",
    "Complexity.pairFstD",
    "Complexity.pairSndD",
    "TCSlib.Cryptography.Composability.FixedLengthScheme.INDSecure",
    "TCSlib.Cryptography.Composability.FixedLengthScheme.encryptAt",
    "TCSlib.Cryptography.Composability.FixedLengthScheme.inLens",
    "TCSlib.Cryptography.Composability.FixedLengthScheme.indGame",
    "TCSlib.Cryptography.Composability.FixedLengthScheme.outLens",
    "TCSlib.Cryptography.Composability.FixedLengthScheme.splitHalf",
    "TCSlib.Cryptography.Games.advantage",
    "TCSlib.Cryptography.Negligible",
    "TCSlib.Cryptography.padFin",
    "TCSlib.Cryptography.prfEncFun",
    "TCSlib.Cryptography.prfScheme",
    "Turing.pairEncode"]
  for index in [:names.size] do
    let spelling := names[index]!
    let name := spelling.toName
    let some ci := (← Lean.getEnv).find? name | throwError "Missing seal candidate {name}"
    unless ci.isDefinition do throwError "Nondefinition seal candidate {name}"
    if Lean.Meta.isInstanceCore (← Lean.getEnv) name then
      Lean.Elab.Command.elabCommand (← `(command| attribute [-instance] $(Lean.mkIdent name):ident))
      let aliasName := ("notCca2SealInstance" ++ toString index).toName
      Lean.Elab.Command.liftCoreM <| Lean.addDecl (.defnDecl {
        name := aliasName, levelParams := ci.levelParams, type := ci.type,
        value := Lean.mkConst name (ci.levelParams.map Lean.Level.param),
        hints := .abbrev, safety := .safe })
      Lean.Elab.Command.elabCommand (← `(command| attribute [local instance] $(Lean.mkIdent aliasName):ident))
      unless !(Lean.Meta.isInstanceCore (← Lean.getEnv) name) do
        throwError "Original instance remains registered: {name}"
      Lean.logInfo m!"INSTANCE_ALIAS|{name}|{aliasName}"
    Lean.Elab.Command.elabCommand (← `(command| attribute [local irreducible] $(Lean.mkIdent name):ident))
    let status ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus name
    unless status == .irreducible do throwError "Seal not installed for {name}"
    Lean.logInfo m!"SEALED|{name}|{repr status}"

example (z : List Bool) : Complexity.NUPPT.inArg z =
    Complexity.pairSndD (Complexity.pairFstD (Complexity.pairFstD z)) := by
  rfl
