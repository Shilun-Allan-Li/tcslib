import Lean
import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveSecurity
import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Hybrid
import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Handler

run_cmd do
  let names : Array String := #[
    "Complexity.NUPPT.coinLen",
    "Complexity.NUPPT.runAt",
    "Complexity.NUPPT.toCompOn",
    "Complexity.pairFstD",
    "Complexity.pairSndD",
    "TCSlib.Cryptography.Composability.AdaptiveCPA.acDin",
    "TCSlib.Cryptography.Composability.AdaptiveCPA.acDout",
    "TCSlib.Cryptography.Composability.AdaptiveCPA.castImpl",
    "TCSlib.Cryptography.Composability.AdaptiveCPA.hybImpl",
    "TCSlib.Cryptography.Composability.AdaptiveCPA.msgOf",
    "TCSlib.Cryptography.Composability.FixedLengthPKScheme.adaptiveIndGame",
    "TCSlib.Cryptography.Composability.FixedLengthPKScheme.adaptiveIndImpl",
    "TCSlib.Cryptography.Composability.FixedLengthPKScheme.inLens",
    "TCSlib.Cryptography.Composability.FixedLengthPKScheme.indCodec",
    "TCSlib.Cryptography.Composability.FixedLengthPKScheme.indImpl",
    "TCSlib.Cryptography.Composability.FixedLengthPKScheme.outLens",
    "TCSlib.Cryptography.Composability.FixedLengthScheme.decAnswer",
    "TCSlib.Cryptography.Composability.FixedLengthScheme.decOpen",
    "TCSlib.Cryptography.Composability.FixedLengthScheme.splitHalf",
    "TCSlib.Cryptography.Games.OracleComp.bind",
    "TCSlib.Cryptography.Games.ProbComp.sample",
    "TCSlib.Cryptography.Games.bitCodec",
    "TCSlib.Cryptography.Games.decodeBitMove",
    "TCSlib.Cryptography.Games.simulate",
    "TCSlib.Cryptography.Games.zeroBits",
    "TCSlib.Cryptography.decodeFin",
    "TCSlib.Cryptography.padFin",
    "Turing.pairEncode"]
  for index in [:names.size] do
    let name := names[index]!.toName
    let some ci := (← Lean.getEnv).find? name | throwError "Missing seal candidate {name}"
    unless ci.isDefinition do throwError "Nondefinition seal candidate {name}"
    if Lean.Meta.isInstanceCore (← Lean.getEnv) name then
      Lean.Elab.Command.elabCommand (← `(command| attribute [-instance] $(Lean.mkIdent name):ident))
      let aliasName := ("GamesSealInstance" ++ toString index).toName
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

example (S : TCSlib.Cryptography.Composability.FixedLengthPKScheme) (n : ℕ) :
    S.inLens n 0 = S.ctLen.eval n := by
  rfl
