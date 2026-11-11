import Lean
import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveSecurity
import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Hybrid
import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Handler
import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Games
import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Reduction
import TCSlib.Cryptography.Games.Advantage
import TCSlib.Cryptography.Games.Efficiency
import TCSlib.Cryptography.Asymptotic.ReductionSupport

run_cmd do
  let names : Array String := #[
    "Complexity.NUPPT.toCompOn",
    "TCSlib.Cryptography.Composability.AdaptiveCPA.acDin",
    "TCSlib.Cryptography.Composability.AdaptiveCPA.acDout",
    "TCSlib.Cryptography.Composability.AdaptiveCPA.acHandler",
    "TCSlib.Cryptography.Composability.AdaptiveCPA.acHyb",
    "TCSlib.Cryptography.Composability.FixedLengthPKScheme.AdaptiveINDSecure",
    "TCSlib.Cryptography.Composability.FixedLengthPKScheme.INDSecure",
    "TCSlib.Cryptography.Composability.FixedLengthPKScheme.adaptiveIndGame",
    "TCSlib.Cryptography.Composability.FixedLengthPKScheme.indGame",
    "TCSlib.Cryptography.Games.InteractiveHandler.advInput",
    "TCSlib.Cryptography.Games.InteractiveHandler.finish",
    "TCSlib.Cryptography.Games.InteractiveHandler.impl",
    "TCSlib.Cryptography.Games.OracleComp.bind",
    "TCSlib.Cryptography.Games.accept",
    "TCSlib.Cryptography.Games.advantage",
    "TCSlib.Cryptography.Games.bitCodec",
    "TCSlib.Cryptography.Games.simulate",
    "TCSlib.Cryptography.Negligible"]
  for index in [:names.size] do
    let name := names[index]!.toName
    let some ci := (← Lean.getEnv).find? name | throwError "Missing seal candidate {name}"
    unless ci.isDefinition do throwError "Nondefinition seal candidate {name}"
    if Lean.Meta.isInstanceCore (← Lean.getEnv) name then
      Lean.Elab.Command.elabCommand (← `(command| attribute [-instance] $(Lean.mkIdent name):ident))
      let aliasName := ("OwnedSealInstance" ++ toString index).toName
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

example (S : TCSlib.Cryptography.Composability.FixedLengthPKScheme) (cap : Complexity.PolyExpr)
    (ist : ℕ → ℕ) :
    (TCSlib.Cryptography.Composability.AdaptiveCPA.acHandler S cap ist).perCall = .const 1 := by
  rfl
