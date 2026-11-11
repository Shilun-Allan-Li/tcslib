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
    "Complexity.NUPPT.inCoins",
    "Complexity.NUPPT.inParam",
    "Complexity.NUPPT.ofPolyTimeUniform",
    "Complexity.NUPPT.runAt",
    "Complexity.NUPPT.runAtL",
    "Complexity.NUPPT.toComp",
    "Complexity.PolyTimeComputable",
    "Complexity.pairFstD",
    "Complexity.pairSndD",
    "TCSlib.Cryptography.Composability.FixedLengthScheme.INDSecure",
    "TCSlib.Cryptography.Composability.FixedLengthScheme.decAnswer",
    "TCSlib.Cryptography.Composability.FixedLengthScheme.decOpen",
    "TCSlib.Cryptography.Composability.FixedLengthScheme.encryptAt",
    "TCSlib.Cryptography.Composability.FixedLengthScheme.inLens",
    "TCSlib.Cryptography.Composability.FixedLengthScheme.indCodec",
    "TCSlib.Cryptography.Composability.FixedLengthScheme.indGame",
    "TCSlib.Cryptography.Composability.FixedLengthScheme.indImpl",
    "TCSlib.Cryptography.Composability.FixedLengthScheme.outLens",
    "TCSlib.Cryptography.Composability.FixedLengthScheme.splitHalf",
    "TCSlib.Cryptography.Games.MachineCodec.encodeLog",
    "TCSlib.Cryptography.Games.OracleComp.bind",
    "TCSlib.Cryptography.Games.ProbComp.expect",
    "TCSlib.Cryptography.Games.ProbComp.prob",
    "TCSlib.Cryptography.Games.ProbComp.sample",
    "TCSlib.Cryptography.Games.accept",
    "TCSlib.Cryptography.Games.advantage",
    "TCSlib.Cryptography.Games.bitCodec",
    "TCSlib.Cryptography.Games.buildComp",
    "TCSlib.Cryptography.Games.decodeBitMove",
    "TCSlib.Cryptography.Games.simulate",
    "TCSlib.Cryptography.Games.zeroBits",
    "TCSlib.Cryptography.Negligible",
    "TCSlib.Cryptography.decodeFin",
    "TCSlib.Cryptography.padFin",
    "TCSlib.Cryptography.prfDecFun",
    "TCSlib.Cryptography.prfDecWF",
    "TCSlib.Cryptography.prfEncFun",
    "TCSlib.Cryptography.prfScheme",
    "Turing.pairEncode"]
  for index in [:names.size] do
    let name := names[index]!.toName
    let some ci := (← Lean.getEnv).find? name | throwError "Missing seal candidate {name}"
    unless ci.isDefinition do throwError "Nondefinition seal candidate {name}"
    if Lean.Meta.isInstanceCore (← Lean.getEnv) name then
      Lean.Elab.Command.elabCommand (← `(command| attribute [-instance] $(Lean.mkIdent name):ident))
      let aliasName := ("OracleFromPRFSealInstance" ++ toString index).toName
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

example (S : TCSlib.Cryptography.Composability.FixedLengthScheme) (n : ℕ) :
    S.inLens n 2 = n + n := by
  rfl
