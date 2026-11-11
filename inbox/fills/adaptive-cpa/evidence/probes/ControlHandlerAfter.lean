import Lean
import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity
import TCSlib.Cryptography.Games.Efficiency
import TCSlib.Cryptography.Asymptotic.OneWayLemmas
import TCSlib.Cryptography.Asymptotic.EnsemblesLemmas
import TCSlib.Cryptography.Asymptotic.CollectionsHelpers
import TCSlib.Cryptography.Asymptotic.CollectionsLemmas
import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM.Run
import TCSlib.Complexity.ClassNP.PolyTimePrefix

run_cmd do
  let names : Array String := #[
    "Complexity.NUPPT.advInput",
    "Complexity.NUPPT.coinLen",
    "Complexity.NUPPT.coinsEquivPoly",
    "Complexity.NUPPT.output",
    "Complexity.NUPPT.runAt",
    "Complexity.PolyTimeComputable",
    "Complexity.PrefixByLength.drop",
    "Complexity.pairFstD",
    "Complexity.pairSndD",
    "TCSlib.Cryptography.EnsembleLemmas.padL",
    "TCSlib.Cryptography.FunFamily.blocks",
    "TCSlib.Cryptography.Games.InteractiveHandler.advInput",
    "TCSlib.Cryptography.Games.InteractiveHandler.call",
    "TCSlib.Cryptography.Games.InteractiveHandler.finInput",
    "TCSlib.Cryptography.Games.InteractiveHandler.finish",
    "TCSlib.Cryptography.Games.InteractiveHandler.impl",
    "TCSlib.Cryptography.Games.InteractiveHandler.input",
    "TCSlib.Cryptography.Games.MachineCodec.encodeLog",
    "TCSlib.Cryptography.Games.OracleComp.bind",
    "TCSlib.Cryptography.Games.bitCodec",
    "TCSlib.Cryptography.Games.buildComp",
    "TCSlib.Cryptography.Games.decodeBitMove",
    "TCSlib.Cryptography.Games.seedIn",
    "TCSlib.Cryptography.Games.zeroBits",
    "TCSlib.Cryptography.padFin",
    "Turing.pairEncode"]
  for index in [:names.size] do
    let name := names[index]!.toName
    let some ci := (← Lean.getEnv).find? name | throwError "Missing seal candidate {name}"
    unless ci.isDefinition do throwError "Nondefinition seal candidate {name}"
    if Lean.Meta.isInstanceCore (← Lean.getEnv) name then
      Lean.Elab.Command.elabCommand (← `(command| attribute [-instance] $(Lean.mkIdent name):ident))
      let aliasName := ("HandlerSealInstance" ++ toString index).toName
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

example (n : ℕ) (z ω s : List Bool) (i : Fin 2) (x L : List Bool) :
    TCSlib.Cryptography.Games.InteractiveHandler.input n z ω s i x L =
      Turing.pairEncode (Turing.pairEncode (List.replicate n true) (Turing.pairEncode z ω))
        (Turing.pairEncode s (Turing.pairEncode (Turing.pairEncode (List.replicate i true) x) L)) := by
  rfl
