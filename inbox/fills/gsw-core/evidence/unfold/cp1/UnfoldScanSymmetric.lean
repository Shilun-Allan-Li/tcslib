import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Symmetric
import Lean

namespace TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
open Encryption.PublicKey

run_cmd do
  let home := `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Symmetric
  let env ← Lean.getEnv
  for tok in [] do
    let id := Lean.mkIdent (tok.toName)
    let cs ← (Lean.Elab.Command.liftCoreM (Lean.resolveGlobalConst id)) <|> pure []
    if cs.isEmpty then Lean.logInfo m!"UNFOLDSCAN {tok} UNRESOLVED"
    for c in cs do
      let some ci := env.find? c | continue
      let kind := match ci with
        | .thmInfo _ => "thm" | .defnInfo _ => "def" | .axiomInfo _ => "axiom"
        | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot"
        | .inductInfo _ => "induct" | .ctorInfo _ => "ctor" | .recInfo _ => "rec"
      let mod := match env.getModuleIdxFor? c with
        | some i => (env.header.moduleNames[i.toNat]!).toString
        | none => home.toString
      let red := (Lean.getReducibilityStatusCore env c).toAttrString
      let proj := env.isProjectionFn c
      let matcher := Lean.Meta.isMatcherCore env c
      Lean.logInfo m!"UNFOLDSCAN {tok} {c} {kind} {mod} red={red} proj={proj} matcher={matcher}"
