import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Symmetric
import Lean

namespace TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
open Encryption.PublicKey

run_cmd do
  let home := `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Symmetric
  let env ← Lean.getEnv
  for tok in ["Equiv.apply_symm_apply", "Equiv.coe_addRight", "Equiv.ofBijective_apply", "Equiv.symm_apply_apply", "Equiv.trans_apply", "Int.cast_natCast", "LWE.decisionAdvantage_eq", "Matrix.submatrix_apply", "Matrix.vecMul_add", "Matrix.vecMul_smul", "Prod.mk.eta", "abs_sub_comm", "acceptProb_comp_equiv", "acceptProb_def", "add_comm", "distAdv_def", "encrypts_iff", "hE", "hideal", "hreal", "id_eq", "symEncrypt_apply"] do
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
