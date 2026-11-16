import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Gadget
import Lean

namespace TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW

run_cmd do
  let home := `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Gadget
  let env ← Lean.getEnv
  for tok in ["Equiv.apply_symm_apply", "Finset.sum_eq_single", "Fintype.sum_prod_type", "Int.cast_mul", "Int.cast_natCast", "Int.cast_sum", "Matrix.mul_apply", "TrapdoorFunctions.Lossy.digits_eq", "ZMod.natCast_zmod_val", "ZMod.val_zero", "decomposeVec_eq", "decompose_apply", "digit_val", "digits_decomposeVec", "finProdFinEquiv.sum_comp", "gadget_apply", "h", "hj", "lift_apply"] do
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
