import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Noise
import Lean

namespace TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW

run_cmd do
  let home := `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Noise
  let env ← Lean.getEnv
  for tok in ["Bool.toNat_true", "Finset.sum_empty", "Finset.sum_insert", "Int.cast_add", "Int.cast_mul", "Int.cast_natCast", "Int.cast_neg", "Int.cast_one", "Int.cast_sum", "Int.cast_zero", "Int.natAbs_mul", "Int.natAbs_natCast", "List.all_cons", "List.all_nil", "List.length_cons", "List.length_nil", "Matrix.add_vecMul", "Matrix.smul_vecMul", "Matrix.vecMul_add", "Matrix.vecMul_neg", "Matrix.vecMul_vecMul", "Matrix.vecMul_zero", "Nat.cast_one", "Nat.succ_mul", "Pi.add_apply", "Pi.neg_apply", "Pi.smul_apply", "Pi.zero_apply", "add_zero", "chain_cons", "chain_nil", "encrypts_iff", "gadget_mul_decompose", "hC", "hC\u2081", "hC\u2082", "hX", "hand", "hm", "hn", "id_eq", "lift_apply", "mul_assoc", "mul_eq", "nand_eq", "one_mul", "one_smul", "smul_eq_mul", "sub_eq_add_neg", "zero_mul", "zero_smul"] do
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
