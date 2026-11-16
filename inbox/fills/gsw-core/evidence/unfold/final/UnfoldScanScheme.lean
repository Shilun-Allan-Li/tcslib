import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Scheme
import Lean

namespace TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
open Encryption.PublicKey

run_cmd do
  let home := `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Scheme
  let env ← Lean.getEnv
  for tok in ["Bool.false_eq_true", "Bool.toNat_false", "Bool.toNat_true", "Fin.init_def", "Fin.snoc_castSucc", "Fin.snoc_last", "Fin.sum_univ_castSucc", "Finset.sum_const_zero", "Finset.sum_neg_distrib", "Fintype.sum_eq_single", "Int.cast_mul", "Int.cast_natCast", "Int.cast_one", "Int.cast_sum", "Int.cast_zero", "LWE.BitEncoding.codepoint_eq", "LWE.noisyValues_apply", "Matrix.dotProduct_mulVec", "Matrix.transpose_apply", "Matrix.vecMul_add", "Matrix.vecMul_smul", "Matrix.vecMul_vecMul", "Nat.cast_one", "Nat.cast_zero", "Nat.mod_eq_of_lt", "Nat.mul_div_cancel", "Nat.sub_add_cancel", "Pi.neg_apply", "Pi.zero_apply", "Regev.augmented_eq", "Regev.decrypt_eq", "Regev.keygen_fst", "Regev.keygen_snd", "TrapdoorFunctions.Lossy.digits_val", "ZMod.val_natCast", "ZMod.val_zero", "add_comm", "add_dotProduct", "decide_eq_false", "decide_eq_true", "decryptColumn_eq", "decrypt_eq", "digit_val", "digits_decomposeVec", "encrypt_eq", "encrypts_iff", "gadget_mulVec_decomposeVec", "h2", "hC", "halfVector_eq", "hb", "hc", "hdec", "herr", "hhalf", "hi\u2080", "hq", "hs", "hsplit", "hsum", "hw", "hz", "if_false", "if_pos", "if_true", "lift_apply", "mul_one", "mul_zero", "neg_add_cancel_left", "neg_mul", "one_mul", "pow_succ", "secretVector_eq", "smul_dotProduct", "smul_eq_mul", "vecMul_secretVector_augmented", "zero_add", "zero_mul"] do
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
