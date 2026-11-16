import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Eval
import Lean

namespace TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
open BoolCircuit
open Encryption.PublicKey

run_cmd do
  let home := `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Eval
  let env ← Lean.getEnv
  for tok in ["Bool.and_true", "Cc.depthAt_eq", "Cc.depthAt_gate", "Cc.depth_eq", "Cc.eval_eq", "Cc.values_eq", "DAGGate.depth_eq", "DAGGate.eval_eq", "Function.id_comp", "List.all_cons", "List.all_map", "List.all_nil", "List.any_eq_not_all_not", "List.forall\u2082_map_left_iff", "List.forall\u2082_map_right_iff", "List.forall\u2082_same", "List.getD_eq_getElem", "List.length_cons", "List.length_map", "List.length_ofFn", "List.length_singleton", "List.map_map", "Nat.add_sub_cancel", "Nat.sub_add_cancel", "Nat.sub_self", "evalValues_eq", "eval_eq", "hm", "hmsg", "homAnd_cons_cons", "homAnd_nil", "homAnd_singleton", "homGate_eq", "homNot_eq", "homOr_eq", "mul_assoc", "one_mul", "pow_succ'", "zero_add", "zero_mul"] do
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
