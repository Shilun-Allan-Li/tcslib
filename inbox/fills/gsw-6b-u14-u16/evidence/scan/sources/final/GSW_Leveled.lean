import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Leveled
open Lean Elab Command

namespace TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
open BoolCircuit
open Encryption.PublicKey

def idsToCheck : List String := ["Cc.depthAt_gate","Cc.depth_eq","Cc.eval_eq","Cc.values_eq","DAGCircuit.layerNAND_depth","DAGCircuit.layerNAND_eval","DAGCircuit.toNANDForm_eval","DAGGate.depth_eq","Fin.append_left","Fin.append_right","Fin.coe_castSucc","Fin.val_succ","List.getD_eq_getElem","List.getElem_ofFn","List.length_ofFn","dif_neg","dif_pos","evalKey_eq","h0","hB","hcast","hlev","hm","homAnd_singleton","homNot_eq","hsucc","levelGate","levelGate_of_lt","levelKey_eq","leveledEvalCircuit_eq","leveledEval_eq","litInput_castAdd","litInput_natAdd","literalCts_castAdd","literalCts_eq","literalCts_natAdd"]
def scannedModule : Name := `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Leveled

#eval show CommandElabM Unit from do
  let env ← getEnv
  let modOf (c : Name) : Name :=
    ((env.getModuleIdxFor? c).map fun i => env.header.moduleNames[i.toNat]!).getD scannedModule
  for s in idsToCheck do
    let n := s.toName
    let cands ← liftCoreM <| (realizeGlobalConstWithInfos (mkIdent n)) <|> pure []
    if cands.isEmpty then IO.println s!"{s}\t-\tlocal/unresolved\t-"
    else for c in cands do
      let k := match env.find? c with
        | some (.thmInfo _) => "theorem"
        | some (.defnInfo _) => "DEF"
        | some (.opaqueInfo _) => "opaque"
        | some (.inductInfo _) => "inductive"
        | some (.ctorInfo _) => "ctor"
        | some _ => "other"
        | none => "?"
      let m := modOf c
      let tag := if k == "DEF" then
          (if m == scannedModule then "own-def" else if (`TCSlib).isPrefixOf m then "FOREIGN-TCSLIB-DEF" else "core/mathlib-def")
        else k
      IO.println s!"{s}\t{c}\t{tag}\t{m}"

end TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
