import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.SoundnessRep
open Lean Elab Command

namespace TCSlib.Cryptography.GI
open Complexity Turing Finset

def idsToCheck : List String := ["Bool.false_eq_true","Equiv.prodComm_apply","Fin.coe_castSucc","Fin.coe_divNat","Fin.coe_modNat","Fin.consEquiv_symm_apply","Fin.val_last","HardcoreBit.uprob_eq_one_of_forall","List.cons.injEq","List.drop_one","List.getD_eq_getElem?_getD","List.getElem?_drop","List.getElem?_ofFn","List.getElem?_take","List.getLastD_concat","List.headD_cons","List.length_append","List.length_ofFn","List.length_singleton","List.map_append","List.map_singleton","List.ofFn_succ_last","List.range_succ","List.tail_cons","Nat.add_mul_div_left","Nat.add_mul_mod_self_left","Nat.cast_zero","Nat.div_eq_of_lt","Nat.mod_eq_of_lt","OneWay.uprob_congr","Prod.fst_swap","Prod.snd_swap","and_true","blocksEquiv_apply","coinBlock_eq","coinSlice_blocksEquiv","coinSlice_gniTapes","decGraphAt_encGraph","decide_eq_false_iff_not","decide_eq_true_eq","decide_true","dif_pos","e1","e2","exec_succ","exec_vfirst_eq","gGuess","getD_ofFn_lt'","gniGraphs","gniProtocolRep_outV","gniProver_next_enc","gniRep_outV_eq","gniTapes","gniTapes_apply","gniVerifierRep_next_ge","gni_honest_reply","h1","h2","hT","hV","hi","hideal","hj","hlt","hrec","ht","hwf","id_eq","if_false","if_true","implies_true","instanceVertexCount_encInstance","instanceVertices_length_encInstance","moverIsV_def","moverIsV_true","ofFn_eq_map_range","ofFn_tapeSplit","show","true_and","uprob_comp_equiv","uprob_false","uprob_not","uprob_true","wellFormedInstance_encInstance","zero_add","zero_mul"]
def scannedModule : Name := `TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.SoundnessRep

#eval show CommandElabM Unit from do
  let env ← getEnv
  let modOf (c : Name) : Name :=
    ((env.getModuleIdxFor? c).map fun i => env.header.moduleNames[i.toNat]!).getD scannedModule
  for s in idsToCheck do
    let n := s.toName
    let cands ← liftCoreM <| (realizeGlobalConstWithInfos (mkIdent n)) <|> (Pure.pure [] : CoreM (List Name))
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

end TCSlib.Cryptography.GI
