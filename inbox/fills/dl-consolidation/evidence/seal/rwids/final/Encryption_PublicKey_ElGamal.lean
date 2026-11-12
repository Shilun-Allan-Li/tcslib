import TCSlib.Cryptography.Encryption.PublicKey.ElGamal
open Lean Elab Command

namespace TCSlib.Cryptography.Candidates
open Complexity Turing NumberTheory Finset
open TCSlib.Cryptography.Candidates.GroupPKScheme

def idsToCheck : List String := ["Bool.false_eq_true","Equiv.coe_addRight","Equiv.prodAssoc_apply","Equiv.prodCongr_apply","Equiv.prodCongr_symm","Equiv.refl_apply","Equiv.refl_symm","Equiv.symm_symm","Equiv.symm_trans_apply","Fin.valEmbedding_apply","Fintype.card_fin","Function.comp_apply","GroupPKScheme.challenge","HardcoreBit.uexp_add","HardcoreBit.uexp_const","List.drop_drop","List.drop_left'","List.length_append","List.length_ofFn","List.length_replicate","List.length_take","List.tail_nil","List.take_left'","List.take_of_length_le","NUPPT.Uniform.runAtL_eq","NUPPT.advInput_eq","NUPPT.coinLen_eq","NUPPT.coins_ofPolyTimeUniform","NUPPT.distinguisherL_eq","NUPPT.distinguisher_eq","NUPPT.inAdvice_eq","NUPPT.inArg_eq","NUPPT.inCoins_eq","NUPPT.inParam_eq","NUPPT.layout_eq","NUPPT.runAtL_ofPolyTime","NUPPT.runAtL_ofPolyTimeUniform","NUPPT.runAt_eq","Nat.cast_one","Nat.cast_pow","Nat.mod_eq_of_lt","Nat.mod_mod","Nat.mod_mul_mod","Nat.mod_zero","Nat.not_le","Nat.sub_add_cancel","Nat.sub_eq_iff_eq_add","Ne","OneWay.uprob_congr","Option.getD_none","Option.getD_some","PolyExpr.eval_add","PolyExpr.eval_mul","PolyExpr.eval_var","Prod.map","Units.val_mk0","Units.val_one","Units.val_pow_eq_pow_val","ZMod.coe_unitOfCoprime","ZMod.natCast_eq_zero_iff","ZMod.natCast_mod","ZMod.val_add","ZMod.val_mul","ZMod.val_natCast","ZMod.val_natCast_of_lt","abs_abs","abs_le","abs_lt","acceptProb_comp_equiv","acceptProb_def","add_zero","card_map","constSelector","constSelector_runAt","ddhExpo_eq","ddhRandom_X","ddhReal_X","ddhTuple_eq","decide_eq_decide","decide_eq_true_eq","decide_eq_true_iff","decide_not","decodeFin_ofFn","distAdv_def","divModStr_pairEncode","div_le_iff₀","div_mul_eq_mul_div","dlG_eq","dlM_eq","dlP_eq","dlc_belowAcc","dlc_challenge_eq","dlc_ddhInput","dlc_encEquiv_ofFn","dlc_genEquiv","dlc_genEquiv_ofFn","dlc_grpEquiv","dlc_hyb1_point","dlc_safeMod","dlc_splitEquiv_symm_ofFn","dlc_tuplePk","dlc_uprob_shift","e","e1","e2","e3","egCanon","egDecStr","egDecStr_apply","egEnc","egEncParts","egEncRaw","egEnc_runAt","egGen","egGenCoins","egGenParts","egGenRaw","egGen_runAt","egGroupGenMachine","egGroupGenMachine_runAt","egGroupGenRaw","egGroupParts","egSquareGen","egUnit","elGamal","eval_ddhLen","expF_eq","expOrd_of_valid","expValid_iff","h","h'.not_ge","h0","h1","h2","h3","hC","hCc","hD'","hD'c","hE","hG","hM","hM'","hM'c","hM'len","hP","hS'","hW","ha","haA","hbF","hcq","he","hexpF","hfF","hgG","hgen","hi","hk","hlen","hm","hmM","ho","hord","hord'","hr'","hsq","hu","hval","hx","hxX","id","if_false","if_neg","if_pos","if_true","key","leStr_pairEncode","le_div_iff₀","length_ddhTuple","length_natToList","length_sizeStr","listToNat_addStr","listToNat_append","listToNat_mulStr","listToNat_natToList","listToNat_natToList_zero_append","listToNat_nil","listToNat_singleton_true","listToNat_subStr","mem_QR_iff_pow_eq_one","mem_filter","mem_insert","mem_map","mem_powers_iff_mem_zpowers","mem_singleton","mem_univ","modExpStr_pairEncode","mulStr_pairEncode","mul_assoc","mul_comm","mul_inv_cancel₀","mul_one","mul_one_div","natToList_eq","natToList_mod_two_pow","natToList_zero_append_drop","ofFn_padFin_of_length","one_div","one_div_pow","one_mul","orderOf_eq_zero_iff'.2","orderOf_one","orderOf_units","pairFstD_pairEncode","pairSndD_pairEncode","pow_add","pow_mod_orderOf","pow_mul","pow_one","pow_succ'","pow_zero","safePrimeValid_iff","sampleBelowL_eq_rejectBlocksL","show","sq","subStr_self","true_and","uprob_comp_equiv","uprob_eq_card_filter","uprob_eq_uexp","uprob_prod","xgcdStr_pairEncode","zero_pow","zpowers_eq_QR"]
def scannedModule : Name := `TCSlib.Cryptography.Encryption.PublicKey.ElGamal

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

end TCSlib.Cryptography.Candidates
