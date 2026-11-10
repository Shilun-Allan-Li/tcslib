import TCSlib.Cryptography.TrapdoorFunctions.AllButOne.AntiCyclic

#print axioms TCSlib.Cryptography.TrapdoorFunctions.AllButOne.antiCyclic
#print axioms TCSlib.Cryptography.TrapdoorFunctions.AllButOne.antiCyclic_apply
#print axioms TCSlib.Cryptography.TrapdoorFunctions.AllButOne.antiCyclic_sub
#print axioms TCSlib.Cryptography.TrapdoorFunctions.AllButOne.antiCyclic_mulVec_injective
#print axioms TCSlib.Cryptography.TrapdoorFunctions.AllButOne.branch_difference_injective
#print axioms TCSlib.Cryptography.TrapdoorFunctions.AllButOne.branch_message_bound
#print axioms Polynomial.cyclotomic.irreducible_rat
#print axioms Polynomial.cyclotomic_prime_pow_eq_geom_sum
#print axioms AdjoinRoot.instField
#print axioms AdjoinRoot.mk_self
#print axioms AdjoinRoot.powerBasis'
#print axioms Module.Basis.equivFun_symm_apply
#print axioms Fin.intCast_val_sub_eq_sub_add_ite
#print axioms Equiv.sum_comp

open Lean in
run_cmd do
  let env ← getEnv
  for (n, ci) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? n then
      let mod := env.header.moduleNames[idx.toNat]!
      if mod.toString == "TCSlib.Cryptography.TrapdoorFunctions.AllButOne.AntiCyclic" then
        let kind := match ci with
          | .axiomInfo _ => "axiom"
          | .defnInfo _ => "definition"
          | .thmInfo _ => "theorem"
          | .opaqueInfo _ => "opaque"
          | .quotInfo _ => "quotient"
          | .inductInfo _ => "inductive"
          | .ctorInfo _ => "constructor"
          | .recInfo _ => "recursor"
        logInfo m!"COMBINED_CONSTANT|{mod}|{n}|{kind}|{isPrivateName n}"
        let axs ← Lean.collectAxioms n
        let labels := String.intercalate "," (axs.toList.map fun a => a.toString)
        logInfo m!"COMBINED_AXIOMS|{n}|{labels}"
