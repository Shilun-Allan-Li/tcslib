<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSP.lean :: FABL.CSPInstance.fullySatisfied_iff_unsatisfiedCost_eq_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Full satisfaction and zero cost

**Claim.** An assignment satisfies every constraint of the instance if and only if its total unsatisfied cost, counted with multiplicity, is zero.

**Proof.** First rewrite the instance’s unsatisfied cost as the sum, over its constraint multiset, of the individual unsatisfied indicators (`FABL.CSPInstance.unsatisfiedCost_eq_sum`). The criterion that every constraint is satisfied exactly when this sum is zero is the multiset satisfaction equivalence (`FABL.CSPInstance.forall_satisfied_iff_sum_unsatisfied_eq_zero`). Together these give the claimed equivalence.

**Key facts.** `FABL.CSPInstance.unsatisfiedCost_eq_sum`, `FABL.CSPInstance.forall_satisfied_iff_sum_unsatisfied_eq_zero`.
