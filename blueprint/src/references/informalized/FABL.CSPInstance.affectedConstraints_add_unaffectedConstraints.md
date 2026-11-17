<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSPDerandomization.lean :: FABL.CSPInstance.affectedConstraints_add_unaffectedConstraints -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Constraint partition by occurrence

**Claim.** The constraints whose scopes contain a fixed variable, together with those whose scopes omit it, form the full constraint multiset, including multiplicities.

**Proof.** Filter the constraint multiset by the property that the variable lies in the scope. The multiset filter partition identity says that filtering by a predicate and by its negation gives back the original multiset. Here those two filters are exactly the affected and unaffected constraints, so their sum is the full multiset.
