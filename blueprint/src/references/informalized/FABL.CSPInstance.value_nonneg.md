<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSP.lean :: FABL.CSPInstance.value_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegativity of the Constraint Satisfaction Value

**Claim.** For any domain, predicate family, instance, and assignment as specified, the fraction of constraints satisfied is nonnegative.

**Proof.** The satisfied count is a sum of indicators taking values zero or one, so it is nonnegative. The constraint count is positive because the constraint multiset is nonempty. A quotient of nonnegative numbers by a positive number is nonnegative, and the value is this quotient.
