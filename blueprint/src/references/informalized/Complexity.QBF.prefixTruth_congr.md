<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Formulas/QBF.lean :: Complexity.QBF.prefixTruth_congr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Invariance Under Equivalent Predicates

**Claim.** If two predicates on Boolean assignments agree on every assignment, then any finite quantifier prefix is true with one predicate exactly when it is true with the other.

**Proof.** Apply the invariance result for predicates that agree on assignments matching the initial segment (`Complexity.QBF.prefixTruth_congr_agree`). Its hypothesis holds here because the predicates are equivalent on every assignment, and therefore in particular on every assignment agreeing with the given one below the starting index. The result gives the desired equivalence for the whole prefix.

**Key facts.** `Complexity.QBF.prefixTruth_congr_agree`.
