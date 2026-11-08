<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.WeightedConstraintExperiment.UniformRefinement.globallyFilteredCloneRawCSP_value_eq_expectation -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Raw value as a filtered expectation

**Claim.** For any assignment, the real-valued raw CSP value of the globally filtered clone instance equals the expected padded-clone payoff under the uniform distribution on globally filtered occurrences.

**Proof.** The expectation over a finite type is the sum of the values divided by the cardinality of that type. The raw instance's value is likewise the sum of its constraint satisfaction indicators divided by its number of constraints. Its constraints are the images of the globally filtered occurrences under the construction of the clone constraints, so this sum can be indexed by those occurrences. For each occurrence, the satisfaction indicator is $1$ exactly when the corresponding predicate evaluates to true, and otherwise is $0$. After converting these indicators from rational to real values, they agree term by term with the padded-clone payoffs. The denominators are both the cardinality of the globally filtered occurrence set, so the two averages are equal.
