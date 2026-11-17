<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.finiteCandidateExpectation_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegative Candidate Expectation

**Claim.** For a finite candidate set, a default value, and a real-valued function nonnegative at every candidate, its finite candidate expectation is nonnegative.

**Proof.** If the candidate set is nonempty, the candidate expectation is the uniform finite average of the function values, each of which is nonnegative; hence the average is nonnegative. If the set is empty, the expectation is defined to be the value at the default, which is also nonnegative by the pointwise hypothesis.
