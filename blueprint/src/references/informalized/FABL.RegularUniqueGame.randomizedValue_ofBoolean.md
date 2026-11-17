<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.randomizedValue_ofBoolean -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Randomized Value on Boolean Assignments

**Claim.** For a Boolean assignment, the randomized value of the check equals the predicate indicator evaluated on the assignment's answers to the check's queries.

**Proof.** The randomized value of the check is the predicate's randomized value at the coordinate means supplied by the bounded functions. The randomized-value identity (`SignPredicate.randomizedValue_eq_multilinearExtension`) rewrites it as the predicate's multilinear extension at those means. For the Boolean assignment, each mean is the real sign value of its answer. The multilinear extension on sign values equals the predicate indicator (`multilinearExtension_signValues`), yielding the asserted identity.

**Key facts.** `FABL.SignPredicate.randomizedValue_eq_multilinearExtension`, `FABL.RegularUniqueGame.multilinearExtension_signValues`.
