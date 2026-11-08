<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.pmfExpectation_finiteCandidatePMF -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expectation Under a Candidate Label Law

**Claim.** The expectation under the law that is uniform on a nonempty candidate set and concentrated at the default otherwise equals the corresponding finite candidate average, with the default used in the empty case.

**Proof.** Split according to whether the candidate set is nonempty. In the nonempty case, the uniform law assigns each candidate mass equal to the reciprocal of the set’s cardinality and all other elements mass zero. Substituting these masses into the finite expectation gives the uniform average over the candidate set. In the empty case, the law is concentrated at the default, so its expectation is the value at that element, as required.
