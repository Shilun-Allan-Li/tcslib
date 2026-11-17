<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.pmfExpectation_independentProductPMF_coordinate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Marginal Expectation of a Product Law

**Claim.** Under a product law with independent coordinates distributed according to their respective laws, the expectation of a function of one fixed coordinate equals its expectation under that coordinate’s marginal law.

**Proof.** Express the function of the fixed coordinate as a product over all indices: use the given function at that coordinate and the constant function $1$ at every other coordinate. The expectation of a product of coordinatewise functions under a product law factors into the product of their individual expectations (`pmfExpectation_independentProductPMF_prod`). Every factor away from the chosen coordinate is $1$ (`pmfExpectation_const_one`), leaving only the expectation under the chosen coordinate’s law.

**Key facts.** `FABL.pmfExpectation_independentProductPMF_prod`, `FABL.pmfExpectation_const_one`.
