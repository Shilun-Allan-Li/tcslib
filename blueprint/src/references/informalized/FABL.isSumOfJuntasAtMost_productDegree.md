<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.isSumOfJuntasAtMost_productDegree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decomposition at the product degree

**Claim.** Every function has a decomposition into coordinate juntas at its product degree.

**Proof.** By the dimension bound, the function admits such a decomposition with parameter $n$. Thus the set of natural-number parameters for which a decomposition exists is nonempty. The product degree is defined as the least such parameter; the defining property of the least witness therefore supplies a decomposition at the product degree itself (`FABL.isSumOfJuntasAtMost_dimension`).

**Key facts.** `FABL.isSumOfJuntasAtMost_dimension`.
