<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.productTotalInfluence_uniformSign_eq_totalInfluence -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform product and cube influence

**Claim.** For every real-valued function on the sign cube, total influence under the uniform product law equals the usual total influence defined using discrete derivatives.

**Proof.** Expand both total influences as sums over coordinates. For each coordinate, the product influence under the uniform sign law equals the cube influence defined by the squared discrete derivative (\texttt{productInfluence\_uniformSign\_eq\_influence}). Summing these coordinatewise equalities gives the result.

**Key facts.** `FABL.productInfluence_uniformSign_eq_influence`.
