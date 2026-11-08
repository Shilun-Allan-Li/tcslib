<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.productProbabilityPMF_uniformSign -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform product signs

**Claim.** For every natural number $n$, the product distribution of $n$ independent uniform signs is the uniform distribution on sign vectors of length $n$.

**Proof.** Apply the uniform-product identity `productProbabilityPMF_uniform`: for any finite index type and finite nonempty value type, the independent product of identical uniform distributions is uniform on the function space. Take the index type to be the $n$ coordinates and the value type to be the two signs. This gives the asserted equality.

**Key facts.** `FABL.productProbabilityPMF_uniform`.
