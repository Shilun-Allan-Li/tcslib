<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/VectorValuedFourier.lean :: FABL.real_inner_vectorProductNoiseOperator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Inner Product and Product Noise

**Claim.** Taking the inner product of a vector with the vector-valued product noise average equals applying scalar product noise to the function of pointwise inner products.

**Proof.** At the chosen input, the vector-valued noise operator is the finite probability expectation of the vector-valued function under the product noise law, while the scalar operator is the expectation under that same law of the pointwise inner products. Apply the fact that inner product commutes with finite probability expectation (\texttt{FABL.real_inner_pmfVectorExpectation}) to identify these two expressions.

**Key facts.** `FABL.real_inner_pmfVectorExpectation`.
