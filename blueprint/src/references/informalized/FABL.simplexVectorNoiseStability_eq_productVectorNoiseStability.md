<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/VectorValuedFourier.lean :: FABL.simplexVectorNoiseStability_eq_productVectorNoiseStability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Simplex and Product Noise Stability

**Claim.** The noise stability of a finite-valued function embedded as simplex vertices equals the vector-valued product noise stability of that embedding.

**Proof.** Expand both stability expressions using their definitions. Both are expectations over the same product input distribution. For each fixed input $x$, the inner product of the embedding at $x$ with the vector noise operator applied to the embedding equals the noise expectation of the inner products with the embedding at each output $y$; this is the real inner product identity for the vector product noise operator (\texttt{FABL.real\_inner\_vectorProductNoiseOperator}). The resulting integrands agree pointwise, so their expectations agree.

**Key facts.** `FABL.real_inner_vectorProductNoiseOperator`.
