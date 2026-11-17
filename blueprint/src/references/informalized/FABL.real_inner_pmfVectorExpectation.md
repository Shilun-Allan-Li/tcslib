<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/VectorValuedFourier.lean :: FABL.real_inner_pmfVectorExpectation -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Inner Product and Finite Expectation

**Claim.** The inner product of a vector with the finite probability expectation of a vector-valued function equals the probability expectation of the pointwise inner products.

**Proof.** Expand the vector expectation as the finite sum of the probability weights times the function values. The inner product is additive in its second argument, so it distributes over this finite sum. It also pulls a real scalar out of its second argument. Consequently each summand becomes the probability weight multiplied by the inner product of the fixed vector with the corresponding function value. Summing these terms is precisely the scalar probability expectation in the statement.
