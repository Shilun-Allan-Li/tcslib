<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductFourierBases.lean :: FABL.linearIndependent_of_pmf_orthonormal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Orthonormal Families Are Linearly Independent

**Claim.** A finite family of real-valued functions on a finite probability space is linearly independent if its pairwise probability-weighted inner products are $1$ on the diagonal and $0$ off the diagonal.

**Proof.** Suppose a linear combination of the family, with coefficients $c_i$, is the zero function. Fix an index $a$ and take its probability-weighted inner product with the function indexed by $a$. Distribute the finite sum through the inner product and use bilinearity of the expectation (`pmfExpectation_sum` and `pmfExpectation_const_mul`). The assumed orthonormality makes every term vanish except the one with index $a$, which equals $c_a$ because the diagonal inner product is $1$. The inner product of the zero function is zero (`pmfExpectation_const`), so $c_a=0$. Since this holds for every index, all coefficients vanish, proving linear independence.

**Key facts.** `FABL.pmfExpectation_sum`, `FABL.pmfExpectation_const_mul`, `FABL.pmfExpectation_const`.
