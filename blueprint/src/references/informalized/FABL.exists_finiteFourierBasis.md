<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductFourierBases.lean :: FABL.exists_finiteFourierBasis -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Existence of a finite Fourier basis

**Claim.** If the probability mass function has full support, then the space of real-valued functions on the finite sample space has an orthonormal basis for the weighted inner product whose distinguished vector is constant one.

**Proof.** Transport the weighted inner product to the ordinary Euclidean inner product by scaling each coordinate by the square root of its probability. The resulting vector corresponding to the constant-one function has squared norm equal to its weighted expectation, which is $1$; hence it has norm $1$. Choose any point of the sample space as the distinguished index and take the constant family consisting of this unit vector on that singleton. Extend it to an orthonormal basis of the Euclidean space; this is possible because the space has dimension equal to the number of sample points. Pull that basis back through the inverse scaling map. The vector at the distinguished index pulls back to the constant-one function, and preservation of inner products under the scaling identifies orthonormality in Euclidean space with orthonormality for the weighted expectation.

**Key facts.** `FABL.inner_pmfSqrtScaleLinearEquiv`, `FABL.pmfExpectation_const_one`, `FABL.pmfInner_eq_expect`.
