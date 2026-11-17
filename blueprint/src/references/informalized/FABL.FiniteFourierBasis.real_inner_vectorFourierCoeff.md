<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/VectorValuedFourier.lean :: FABL.FiniteFourierBasis.real_inner_vectorFourierCoeff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Inner product and vector Fourier coefficient

**Claim.** The inner product of $v$ with the vector Fourier coefficient of $f$ at $a$ equals the scalar Fourier coefficient at $a$ of the function $x\mapsto\langle v,f(x)\rangle$.

**Proof.** Expand the vector Fourier coefficient as the finite weighted sum defining its expectation. The inner product with a finite sum of scalar multiples of vectors is the corresponding sum of scalar multiples of inner products, so it equals the expectation of the pointwise inner products. For each input $x$, the vector being averaged is the product basis function at $x$ times $f(x)$. Bilinearity of the real inner product moves this scalar factor outside, giving the product basis function times $\langle v,f(x)\rangle$. This is exactly the defining expectation for the scalar Fourier coefficient of the stated function.

**Key facts.** `FABL.real_inner_pmfVectorExpectation`.
