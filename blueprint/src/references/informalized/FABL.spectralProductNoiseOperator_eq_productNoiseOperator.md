<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.spectralProductNoiseOperator_eq_productNoiseOperator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equality of the two product noise operators

**Claim.** Under the stated finite probability space and orthonormal-basis assumptions, the spectral product noise operator equals the probabilistic product noise operator for every allowed correlation parameter and function.

**Proof.** Fix an input point $x$. The Fourier expansion theorem for the probabilistic product noise operator (\(\texttt{FiniteFourierBasis.productNoiseOperator\_fourier\_expansion}\)) expresses its value at $x$ as the sum over product-basis indices $a$, with each Fourier coefficient multiplied by $\rho$ to the power of the number of nonconstant coordinates and by the corresponding product-basis function at $x$. This is precisely the defining expression for the spectral product noise operator at $x$. Thus the two operators agree pointwise, and hence are equal as functions.

**Key facts.** `FABL.FiniteFourierBasis.productNoiseOperator_fourier_expansion`.
