<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/SparsePolynomialApproximation.lean :: FABL.exists_parityMajorityRepresentation -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parity Majority Representation

**Claim.** Every Boolean function on a positive-dimensional sign cube admits a majority representation by signed parities, using the number of samples specified in the theorem, with each sampled Fourier coefficient nonzero.

**Proof.** Let $s=\lceil 4n\|\widehat f\|_1^2\rceil$. The real-valued function associated with a Boolean function is nonzero (`booleanFunction_toReal_ne_zero`), so its Fourier one-norm is positive (`fourierOneNorm_pos_of_ne_zero`). The ceiling bound, with approximation tolerance $1$, meets the sample-count hypothesis for the uniform approximation theorem. Thus there are $s$ sampled sets, each with nonzero Fourier coefficient, whose sampled Fourier polynomial differs from $f$ by less than $1$ at every input (`exists_fourierAtomSamples_uniformApproximation`). The sampled polynomial equals $\|\widehat f\|_1/s$ times the sum of the signed parity terms (`sampledFourierPolynomial_apply`). This scale factor is positive. Since $f$ takes only the values $1$ and $-1$, an error strictly less than $1$ forces the sampled polynomial to be positive when $f(x)=1$ and negative when $f(x)=-1$. Dividing by the positive scale preserves these signs, so thresholding the sum of signed parities recovers $f$ at every input.

**Key facts.** `FABL.booleanFunction_toReal_ne_zero`, `FABL.fourierOneNorm_pos_of_ne_zero`, `FABL.exists_fourierAtomSamples_uniformApproximation`, `FABL.sampledFourierPolynomial_apply`, `FABL.signValue_one`, `FABL.signValue_neg_one`, `FABL.thresholdSign_of_nonneg`, `FABL.thresholdSign_of_neg`.
