<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/BentDegree.lean :: FABL.isVectorFourierGranular_booleanRealEmbedding_of_isBent -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Granularity from bentness

**Claim.** If the real sign encoding of a binary function is bent, then its Boolean real embedding is vector Fourier granular with granularity $2^{-(\lfloor n/2\rfloor+1)}$.

**Proof.** Fix a frequency $\gamma$ and let $S$ be its support. The Boolean real embedding is related to the sign encoding by $b=(1-f)/2$. The Fourier coefficient of this affine transformation is therefore $\bigl(\mathbf 1_{S=\varnothing}-\widehat f(S)\bigr)/2$ (`FABL.fourierCoeff_one_sub_div_two`); the identification of vector Fourier coefficients with these sign-cube coefficients is given by `FABL.vectorFourierCoeff_eq_fourierCoeff_binaryFunctionOnSignCube`. Bentness says that the absolute value of $\widehat f(S)$ is $2^{-\lfloor n/2\rfloor}$, so it equals either that positive number or its negative. If $S$ is empty, the numerator is $1-\widehat f(S)$: the two possible signs give the integer multiples $2^{\lfloor n/2\rfloor}-1$ or $2^{\lfloor n/2\rfloor}+1$ of the target granularity after division by two. If $S$ is nonempty, the numerator is $-\widehat f(S)$, giving either $-1$ or $1$ times the target granularity. Thus every vector Fourier coefficient is an integer multiple of the stated granularity. The characterization of vector Fourier granularity by this coefficient condition completes the proof (`FABL.isVectorFourierGranular_iff`).

**Key facts.** `FABL.isVectorFourierGranular_iff`, `FABL.vectorFourierCoeff_eq_fourierCoeff_binaryFunctionOnSignCube`, `FABL.realSignEncodedFunction_eq_one_sub_two_booleanRealEmbedding`, `FABL.fourierCoeff_one_sub_div_two`.
