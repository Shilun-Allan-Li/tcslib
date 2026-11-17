<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/PrescribedFourierSupport.lean :: FABL.fourierCoeff_prescribedFourierKernel -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier coefficients of the prescribed kernel

**Claim.** For a nonempty family $\mathcal F$ of coordinate subsets and a point $a$ in the sign cube, the Fourier coefficient of the prescribed Fourier kernel at $T$ is $(|\mathcal F|^{-1})\,\chi_T(a)$ when $T\in\mathcal F$, and is zero otherwise.

**Proof.** By the pointwise formula for the prescribed Fourier kernel (\(\texttt{FABL.prescribedFourierKernel_apply}\)), its product with the character \(\chi_T\) is a finite sum over \(S\in\mathcal F\). Pulling that sum through the uniform expectation expresses the desired coefficient as the sum, over \(S\in\mathcal F\), of \(|\mathcal F|^{-1}\chi_S(a)\) times the expected product \(\chi_S(x)\chi_T(x)\). Character orthogonality says this expectation is $1$ if $S=T$ and $0$ otherwise (\(\texttt{FABL.expect_monomial_mul}\)). Thus every summand vanishes except possibly the one with $S=T$; it occurs exactly when $T\in\mathcal F$, giving the stated value.

**Key facts.** `FABL.prescribedFourierKernel_apply`, `FABL.expect_monomial_mul`.
