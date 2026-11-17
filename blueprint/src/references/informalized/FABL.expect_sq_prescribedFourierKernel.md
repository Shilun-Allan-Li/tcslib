<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/PrescribedFourierSupport.lean :: FABL.expect_sq_prescribedFourierKernel -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second moment of a prescribed Fourier kernel

**Claim.** For a nonempty family $\mathcal F$ and a sign vector $a$, the uniform expectation of the squared prescribed Fourier kernel is $1/|\mathcal F|$.

**Proof.** Parseval's identity expresses the second moment of the kernel as the sum of the squares of all its Fourier coefficients (by `FABL.parseval`). Each coefficient is $(|\mathcal F|^{-1})$ times the monomial at $a$ when its index belongs to $\mathcal F$, and is zero otherwise (by `FABL.fourierCoeff_prescribedFourierKernel`). Consequently only indices in $\mathcal F$ contribute. For each such index, the monomial has square one (by `FABL.monomial_sq`), so each contributes $|\mathcal F|^{-2}$. There are $|\mathcal F|$ such terms, giving $|\mathcal F|\cdot |\mathcal F|^{-2}=|\mathcal F|^{-1}$. Nonemptiness ensures this division is defined.

**Key facts.** `FABL.parseval`, `FABL.fourierCoeff_prescribedFourierKernel`, `FABL.monomial_sq`.
