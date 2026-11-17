<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/MatrixProductVerification.lean :: FABL.matrixProductRowZeroProbability_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero Dot-Product Probability

**Claim.** For a probability density $\phi$ on $\mathbb F_2^n$ and $\gamma\in\mathbb F_2^n$, the $\phi$-expectation of the indicator that $\gamma\cdot x$ is zero equals $\bigl(1+\mathbb E_{x\sim\phi}[(-1)^{\gamma\cdot x}]\bigr)/2$.

**Proof.** At each $x$, the indicator of $\gamma\cdot x=0$ equals $(1+\chi(x))/2$, where $\chi(x)$ is the binary sign of the dot product; the Walsh-character evaluation identifies this sign with the character in the claim. Multiplying by $\phi(x)$ and taking expectation, pull out the constant factor $1/2$ and distribute expectation over the sum. The result is $((\mathbb E_x\phi(x))+\mathbb E_x[\phi(x)\chi(x)])/2$. The density has expectation one, and the second term is its expectation of the Walsh character, giving the formula.

**Key facts.** `FABL.vectorWalshCharacter_apply`, `FABL.f₂ZeroIndicator_eq`, `FABL.ProbabilityDensity.expect_eq_one`.
