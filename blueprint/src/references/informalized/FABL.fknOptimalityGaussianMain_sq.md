<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FKNOptimality.lean :: FABL.fknOptimalityGaussianMain_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Square of the Gaussian Main Term

**Claim.** For every $q\in\mathbb{N}$, the square of the Gaussian main term equals $2\bigl(\frac{1}{q+2}\bigr)^2\log(q+2)$.

**Proof.** Write the main term as the mass $\alpha=1/(q+2)$ times $\sqrt{2\log(1/\alpha)}$. Since $1/\alpha>1$ (`one_lt_inv_fknOptimalityGaussianMass`), its logarithm is nonnegative. Thus squaring the square root gives $2\log(1/\alpha)$, and squaring the product gives $2\alpha^2\log(1/\alpha)$. Substituting the mass and its reciprocal yields the stated expression.

**Key facts.** `FABL.one_lt_inv_fknOptimalityGaussianMass`.
