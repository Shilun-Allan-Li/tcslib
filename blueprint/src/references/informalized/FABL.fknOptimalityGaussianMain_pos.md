<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FKNOptimality.lean :: FABL.fknOptimalityGaussianMain_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive Gaussian Main Term

**Claim.** For every $q\in\mathbb{N}$, the quantity $\frac{1}{q+2}\sqrt{2\log(q+2)}$ is strictly positive.

**Proof.** The mass $1/(q+2)$ is positive. Its reciprocal is greater than $1$ (`one_lt_inv_fknOptimalityGaussianMass`), so the logarithm of that reciprocal is positive. Multiplying by $2$ preserves positivity, and its square root is positive as well. The main term is the product of this positive square root and the positive mass, so it is strictly positive.

**Key facts.** `FABL.one_lt_inv_fknOptimalityGaussianMass`.
