<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/KWiseIndependentLowerBound.lean :: FABL.IsKWiseIndependentMultiset.expect_monomial_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Orthogonality of Monomials

**Claim.** Under the stated limited-independence hypothesis, if $|S\cup T|\le k$, then the expectation of the product of the monomials indexed by $S$ and $T$ is $1$ when $S=T$ and $0$ otherwise.

**Proof.** If $S=T$, the product of the two monomials is the square of one sign-valued monomial, hence is identically $1$; its uniform expectation is therefore $1$. Now suppose $S\ne T$. The product of the monomials is the monomial indexed by the symmetric difference $S\triangle T$ (`monomial_mul_monomial`). This symmetric difference is nonempty, and its size is at most $|S\cup T|$, hence at most $k$. The limited-independence assumption therefore makes the absolute value of the corresponding nonconstant Fourier coefficient at most zero, so that coefficient is zero. The Fourier coefficient for the distribution induced by $A$ equals the uniform expectation of that monomial evaluated at $A$ (`fourierCoeff_signMultisetDensity`). Thus the original expectation is zero, as required.

**Key facts.** `FABL.monomial_mul_monomial`, `FABL.fourierCoeff_signMultisetDensity`.
