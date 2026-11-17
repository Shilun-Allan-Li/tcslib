<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/Regularity.lean :: FABL.isFourierRegular_zero_iff_exists_const -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Vanishing Fourier Coefficients and Constancy

**Claim.** A real-valued function on the Boolean cube has all nonempty-set Fourier coefficients equal to zero if and only if it is constant.

**Proof.** Suppose first that all nonempty-set coefficients vanish. By Fourier expansion, at any point $x$ the value $f(x)$ is the sum over all coordinate sets of the coefficient at $S$ times its monomial at $x$. Every term with nonempty $S$ vanishes, leaving only the empty-set term. The empty-set monomial is $1$, so $f(x)$ equals the fixed coefficient at the empty set, independently of $x$; hence $f$ is constant.

Conversely, suppose $f$ is the constant $c$. Its coefficient at $S$ is the expectation of $c$ times the monomial at $S$, and linearity pulls $c$ outside the expectation. The expectation of a monomial is zero for nonempty $S$. Thus every such coefficient vanishes, which is exactly the required zero regularity.

**Key facts.** `FABL.fourier_expansion`, `FABL.expect_monomial`.
