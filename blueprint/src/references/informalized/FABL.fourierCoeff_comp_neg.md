<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadThreeSat.lean :: FABL.fourierCoeff_comp_neg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Coefficients Under Sign Reversal

**Claim.** For every natural number $n$, every real-valued function $f$ on the $n$-dimensional sign cube, and every coordinate set $S\subseteq\{1,\ldots,n\}$, the Fourier coefficient at $S$ of $x\mapsto f(-x)$ equals $(-1)^{|S|}$ times the Fourier coefficient of $f$ at $S$.

**Proof.** In the expectation defining the coefficient of $x\mapsto f(-x)$, change variables by the bijection $x\mapsto -x$ of the sign cube. This rewrites the integrand as $f(x)$ times the monomial evaluated at $-x$. The monomial sign-reversal identity says that this latter monomial is $(-1)^{|S|}$ times the monomial at $x$ (`monomial_neg_input`). Thus the integrand is the constant $(-1)^{|S|}$ times the one defining the coefficient of $f$. Pulling that constant out of the finite expectation proves the claim.

**Key facts.** `FABL.monomial_neg_input`.
