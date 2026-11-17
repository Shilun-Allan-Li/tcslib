<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FKNImprovement.lean :: FABL.fourierCoeff_negatedInput_toReal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Coefficients Under Input Negation

**Claim.** For a Boolean function $f$ and coordinate set $S$, the Fourier coefficient of $x\mapsto -f(-x)$ is $-(-1)^{|S|}$ times the Fourier coefficient of $f$ at $S$.

**Proof.** In the expectation defining the coefficient, change variables from $x$ to $-x$, which is a bijection of the sign cube. The integrand becomes $-f(x)$ times the monomial at $-x$. Each coordinate in $S$ contributes one factor of $-1$ under input negation, so that monomial is $(-1)^{|S|}$ times the monomial at $x$. Pulling this constant factor outside the expectation gives $-(-1)^{|S|}$ times the coefficient of $f$ at $S$.
