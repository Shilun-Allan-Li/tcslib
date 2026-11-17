<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/ImprovedFKN.lean :: FABL.fourierCoeff_negatedInput_toReal' -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Coefficients Under Input Negation

**Claim.** For a Boolean function $f$ and coordinate set $S$, the Fourier coefficient of $x\mapsto -f(-x)$ is $-(-1)^{|S|}$ times the Fourier coefficient of $f$ at $S$.

**Proof.** Change variables in the defining expectation by the cube bijection $x\mapsto -x$. Under this substitution, the integrand becomes $-f(x)$ times the monomial evaluated at $-x$. Negating each coordinate in $S$ changes the monomial by the factor $(-1)^{|S|}$. Thus the expectation is the constant $-(-1)^{|S|}$ times the expectation defining the original coefficient.
