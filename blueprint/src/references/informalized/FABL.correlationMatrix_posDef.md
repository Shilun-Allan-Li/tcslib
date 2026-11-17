<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/RegularThresholdNoiseStability.lean :: FABL.correlationMatrix_posDef -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive definiteness of the correlation matrix

**Claim.** For every real number $\rho$ with $-1<\rho<1$, the matrix $\begin{pmatrix}1&\rho\\\rho&1\end{pmatrix}$ is positive definite.

**Proof.** The matrix is symmetric. For a vector $x=(x_0,x_1)$, its quadratic form can be written as
\[
 x^{\mathsf T}\begin{pmatrix}1&\rho\\\rho&1\end{pmatrix}x
 =\frac{1+\rho}{2}(x_0+x_1)^2+\frac{1-\rho}{2}(x_0-x_1)^2.
\]
The bounds $-1<\rho<1$ make both coefficients strictly positive. If $x$ is nonzero, the two sums $x_0+x_1$ and $x_0-x_1$ cannot both vanish: together those equations would force $x_0=x_1=0$. Thus at least one squared term is positive, the other is nonnegative, and the quadratic form is strictly positive for every nonzero vector. This proves positive definiteness.
