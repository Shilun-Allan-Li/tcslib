<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadTests.lean :: FABL.BoundedCubeFunction.sum_sq_fourierCoeff_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on the Fourier coefficient squares

**Claim.** If a real-valued function on the sign cube takes all its values in $[-1,1]$, then the sum of the squares of its uniform Fourier coefficients is at most $1$.

**Proof.** Parseval's identity (`FABL.parseval`) identifies the sum of the squared Fourier coefficients with the uniform inner product of $f$ with itself. Writing that inner product as a uniform average, its numerator is the sum of $f(x)^2$ over cube points. The bound $|f(x)|\leq 1$ implies $f(x)^2\leq 1$ pointwise, so this sum is at most the number of points in the cube. Dividing by that positive number gives an average at most $1$, as claimed.

**Key facts.** `FABL.parseval`.
