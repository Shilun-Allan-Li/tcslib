<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/SharpLevelOneInequality.lean :: FABL.fourierCoeff_linearForm_singleton -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Singleton coefficient of a linear form

**Claim.** For a linear form with coordinate weights $a$, the Fourier coefficient at the singleton frequency $\{i\}$ is $a_i$.

**Proof.** Expand the linear form into its coordinate terms and interchange the finite sum with expectation. For each coordinate $j$, its contribution to the coefficient at $\{i\}$ is $a_j$ times the expected product of the monomials at $\{j\}$ and $\{i\}$. Monomial orthogonality (`FABL.expect_monomial_mul`) makes this contribution zero unless $j=i$, when it equals $a_i$. Summing leaves $a_i$.

**Key facts.** `FABL.expect_monomial_mul`.
