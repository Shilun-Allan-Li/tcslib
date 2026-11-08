<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/NoiseOperatorExercises.lean :: FABL.uniform_expect_prod_le_prod_uniformLpNorm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform Hölder Bound

**Claim.** For $r>0$, the uniform expectation of a product of $r$ nonnegative functions is at most the product of their uniform $L^r$ norms.

**Proof.** Write $N_i=\|g_i\|_r$ for each of the $r$ functions. If some $N_i=0$, its nonnegative $r$th-power average is zero, so that function vanishes at every point of the finite space. The product then has zero expectation, and the bound follows from nonnegativity of all the norms.

Otherwise all $N_i>0$. Normalize by setting $h_i=g_i/N_i$. Each normalized function is nonnegative and has average $r$th power equal to $1$. At each point, the weighted arithmetic-geometric mean inequality with all $r$ weights equal to $1/r$ gives $\prod_i h_i\le (1/r)\sum_i h_i^r$. Taking expectations shows that the normalized product has expectation at most $1$. Restoring the factors $N_i$ yields the result. The identities connecting the norm to its $r$th-power moment and its nonnegativity are supplied by $\texttt{uniformLpNorm_rpow}$ and $\texttt{uniformLpNorm_nonneg}$.

**Key facts.** `FABL.uniformLpNorm_nonneg`, `FABL.uniformLpNorm_rpow`.
