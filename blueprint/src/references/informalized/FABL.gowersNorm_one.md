<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Gowers.lean :: FABL.gowersNorm_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Norm of the constant function

**Claim.** For positive $k$, the Gowers norm of the constant function $1$ on the Boolean cube is $1$.

**Proof.** Both the Gowers norm of the constant function and $1$ are nonnegative, so equality follows once their $2^k$-th powers agree, since positive integer powers are injective on nonnegative reals. The power identity (`gowersNorm_pow`) identifies the first power with the diagonal inner product. In that inner product every factor in the cube product is $1$, so the product and its uniform average are both $1$. The $2^k$-th power of $1$ is also $1$, proving the claim.

**Key facts.** `FABL.gowersNorm_nonneg`, `FABL.gowersNorm_pow`.
