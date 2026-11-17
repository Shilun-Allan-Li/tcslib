<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFourier.lean :: FABL.uniformLpNorm_sub_sq_comm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Symmetry of Squared Difference Norm

**Claim.** For $n\in\mathbb N$ and $f,g\colon\{-1,1\}^n\to\mathbb R$, the squared uniform $2$-norm of $f-g$ equals that of $g-f$.

**Proof.** The squared uniform $2$-norm of any function is its uniform expectation of the pointwise square (\texttt{uniformLpNorm_two_sq_eq_expect_sq}). Apply this identity to both differences. At each input, $g(x)-f(x)=-(f(x)-g(x))$, so their squares agree; therefore their uniform expectations agree as well.

**Key facts.** `FABL.uniformLpNorm_two_sq_eq_expect_sq`.
