<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/OneBitHypercontractivity.lean :: FABL.uniformLpNorm_const_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scaling the uniform norm

**Claim.** For a finite set $\Omega$, real numbers $p,c$ with $p>0$, and a function $f:\Omega\to\mathbb R$, the uniform $L^p$ quantity of $cf$ equals $|c|$ times the uniform $L^p$ quantity of $f$.

**Proof.** At each point, $|cf(x)|=|c|\,|f(x)|$. Raising both sides to the exponent $p$ using the product rule for real powers gives $|cf(x)|^p=|c|^p|f(x)|^p$. Averaging over $\Omega$ therefore factors out $|c|^p$. The expectation of $|f|^p$ is nonnegative, as is $|c|^p, so the product rule applies once more to the outer $p^{-1}$ power. The result is $|c|^{p\cdot p^{-1}}$ times the uniform norm of $f$, which is $|c|$ times that norm because $p>0$.
