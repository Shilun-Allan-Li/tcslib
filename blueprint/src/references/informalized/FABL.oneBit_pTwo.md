<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/OneBitHypercontractivity.lean :: FABL.oneBit_pTwo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-bit $(p,2)$ inequality

**Claim.** For $1\le p\le2$ and $0\le\rho\le\sqrt{p-1}$, the $2$-norm of $a+\rho bx$ on a uniform sign is at most the $p$-norm of $a+bx$.

**Proof.** The affine-sign norm formulas identify the left-hand norm with $\sqrt{a^2+\rho^2b^2}$ and the right-hand norm with $\big((|a+b|^p+|a-b|^p)/2\big)^{1/p}$ (\texttt{uniformLpNorm\_two\_affineSign} and \texttt{uniformLpNorm\_affineSign}). From $\rho\le\sqrt{p-1}$ and $p\ge1$ we get $\rho^2\le p-1$. Hence $a^2+\rho^2b^2\le a^2+(p-1)b^2$, and taking square roots preserves the inequality. The one-bit affine Hanner inequality (\texttt{affine\_pTwo\_hanner}) bounds this last square root by the stated $p$-norm expression, proving the result.

**Key facts.** `FABL.uniformLpNorm_two_affineSign`, `FABL.uniformLpNorm_affineSign`, `FABL.affine_pTwo_hanner`.
