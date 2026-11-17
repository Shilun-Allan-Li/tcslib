<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/HypercontractiveApplications.lean :: FABL.uniformLpNorm_abs_rpow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Power scaling of the uniform norm

**Claim.** For real numbers $p,c>0$ and a function $f:\Omega\to\mathbb R$, the uniform $L^{p/c}$ quantity of $x\mapsto |f(x)|^c$ equals the uniform $L^p$ quantity of $f$, raised to the power $c$.

**Proof.** Since $p,c>0$, the exponent $p/c$ is positive. In the moment defining the left-hand norm, the function value is nonnegative, so its absolute value is itself. The power law for real powers of a nonnegative number then gives $\bigl(|f(x)|^c\bigr)^{p/c}=|f(x)|^{c(p/c)}=|f(x)|^p$. Thus the two moments agree. Write their common value as $M$; it is nonnegative because it is an expectation of nonnegative terms. The left-hand norm is $M^{(p/c)^{-1}}=M^{p^{-1}c}$, while the right-hand side is $(M^{p^{-1}})^c$. The power law $(u^a)^b=u^{ab}$ for $u\ge 0$ identifies these expressions.
