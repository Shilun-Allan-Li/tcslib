<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/HypercontractiveNecessity.lean :: FABL.secondDeriv_nonneg_of_isLocalMin -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second Derivative at a Local Minimum

**Claim.** If a twice differentiable real function has a local minimum at $a$, then its second derivative at $a$ is nonnegative.

**Proof.** At a local minimum, the first derivative vanishes, so the specified derivative value $d$ is zero. Suppose for contradiction that $d_2<0$. The derivative of $f'$ at $a$ is then negative, and the second derivative test implies that $f$ has a local maximum at $a$ as well. In a neighborhood where both the local minimum and maximum inequalities hold, $f$ must equal the constant value $f(a)$. Thus $f$ is locally constant, and its derivative is locally zero. Consequently the derivative of $f'$ at $a$ is zero, contradicting $d_2<0$. Hence $d_2\ge0$.
