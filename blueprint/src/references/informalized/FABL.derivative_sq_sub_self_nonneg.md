<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/UnateFunctions.lean :: FABL.derivative_sq_sub_self_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative Square Nonnegativity

**Claim.** For a sign-valued function on the Boolean cube, the square of its discrete derivative at any coordinate and input, minus the derivative itself, is nonnegative.

**Proof.** The two values of the real-valued function obtained by setting coordinate $i$ to $1$ and to $-1$ are each either $1$ or $-1$. By the discrete derivative formula (`discreteDerivative_apply`), the derivative is half their difference, so it is one of $-1,0,1$. For each of these three values $t$, $t^2-t$ is nonnegative, proving the claim.

**Key facts.** `FABL.discreteDerivative_apply`.
