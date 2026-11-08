<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/UnateFunctions.lean :: FABL.derivative_sq_add_self_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegativity of derivative square plus derivative

**Claim.** For a sign-valued function $f$ on the sign cube, a coordinate $i$, and an input $x$, the square of the discrete derivative of its real-valued version at $x$, plus that derivative, is nonnegative.

**Proof.** By the formula for the discrete derivative ($\texttt{FABL.discreteDerivative\_apply}$), the derivative is half the difference between the two values of $f$ obtained by setting coordinate $i$ to $1$ and to $-1$. Each of those values is either $1$ or $-1$, so the derivative is one of $-1,0,1$. For each of these possibilities, its square plus itself is respectively $0,0,2$, and hence is nonnegative.

**Key facts.** `FABL.discreteDerivative_apply`.
