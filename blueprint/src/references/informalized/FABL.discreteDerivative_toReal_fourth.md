<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/KKL.lean :: FABL.discreteDerivative_toReal_fourth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourth Power of the Discrete Derivative

**Claim.** For every Boolean function, coordinate, and cube point, the fourth power of the discrete derivative of its real-valued version equals the square of that derivative.

**Proof.** The function values at the two points used to form the derivative are each $1$ or $-1$. Their difference divided by $2$ is therefore $0$, $1$, or $-1$, by the derivative formula (`discreteDerivative_apply`). For each of these three values, the fourth power equals the square.

**Key facts.** `FABL.discreteDerivative_apply`.
