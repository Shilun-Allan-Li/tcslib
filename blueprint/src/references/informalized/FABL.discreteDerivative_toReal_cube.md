<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/KKL.lean :: FABL.discreteDerivative_toReal_cube -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cubic Derivative Identity

**Claim.** For every Boolean function, coordinate, and cube point, the cube of the discrete derivative of its real-valued version equals the derivative itself.

**Proof.** At the two points obtained by setting coordinate $i$ to $1$ and $-1$, respectively, the Boolean function takes values in $\{\pm1\}$. The discrete derivative is their real-valued difference divided by $2$ (`discreteDerivative_apply`). If the two values agree, this derivative is $0$; if they differ, it is $1$ or $-1$. In each case its cube equals itself.

**Key facts.** `FABL.discreteDerivative_apply`.
