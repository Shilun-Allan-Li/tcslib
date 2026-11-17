<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeExercises.lean :: FABL.discreteDerivative_osssCounterexampleAt_two -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second Coordinate Derivative Formula

**Claim.** For every real $t$ and every point $x$ of the three-dimensional sign cube, the discrete derivative in coordinate $2$ of $F_t$ at $x$ is $(t+s_0+(t-1)s_1)/4$, where $s_j$ is the real sign value of coordinate $j$.

**Proof.** Apply the pointwise derivative formula ($\texttt{FABL.discreteDerivative\_apply}$): evaluate $F_t$ with coordinate $2$ set to each sign, subtract the values, and divide by $2$. Expanding the definition of $F_t$ cancels the terms independent of coordinate $2}; simplifying the remaining terms using the sign values yields $(t+s_0+(t-1)s_1)/4$.

**Key facts.** `FABL.discreteDerivative_apply`.
