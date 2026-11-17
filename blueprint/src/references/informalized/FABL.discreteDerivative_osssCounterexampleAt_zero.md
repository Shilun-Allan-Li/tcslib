<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeExercises.lean :: FABL.discreteDerivative_osssCounterexampleAt_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero Coordinate Derivative Formula

**Claim.** For every real $t$ and every point $x$ of the three-dimensional sign cube, the discrete derivative in coordinate $0$ of $F_t$ is $(-s_1+s_2)/4$, where $s_j$ is the real sign value of coordinate $j$.

**Proof.** By the pointwise derivative formula ($\texttt{FABL.discreteDerivative\_apply}$), evaluate $F_t$ at the points with coordinate $0$ set to $1$ and $-1$, take their difference, and divide by $2$. In the defining expression for $F_t$, the terms independent of coordinate $0$ cancel. Simplifying the remaining terms using the sign values gives $(-s_1+s_2)/4$.

**Key facts.** `FABL.discreteDerivative_apply`.
