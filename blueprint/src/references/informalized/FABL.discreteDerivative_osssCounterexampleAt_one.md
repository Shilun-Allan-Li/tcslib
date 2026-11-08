<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeExercises.lean :: FABL.discreteDerivative_osssCounterexampleAt_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First Coordinate Derivative Formula

**Claim.** For every real $t$ and every point $x$ of the three-dimensional sign cube, the discrete derivative in coordinate $1$ of $F_t$ at $x$ is $(t-s_0+(t-1)s_2)/4$, where $s_j$ is the real sign value of coordinate $j$.

**Proof.** Use the pointwise derivative formula ($\texttt{FABL.discreteDerivative\_apply}$), which takes the difference of $F_t$ at the points with coordinate $1$ set respectively to $1$ and $-1$, then divides by $2$. Substituting the displayed definition of $F_t$ and evaluating these coordinate updates cancels the terms independent of coordinate $1$; the remaining difference simplifies to the claimed expression. The sign values satisfy the defining sign arithmetic, and ordinary real algebra completes the simplification.

**Key facts.** `FABL.discreteDerivative_apply`.
