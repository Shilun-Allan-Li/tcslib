<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/RandomRestrictions.lean :: FABL.discreteDerivative_extendedSignRestriction_of_not_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative Vanishes Outside the Free Coordinates

**Claim.** If $i$ is outside $J$, the discrete derivative in coordinate $i$ of the extended sign restriction is zero everywhere.

**Proof.** Write the derivative as the difference quotient of the extended restriction evaluated after setting coordinate $i$ first to $1$ and then to $-1$. Because $i\notin J$, the extended restriction does not change when coordinate $i$ is updated: the assembled point uses the fixed signs outside $J$ and the free signs from coordinates in $J$. The two function values are therefore equal, so their difference, and hence the derivative, is zero. The invariance under such an update is the fact that the extended restriction is unchanged by updating a coordinate outside $J$ (\texttt{FABL.extendedSignRestriction_setCoordinate_of_not_mem}).

**Key facts.** `FABL.extendedSignRestriction_setCoordinate_of_not_mem`.
