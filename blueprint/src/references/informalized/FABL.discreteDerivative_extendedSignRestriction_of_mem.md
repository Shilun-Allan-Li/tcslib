<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/RandomRestrictions.lean :: FABL.discreteDerivative_extendedSignRestriction_of_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative of an Extended Sign Restriction

**Claim.** When $i$ belongs to the free coordinate set $J$, the discrete derivative of the extended restriction at $x$ agrees with the derivative of $f$ at the cube point assembled from $x$ on $J$ and the fixed signs outside $J$.

**Proof.** Expand both derivatives as difference quotients. The numerator on the left evaluates $f$ at the assembled points whose free assignments come from $x$ after setting coordinate $i$ to $1$ and to $-1$. Since $i\in J$, changing that free coordinate before assembling the full point has the same effect as changing coordinate $i$ in the assembled point itself. This follows coordinate by coordinate: at coordinate $i$ the updated sign is used, at other coordinates in $J$ the original sign from $x$ is used, and outside $J$ the fixed assignment is unchanged. Thus the two terms in the left numerator are precisely the corresponding two terms on the right, and the difference quotients agree.
