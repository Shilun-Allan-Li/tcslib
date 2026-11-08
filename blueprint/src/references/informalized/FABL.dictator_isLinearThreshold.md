<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/SocialChoiceFunctions/Definitions.lean :: FABL.dictator_isLinearThreshold -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dictators Are Linear Thresholds

**Claim.** For each coordinate, the function that returns its sign is a linear threshold function.

**Proof.** Choose bias $0$ and assign weight $1$ to coordinate $i$ and weight $0$ to every other coordinate. The resulting affine form at a sign vector $x$ is exactly the real value of $x_i$, since all terms except the $i$th vanish. A sign is either $1$ or $-1$: in the first case the form is nonnegative and the threshold returns $1$; in the second it is negative and the threshold returns $-1$. Thus the threshold agrees with the dictator at every $x$.
