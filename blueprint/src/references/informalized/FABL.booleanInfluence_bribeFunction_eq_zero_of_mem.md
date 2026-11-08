<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.booleanInfluence_bribeFunction_eq_zero_of_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influence of a Bribed Coordinate

**Claim.** If coordinate $i$ belongs to $J$, then the function obtained by setting all coordinates in $J$ to $b$ has zero influence in coordinate $i$.

**Proof.** At any input, bribing replaces every coordinate in $J$ by $b$. Since $i\in J$, flipping coordinate $i$ before bribing does not change the bribed input: coordinates in $J$ are set to $b$ in either case, and coordinates outside $J$ are unchanged by the flip. Thus the function has the same output before and after flipping coordinate $i$, so no input is pivotal. The uniform probability of the pivotal event is therefore zero.
