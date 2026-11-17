<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter01/BasicFourierFormulas.lean :: FABL.uniformProbability_one_add_neg_one_eq_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Probabilities of the two signs

**Claim.** For a sign-valued function on the sign cube, the uniform probabilities of the values $1$ and $-1$ sum to $1$.

**Proof.** At each input, the function's value is either the unit $1$ or the unit $-1$, since these are the two possibilities for an integer unit. Thus the indicators of these two events sum pointwise to $1$. Averaging over the cube gives the sum of their probabilities as the average of the constant function $1$, which is $1$.
