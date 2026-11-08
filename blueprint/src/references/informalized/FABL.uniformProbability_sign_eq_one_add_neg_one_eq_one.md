<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/DictatorTesting.lean :: FABL.uniformProbability_sign_eq_one_add_neg_one_eq_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform probabilities of the two signs

**Claim.** For a sign-valued function on a finite nonempty set, the uniform probabilities that it equals $1$ and $-1$ sum to $1$.

**Proof.** At each point, the function's value is either $1$ or $-1$, the only two integer units. Hence the indicators of these two events sum pointwise to $1$. Taking the uniform average of this identity yields the sum of the two probabilities as the average of the constant function $1$, which equals $1$.
