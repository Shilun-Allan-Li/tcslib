<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BiasedCoin.lean :: Randomized.biasedProb_mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of Biased Probability

**Claim.** If $0\leq\rho\leq1$ and every length-$m$ string satisfying $A$ also satisfies $B$, then the biased probability of $A$ is at most that of $B$.

**Proof.** Induct on $m$. At length zero, the only string is empty. If it satisfies $A$, the hypothesis implies that it satisfies $B$, giving the desired comparison of the two probabilities. If it does not satisfy $A$, its probability for $A$ is zero, while the probability for $B$ is either zero or one. For the inductive step, expand both probabilities into their true and false first-bit branches (`Randomized.biasedProb_succ`). In each branch, the implication from the hypothesis still holds for every tail of length $m$: prefixing that tail by the chosen bit gives a string of length $m+1$. The induction hypothesis compares the two branch probabilities. Multiplication by the true-branch weight $\rho$ preserves the inequality because $\rho\geq0$; multiplication by the false-branch weight $1-\rho$ preserves it because $\rho\leq1$. Adding the two inequalities proves the result.

**Key facts.** `Randomized.biasedProb_succ`.
