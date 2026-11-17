<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/MistakeBounds/WeightedMajority.lean :: wm_weight_shrinkage -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Weight shrinkage bound

**Claim.** If each step up to $M$ multiplies a positive weight by at most $(1+\beta)/2$, then $W(M)\le W(0)((1+\beta)/2)^M$.

**Proof.** Proceed by induction on $M$. At $M=0$, both sides equal $W(0)$. For the successor case, the last-step hypothesis gives $W(M+1)\le W(M)(1+\beta)/2$. By the induction hypothesis, $W(M)\le W(0)((1+\beta)/2)^M$. The factor $(1+\beta)/2$ is nonnegative, so multiplying this latter inequality by it preserves the order. Combining the inequalities and using the successor power identity proves the bound at $M+1$.
