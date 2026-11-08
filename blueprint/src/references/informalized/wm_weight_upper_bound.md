<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/MistakeBounds/WeightedMajority.lean :: wm_weight_upper_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Geometric weight upper bound

**Claim.** If $W(0)=n$ and each step shrinks the positive sequence by a factor at most $(1+\beta)/2$, then $W(M)\le n((1+\beta)/2)^M$.

**Proof.** Apply the weight-shrinkage bound (`wm_weight_shrinkage`) to obtain $W(M)\le W(0)((1+\beta)/2)^M$. Substitute $W(0)=n$ to get the stated inequality.

**Key facts.** `wm_weight_shrinkage`.
