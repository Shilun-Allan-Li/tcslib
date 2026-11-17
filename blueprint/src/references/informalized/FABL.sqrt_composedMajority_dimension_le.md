<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ComposedMajorityInfluence.lean :: FABL.sqrt_composedMajority_dimension_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Composed Majority Dimension Bound

**Claim.** For every natural number $m$, $\sqrt{2m+3}\le2\sqrt{2m+1}$.

**Proof.** Both radicands are nonnegative, as are their square roots and twice the second square root. It is therefore enough to compare their squares. The resulting inequality is $2m+3\le4(2m+1)$, which holds for every $m\ge0$. Taking nonnegative square roots proves the claim.
