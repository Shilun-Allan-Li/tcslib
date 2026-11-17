<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/ZkFourier.lean :: ZkFourier.zkDot_neg_left -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Negation in the left argument

**Claim.** For vectors $s,x\in(\mathbb{Z}/k\mathbb{Z})^n$, negating the left argument negates the dot product: $(-s)\cdot x=-(s\cdot x)$.

**Proof.** For each coordinate, $(-s_i)x_i=-(s_ix_i)$. Summing coordinatewise, the sum of the negatives is the negative of the sum. Hence $\sum_i(-s_i)x_i=-\sum_i s_ix_i$, as required.
