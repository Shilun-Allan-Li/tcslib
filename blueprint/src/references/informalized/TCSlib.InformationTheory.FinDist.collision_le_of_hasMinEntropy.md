<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/InformationTheory/FinDist.lean :: TCSlib.InformationTheory.FinDist.collision_le_of_hasMinEntropy -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Collision bound from min-entropy

**Claim.** If every outcome under a finite probability distribution has probability at most $2^{-k}$, then its collision probability is at most $2^{-k}$.

**Proof.** Write each square as $p(a)^2=p(a)p(a)$. The min-entropy hypothesis gives $p(a)\le 2^{-k}$, and nonnegativity of $p(a)$ allows multiplication by $p(a)$ without reversing the inequality. Summing over outcomes yields $\sum_a p(a)^2\le 2^{-k}\sum_a p(a)$. The probabilities sum to one, so the right side is $2^{-k}$.
