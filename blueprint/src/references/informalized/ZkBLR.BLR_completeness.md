<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/ZkBLR.lean :: ZkBLR.BLR_completeness -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Completeness of the BLR test

**Claim.** If $f$ is additive, then the BLR test accepts every pair and its acceptance probability is $1$.

**Proof.** By additivity, for every pair $(x,y)$ the equality $f(x+y)=f(x)+f(y)$ holds, so every summand in the acceptance count is $1$. The vector space has $k^n$ elements (`ZkFourier.card_ZkVec`), hence there are $(k^n)^2$ ordered pairs. Dividing the count by this number gives acceptance probability $1$.

**Key facts.** `ZkFourier.card_ZkVec`.
