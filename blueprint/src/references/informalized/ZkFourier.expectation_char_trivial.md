<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/ZkFourier.lean :: ZkFourier.expectation_char_trivial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mean of the Trivial Character

**Claim.** The Fourier character indexed by the zero vector has uniform expectation equal to $1$.

**Proof.** By the definition of expectation, it suffices to show that the sum of the trivial character over all vectors equals the denominator $k^n$. The character indexed by zero is identically $1$, so its sum is the number of vectors in $(\mathbb{Z}/k\mathbb{Z})^n$. That number is $k^n$ (`card_ZkVec`), and the quotient is therefore $1$.

**Key facts.** `ZkFourier.card_ZkVec`.
