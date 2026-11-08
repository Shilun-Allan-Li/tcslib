<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomBits.lean :: Randomized.randProb_bitsVal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Probability of a Binary-Value Property

**Claim.** The probability that the value of a uniformly random Boolean string of length $L$ satisfies $P$ equals the number of values below $2^L$ satisfying $P$, divided by $2^L$.

**Proof.** Unfold the probability as the number of length-$L$ Boolean strings satisfying the property, divided by $2^L$. Map each such string to its binary value. The bound on binary values (`Complexity.LogProg.bitsVal_lt_two_pow`) shows that every image lies in the range from $0$ through $2^L-1$. This map is injective: the binary-value equivalence (`Randomized.bitsEquiv_apply`) identifies the value with the image under an equivalence between length-$L$ Boolean strings and numbers in that range, so equal values give equal strings. It is also surjective onto the values in the range satisfying $P$: apply the inverse equivalence to any such value; its associated string has that value, again by `Randomized.bitsEquiv_apply`, and therefore satisfies the required predicate. Hence the two finite sets have the same cardinality, giving the stated probability formula.

**Key facts.** `Complexity.LogProg.bitsVal_lt_two_pow`, `Randomized.bitsEquiv_apply`.
