<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomBits.lean :: Randomized.randProb_blocks_piFinset -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Probability of a Predicate on Blocks

**Claim.** The probability that the block values of a uniform Boolean word of length $nb$ satisfy $P$ equals the number of functions to $\{0,\ldots,2^b-1\}$ satisfying $P$, divided by $2^{nb}$.

**Proof.** First apply the block-value counting formula (`Randomized.randProb_blocks`), which expresses the probability as the number of satisfying functions into the finite type of values below $2^b$, divided by $(2^b)^n$. Since $(2^b)^n=2^{nb}$, this is the desired denominator. To express the numerator as a finset of natural-valued functions, map each function into the finite type to the same function viewed as natural numbers. The values lie in the required range by construction. This map is injective because equality of natural-valued functions implies equality at every position, and hence equality in each finite type. It is surjective onto the functions whose values lie in the range and which satisfy $P$: for such a function, regard each value as an element of the corresponding finite type; the resulting function still satisfies $P$. Thus the two counted sets have equal cardinality, yielding the claim.

**Key facts.** `Randomized.randProb_blocks`.
