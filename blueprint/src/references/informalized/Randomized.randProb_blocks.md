<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomBits.lean :: Randomized.randProb_blocks -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Probability of a Block Predicate

**Claim.** The probability that the block values of a uniform Boolean word of length $nb$ satisfy $P$ equals the number of functions from the $n$ block positions to $\{0,\ldots,2^b-1\}$ satisfying $P$, divided by $(2^b)^n$.

**Proof.** Unfold the probability and use $(2^b)^n=2^{bn}=2^{nb}$ to put its denominator in the stated form. The equivalence `blocksEquiv n b` identifies a Boolean word of length $nb$ with its function of $n$ block values, each represented by an element of $\{0,\ldots,2^b-1\}$. Its value at each position agrees with the value of the corresponding block (`Randomized.blocksEquiv_apply`). Consequently this equivalence restricts to a bijection between words whose block values satisfy $P$ and functions satisfying $P$. The corresponding finite sets have equal cardinalities, which proves the formula.

**Key facts.** `Randomized.blocksEquiv_apply`.
