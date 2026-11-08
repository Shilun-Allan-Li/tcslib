<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/Cells.lean :: Light.Compiler.Sizes.inRange_neg_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Negative one lies in the word range

**Claim.** For every size configuration, $-1$ lies in the signed word range.

**Proof.** The offset bound implies that the dispatcher position is at least $2$: since the number of locals is nonnegative, twice one plus that number is at least $2$, and the dispatcher is at least this quantity. The pool-fit inequality therefore gives $4<2^W$. In particular, $2^W$ is at least $4$, so $-2^W\le -2$; also $-2<2^W$. These are precisely the two bounds required for $-1$ to lie in the signed word range.
