<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomBits.lean :: Randomized.blockCount_add_not -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complementary Block Counts

**Claim.** For natural numbers $q,K$, a predicate $B$ on finite bit strings, and a finite bit string $l$, the number of the first $K$ consecutive length-$q$ blocks satisfying $B$ plus the number satisfying its negation is $K$.

**Proof.** Induct on $K$, allowing the bit string to vary. At $K=0$ both counts vanish. For the successor case, the recursive block-count formula separates the first block from the remaining $K$ blocks, which are counted in the string with its first $q$ bits dropped (`Randomized.blockCount_succ`). Apply this formula to both $B$ and its negation. The induction hypothesis says the two counts on the remaining string sum to $K$. The first block contributes exactly one across the two counts: either it satisfies $B$ or its negation does. Adding these contributions gives $K+1$.

**Key facts.** `Randomized.blockCount_succ`.
