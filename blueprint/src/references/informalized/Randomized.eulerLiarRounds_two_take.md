<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PrimalityMath.lean :: Randomized.eulerLiarRounds_two_take -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Two Euler-liar rounds use only two blocks

**Claim.** For every $N$, block length $\ell$, and binary string $r$, two Euler-liar rounds give the same result on $r$ and on its prefix of length $2\ell$.

**Proof.** Expand the two-round recursion on both strings. The first round reads the first $\ell$ bits; taking the prefix of length $2\ell$ does not change that block. The recursive round then reads the next $\ell$ bits. The list identities for taking a prefix of a prefix and dropping the first block show these are also unchanged by the original truncation. Thus both round tests, and consequently their conjunction, agree.
