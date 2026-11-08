<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomBits.lean :: Randomized.blockVal_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on a Block Value

**Claim.** For natural numbers $b,i$ and a finite bit string $r$, the integer represented by the length-at-most-$b$ block of $r$ beginning at position $ib$ is strictly less than $2^b$.

**Proof.** The value of any bit string $w$ is strictly less than $2^{|w|}$ (`Complexity.LogProg.bitsVal_lt_two_pow`). The selected block is obtained by taking at most $b$ bits, so its length is at most $b$. Since powers of two are increasing in their natural-number exponent, its value is therefore less than or equal to a quantity strictly below $2^b$, and hence is strictly less than $2^b$.

**Key facts.** `Complexity.LogProg.bitsVal_lt_two_pow`.
