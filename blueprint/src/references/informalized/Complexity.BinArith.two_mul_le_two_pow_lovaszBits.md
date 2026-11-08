<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/PrimeFind.lean :: Complexity.BinArith.two_mul_le_two_pow_lovaszBits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Power Bound for the Lovász Bit Count

**Claim.** For every natural number $n$, if $L=\lceil\log_2(2n)\rceil$ in the natural-number convention, then $2n\le 2^L$.

**Proof.** By the defining lower-bound property of the natural logarithm ceiling, for a base greater than one and a natural number argument, the argument is at most the base raised to its ceiling logarithm. Apply this with base $2$ and argument $2n$; since $L=\operatorname{clog}_2(2n)$, this gives $2n\le 2^L$.
