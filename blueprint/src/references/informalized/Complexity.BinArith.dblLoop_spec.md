<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/PrimeFind.lean :: Complexity.BinArith.dblLoop_spec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First component after doubling

**Claim.** For every bit string $z$, the first decoded component after the doubling loop is $\lceil\log_2(2|z|)\rceil$ zero bits followed by one.

**Proof.** The initial state satisfies the doubling invariant with exponent $j=0$: the counting-loop result says the count is the binary representation of $|z|$, and the initial first component is `[true]`. The potential is at most the loop's iteration budget, since `lovaszBits_le` bounds the ceiling logarithm by $|z|+1$. The one-step result `dblInv_step` preserves the invariant, decreases the potential when it is positive, and fixes the state when it is zero. Consequently `iterate_measure_eq_zero` makes the potential zero after the loop, while `iterate_invariant` keeps the state in the invariant throughout. The invariant identifies the first component as $j$ zeros followed by one, so its length is $j+1$; zero potential therefore gives $j=\lceil\log_2(2|z|)\rceil$. Decoding the first component of the paired encoding yields the stated word.

**Key facts.** `Complexity.BinArith.countLoop_eq`, `Complexity.BinArith.dblInv_step`, `Complexity.BinArith.iterate_invariant`, `Complexity.BinArith.iterate_measure_eq_zero`, `Complexity.BinArith.lovaszBits_le`, `Complexity.pairFstD_pairEncode`.
