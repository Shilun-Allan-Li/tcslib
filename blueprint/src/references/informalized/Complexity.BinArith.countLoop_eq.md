<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/PrimeFind.lean :: Complexity.BinArith.countLoop_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counting loop output

**Claim.** For every bit string $z$, iterating the counting step $|z|+1$ times from the encoding of the empty word and $z$ yields the encoding of the binary bit list of $|z|$ and the empty word.

**Proof.** The initial state satisfies the counting invariant: its accumulator is empty, its value is zero, and the remainder has length $|z|$. By `countInv_step`, each iteration preserves the invariant, decreases the remainder length whenever that length is positive, and fixes a state once the remainder is empty. Since the initial remainder length is at most $|z|+1$, `iterate_measure_eq_zero` shows that after the prescribed iterations its length is zero. The invariant after those iterations (`iterate_invariant`) still holds. Thus the accumulator value is $|z|$, because its value plus the now-zero remainder length equals $|z|$; the invariant also says that the accumulator is the binary bit list of its own value. The paired-encoding projection identifies the final second component as empty, yielding the claimed output.

**Key facts.** `Complexity.BinArith.countInv_step`, `Complexity.BinArith.iterate_invariant`, `Complexity.BinArith.iterate_measure_eq_zero`, `Complexity.pairSndD_pairEncode`.
