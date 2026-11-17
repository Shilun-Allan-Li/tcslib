<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Words.lean :: Complexity.BinArith.length_iterate_pairSndD_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length under iterated decoding

**Claim.** For every finite bit string $w$ and natural number $i$, iterating the total second projection $i$ times produces a string of length at most $|w|$.

**Proof.** Induct on $i$. At $i=0$, the iterate is $w$ itself, so the lengths agree. For the successor step, the iterate is obtained by first applying the total second projection to $w$ and then iterating it $i$ more times. The one-step length bound (`Complexity.length_pairSndD_le`) says that this first application does not increase length; the induction hypothesis bounds the remaining iterates by the length of its input. Combining the two inequalities proves the claim.

**Key facts.** `Complexity.length_pairSndD_le`.
