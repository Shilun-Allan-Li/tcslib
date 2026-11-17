<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Basic.lean :: Complexity.BinArith.iterate_drop_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Repeated deletion of initial bits

**Claim.** For every bit string $w$ and natural number $i$, deleting the first bit repeatedly $i$ times gives the suffix of $w$ obtained by deleting its first $i$ bits.

**Proof.** Induct on $i$. At $i=0$, neither operation changes $w$. For the successor case, one more application of the function removes the first bit from the result at stage $i$. By the induction hypothesis that result is $w$ with its first $i$ bits deleted, and deleting one more bit is the same as deleting $i+1$ bits in total. Thus the two lists agree.
