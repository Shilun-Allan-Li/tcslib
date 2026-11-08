<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimeBlockTests.lean :: Complexity.zipWith_xor_blockAt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# XOR with a Zero Block

**Claim.** The bitwise XOR of a zero word of length $m=a(|\pi_1(z)|+1)^k$ with the length-$m$ block beginning at position $im$ in the total second projection of $z$ equals that block.

**Proof.** Let the block be $l$ and its length bound be $n=m$. Prove the claim by induction on the block. For the empty block, both sides are empty. For a nonempty block $b::l'$, the length bound rules out $n=0$, so write $n=n'+1$. The first zero of the replicated word pairs with $b$ and gives $b$, since false XOR any bit is that bit. The remaining replicated zeros pair with $l'$. Its length is at most $n'$, so induction identifies the remaining zipped XOR with $l'$. Combining the first bit and this tail yields the block itself.
