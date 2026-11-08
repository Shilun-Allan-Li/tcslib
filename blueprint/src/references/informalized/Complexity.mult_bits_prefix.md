<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/Mult.lean :: Complexity.mult_bits_prefix -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value of a Finite Bit Prefix

**Claim.** For every bit string $w$ and natural number $n$, the weighted sum of its bits in positions below $n$, with weights $2^j$, equals the value of the length-$n$ prefix, with missing bits treated as zero.

**Proof.** Proceed by induction on $n$, allowing the bit string to vary in the induction hypothesis. For $n=0$, both the empty sum and the value of the empty prefix are zero. For the successor step, separate the last summand of the sum. If $w$ is empty, all accessed bits and the prefix value are zero. Otherwise write $w=t::w'$. The prefix of length $n+1$ consists of $t$ followed by the length-$n$ prefix of $w'$, so its value is $t.toNat+2\operatorname{bitsVal}(w'.take\ n)$. The remaining weighted sum is twice the corresponding sum for $w'$ of length $n$; applying the induction hypothesis identifies it with twice that prefix value. Adding the contribution $t.toNat$ proves the identity.
