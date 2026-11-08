<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimeBlockLoop.lean :: Complexity.xorPair_output -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output of the Pairwise XOR Process

**Claim.** If the shorter of $p$ and $u$ has length at most $N$, then concatenating the pair-output rule's outputs on the encodings of the suffixes obtained by dropping $i$ bits, for $0\le i<N$, gives the bitwise XOR of $p$ and $u$.

**Proof.** Induct on $N$. When $N=0$, the length condition forces at least one of the strings to be empty. The pair-output rule then returns nothing at every suffix, and the bitwise XOR is also empty. For the successor step, if either string is empty, the same empty-component fact makes every output empty, as is the zipped XOR. Otherwise write the strings as $b::p$ and $c::u$. The term for $i=0$ emits the single bit $b\mathbin{\mathrm{xor}}c$, by the leading-bit rule. The remaining terms, indexed by the first $N$ positions, are exactly the process applied to $p$ and $u$: dropping $i+1$ bits from the original strings is dropping $i$ bits from their tails. The shorter-tail length is at most $N$ by the original bound, so the induction hypothesis identifies these remaining outputs with the zipped XOR of the tails. Prepending the first XOR bit gives the zipped XOR of the original strings.

**Key facts.** `Complexity.xorPairEmit_nil`, `Complexity.xorPairEmit_cons`.
