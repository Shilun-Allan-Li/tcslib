<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevin/PrefixBuckets.lean :: FABL.freeFrequencyPart_prefixFrequency -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Free Part of a Prefix Frequency Set

**Claim.** The part inside the first $k$ coordinates of the prefix of $U$ equals the part of $U$ inside those coordinates.

**Proof.** Compare membership for an arbitrary coordinate of the first $k$ coordinates. Its membership in the free part is equivalent to membership in the frequency set being restricted. Because the coordinate is already less than $k$, filtering $U$ to coordinates less than $k$ does not change whether it belongs to $U$. Hence the two free parts agree.

**Key facts.** `FABL.mem_freeFrequencyPart`.
