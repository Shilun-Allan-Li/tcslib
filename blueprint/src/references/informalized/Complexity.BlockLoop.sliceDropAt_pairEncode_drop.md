<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimeBlockLoop.lean :: Complexity.BlockLoop.sliceDropAt_pairEncode_drop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dropping a Successive Encoded Slice

**Claim.** If $L=a(|x|+1)^k$, then applying the slice-drop operation to the encoding of $x$ paired with $u$ after dropping its first $iL$ bits yields the encoding of $x$ paired with $u$ after dropping its first $(i+1)L$ bits.

**Proof.** Decode the encoded pair and re-encode it after dropping the prescribed number of bits from its second component. The decoding identities for encoded pairs (`pairFstD_pairEncode` and `pairSndD_pairEncode`) show that the first component remains $x$ and the second is $u$ with its first $iL$ bits removed. Dropping another $L$ bits from that suffix is the same as dropping $iL+L=(i+1)L$ bits from $u$ (`List.drop_drop`); the equality of the indices is the elementary arithmetic identity $iL+L=(i+1)L$.

**Key facts.** `Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`.
