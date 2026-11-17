<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimeBlockLoop.lean :: Complexity.BlockLoop.sliceTakeAt_pairEncode_drop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Taking a Slice After an Encoded Drop

**Claim.** If $L=a(|x|+1)^k$, applying the slice-take operation to the encoding of $x$ paired with the suffix of $u$ after its first $iL$ bits yields the encoding of $x$ paired with the first $L$ bits of that suffix.

**Proof.** The slice-take operation decodes the pair, takes the prescribed number of bits from its second component, and re-encodes the result. The decoding identities (`pairFstD_pairEncode` and `pairSndD_pairEncode`) show that the decoded components are $x$ and the suffix of $u$ after its first $iL$ bits. Taking the first $L$ bits of that suffix gives exactly the claimed encoding.

**Key facts.** `Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`.
