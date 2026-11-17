<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Word.lean :: Complexity.Codec.bitsVal_append_replicate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Appending Zero Bits Preserves Value

**Claim.** For every finite Boolean list $w$ and natural number $z$, appending $z$ false entries to $w$ leaves its binary value unchanged.

**Proof.** Induct on the list. For a nonempty list, the binary value is its first bit's value plus twice the value of the tail; applying the induction hypothesis to the tail shows that appending false entries does not change this expression. For the empty list, induct on the number of appended entries: the value remains zero, since each new leading false bit contributes zero and twice the value of the remaining false list is still zero.
