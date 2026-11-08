<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PolyTimeModel.lean :: Randomized.polyTimeComputable_dropPrefixByLen -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Prefix Removal

**Claim.** The function that decodes a pair, takes its second component, and drops as many bits as the first component's length is polynomial-time computable, using empty strings when decoding fails.

**Proof.** The defined prefix-removal function is exactly the second-component drop operation in the general prefix-by-length construction: its input supplies the pair whose first-component length determines how many bits to remove from the second component. The general theorem that this operation is polynomial-time computable therefore applies directly.

**Key facts.** `Complexity.polyTimeComputable_dropPrefixByLength`.
