<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PolyTimeModel.lean :: Randomized.polyTimeComputable_takePrefixByLen -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Prefix Extraction

**Claim.** The function sending a bit string $p$ to the prefix of its decoded second component whose length is the length of its decoded first component is polynomial-time computable; failed decoding yields empty components.

**Proof.** The function is precisely the length-indexed prefix operation on the decoded pair: it returns the second component truncated to the length of the first. The polynomial-time result for prefix extraction by component length (Complexity.polyTimeComputable_takePrefixByLength) applies directly. Unfolding the definition of the decoded prefix function identifies it with that operation, so the same polynomial-time computation proves the claim.

**Key facts.** `Complexity.polyTimeComputable_takePrefixByLength`.
