<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean :: Complexity.pairEncode_ne_nil -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonemptiness of a Pair Encoding

**Claim.** The pair encoding of any two binary strings is nonempty.

**Proof.** Its length is $2|x|+2+|y|$ (`Turing.length_pairEncode`), which is positive because it includes the two separator bits. An empty list has length zero, so the pair encoding cannot be empty.

**Key facts.** `Turing.length_pairEncode`.
