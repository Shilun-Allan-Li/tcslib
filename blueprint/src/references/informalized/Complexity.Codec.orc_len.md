<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Run.lean :: Complexity.Codec.orc_len -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length Oracle on Encoded Input

**Claim.** For every bit string $y$ and natural number $a$, the length oracle applied to the pair encoding of $y$ and the binary representation of $a$ returns true exactly when $a<|y|$.

**Proof.** At the length-oracle index, the chosen oracle language asks whether the queried index is strictly less than the length of the first component. Its indicator on the encoded pair is therefore the Boolean decision of $a<|y|$, by the length-oracle characterization (`indicator_inputLenLang`).

**Key facts.** `Complexity.indicator_inputLenLang`.
