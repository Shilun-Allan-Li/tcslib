<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.drop_len -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length Oracle on Encoded Input

**Claim.** For every bit string $h$ and natural number $i$, the length oracle on the encoded pair of $h$ and the binary word for $i$ returns true exactly when $i<|h|$.

**Proof.** At index $1$, the oracle bank selects the input-length language. Its indicator on an encoded pair is exactly the decision of whether the index is smaller than the first component's length (`Complexity.indicator_inputLenLang`). This is the desired equality.

**Key facts.** `Complexity.indicator_inputLenLang`.
