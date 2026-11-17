<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/ZkFourier.lean :: ZkFourier.char_s_ne_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Characters are nonzero

**Claim.** Every Fourier character is nonzero at every vector.

**Proof.** Each character value has complex modulus $1$ (`ZkFourier.norm_char_s`). If a character value were zero, its modulus would be zero, contradicting that it equals $1$.

**Key facts.** `ZkFourier.norm_char_s`.
