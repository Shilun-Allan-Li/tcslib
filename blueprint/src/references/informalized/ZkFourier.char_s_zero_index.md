<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/ZkFourier.lean :: ZkFourier.char_s_zero_index -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero-index character

**Claim.** The character indexed by the zero vector is identically $1$.

**Proof.** The dot product of the zero frequency with any vector is zero (`ZkFourier.zkDot_zero_left`). The root-of-unity map takes zero to $1$ (`ZkFourier.toOmega_zero`), so the zero-index character has value $1$ at every vector.

**Key facts.** `ZkFourier.zkDot_zero_left`, `ZkFourier.toOmega_zero`.
