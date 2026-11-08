<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Run.lean :: Complexity.Codec.scSrc_ne -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Distinct scan registers

**Claim.** For every scan identifier, the source register differs from its destination register.

**Proof.** The source is always register $13$. The six destinations, in order, are registers $7,8,9,10,14,14$. Each differs from $13$, so the source and destination are distinct in every case.
