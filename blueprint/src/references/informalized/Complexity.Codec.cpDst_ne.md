<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Run.lean :: Complexity.Codec.cpDst_ne -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Distinct Copy Registers

**Claim.** For every instruction label, its destination and source register indices are distinct.

**Proof.** Exhaust the finitely many instruction labels. In each case the destination and source are the specified concrete register indices, and direct comparison shows that the two indices differ.
