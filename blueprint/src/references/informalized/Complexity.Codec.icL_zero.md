<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Run.lean :: Complexity.Codec.icL_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Increment Label

**Claim.** For any increment-count identifier $c$, the label assigned at index zero is the indexed increment label with index zero.

**Proof.** For each of the five identifiers, its associated increment count is positive: the counts are either $2W$, $4$, or $2(H+2)$, with $W\ge1$ and $H\ge0$. Hence index zero lies within the indexed increment range. By the definition of the label assignment, the index-zero label is therefore the indexed increment label at zero.

**Key facts.** `Complexity.Codec.icCount_le`.
