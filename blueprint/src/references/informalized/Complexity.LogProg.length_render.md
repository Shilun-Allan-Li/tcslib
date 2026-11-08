<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Layout.lean :: Complexity.LogProg.length_render -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rendered segment length

**Claim.** For a segment consisting of a bit string $w$ and a flag indicating whether it is doubled, its rendered length is $2|w|$ when the flag is true and $|w|$ otherwise.

**Proof.** Unfold the definitions of rendering and rendered length, and split according to the flag. When it is false, rendering leaves $w$ unchanged, so the lengths agree. When it is true, rendering replaces each bit by two copies; the length of this flattened list is twice the length of $w$.
