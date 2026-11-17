<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauSpec.lean :: Complexity.UTab.padS_toBitSrc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Padding and Source Translation

**Claim.** Translating a list padded with false constants gives the translated original list followed by the corresponding number of false constants.

**Proof.** Map the source translation over the concatenation defining the padded list. Mapping distributes over concatenation, and mapping a constant function over a replicated list preserves its length and replicates the translated value. The translation of the false constant is the false bit constant. Finally, the original list and its image under translation have the same length, so the padding count on the right is the same as the one in the definition of the padded list.
