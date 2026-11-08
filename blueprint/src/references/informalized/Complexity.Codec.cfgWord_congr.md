<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Word.lean :: Complexity.Codec.cfgWord_congr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Configuration Word Congruence

**Claim.** If two configurations have the same core data and the same output summary, then their encoded configuration words are equal.

**Proof.** The equality of the core-and-summary pairs gives equality of their input-head positions by projecting to the input-position component. The configurations also have equal cell descriptions at every position, by the cell-congruence fact (`cellOf_congr`). Thus the concatenated chunk encodings agree, and the padded input-position segments agree as well. The final marker bit is fixed, so all parts of the configuration words coincide.

**Key facts.** `Complexity.Codec.cellOf_congr`.
