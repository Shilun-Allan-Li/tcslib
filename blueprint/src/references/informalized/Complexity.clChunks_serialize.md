<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clChunks_serialize -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Chunks Serialize the Concatenated Formula

**Claim.** Concatenating the chunks at indices $0,\ldots,R$ gives the full serialization of the concatenation of the formulas at those indices.

**Proof.** Separate the final index $R$ from the preceding indices. By the preceding-chunks identity (`Complexity.clChunks_before`), the earlier chunks concatenate to the fragment of the earlier formulas. The last chunk contributes the fragment of $G(R)$ followed by the final separator, because its index is $R$. Concatenating these fragments gives the fragment of the full concatenated formula, followed by that separator; this is exactly its serialization.

**Key facts.** `Complexity.clChunks_before`.
