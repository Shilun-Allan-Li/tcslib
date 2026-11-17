<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Word.lean :: Complexity.Codec.bitsVal_padBits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value of a Padded Binary Expansion

**Claim.** For all natural numbers $w$ and $v$, the binary value of the binary expansion of $v$ followed by enough false bits to meet the prescribed padding length $w$ is exactly $v$.

**Proof.** The padded word is the binary expansion of $v$ followed by a list of false entries. Appending false entries preserves binary value (`bitsVal_append_replicate`), and the binary expansion of $v$ has value $v` (`bitsVal_bits`). Therefore the padded word has value $v$.

**Key facts.** `Complexity.Codec.bitsVal_append_replicate`, `Complexity.LogProg.bitsVal_bits`.
