<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Run.lean :: Complexity.Codec.codecAs_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Log-Space Decidability of Codec Languages

**Claim.** For each index $j$ in the two-element type, the language selected by the codec map belongs to LOGSPACE.

**Proof.** Split on the two possible values of $j$. At $j=0$, the codec selects the language testing whether the indexed position lies within the first string's length, which is in LOGSPACE by `inputLenLang_mem`. At $j=1$, it selects the language testing whether the indexed bit is true, which is in LOGSPACE by `inputBitLang_mem`. These two cases establish the claim for every index.

**Key facts.** `Complexity.inputLenLang_mem`, `Complexity.inputBitLang_mem`.
