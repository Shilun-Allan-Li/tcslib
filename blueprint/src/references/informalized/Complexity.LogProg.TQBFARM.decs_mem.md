<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFARM/Machine.lean :: Complexity.LogProg.TQBFARM.decs_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Logarithmic-Space Decidability of the Index Languages

**Claim.** Both index languages—the one testing whether the indexed bit is true, with a missing bit treated as false, and the one testing whether the index is less than the word length—are decidable in logarithmic space.

**Proof.** There are two possible indices for the decider family. At the first index, the language is the input-bit language, which is in logarithmic space (`Complexity.inputBitLang_mem`). At the second, it is the input-length language, which is also in logarithmic space (`Complexity.inputLenLang_mem`). These cases establish the claim for every index.

**Key facts.** `Complexity.inputBitLang_mem`, `Complexity.inputLenLang_mem`.
