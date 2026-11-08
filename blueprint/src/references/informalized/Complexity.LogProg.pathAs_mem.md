<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathWalkMachine.lean :: Complexity.LogProg.pathAs_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Path language space bound

**Claim.** For either choice of $j\in\{0,1\}$, the corresponding path language belongs to logarithmic space.

**Proof.** The type $\mathrm{Fin}\,2$ has two cases. At $j=0$, the path language is the indexed bit-test language, which is in logarithmic space by the fact that the bit-test language is in $\mathrm{LOGSPACE}$ (`Complexity.inputBitLang_mem`). At $j=1$, it is the indexed length-test language, which is in $\mathrm{LOGSPACE}$ by the corresponding result for that language (`Complexity.inputLenLang_mem`).

**Key facts.** `Complexity.inputBitLang_mem`, `Complexity.inputLenLang_mem`.
