<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.drop_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Logarithmic Space for Drop Languages

**Claim.** For either mode, the language that tests the transformed word's length or a bit of that word is decidable in logarithmic space.

**Proof.** Both oracle languages used by the machine are in logarithmic space: the bit language and the length language have their respective membership results (`Complexity.inputBitLang_mem`, `Complexity.inputLenLang_mem`). Since the oracle bank has only these two entries, every oracle language required by the machine is in logarithmic space. The general theorem for alternating register machines with polynomially bounded registers therefore applies to the machine, using the stated run from its initial length-test state to the indicator of the drop language (`Complexity.LogProg.arm_decides_poly`, `Complexity.drop_run`). The run's register bound is of the form required by that theorem: the established bound $4(|h|+1)$ is at most $4(|h|+1)^1$. Finally, the halting result remains valid when its safety predicate is weakened to the one required by the general theorem (`Complexity.LogProg.AHalt.mono`).

**Key facts.** `Complexity.inputBitLang_mem`, `Complexity.inputLenLang_mem`, `Complexity.LogProg.arm_decides_poly`, `Complexity.drop_run`, `Complexity.LogProg.AHalt.mono`.
