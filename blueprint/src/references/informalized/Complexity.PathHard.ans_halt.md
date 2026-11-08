<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHardMachine.lean :: Complexity.PathHard.ans_halt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halting from an answer state

**Claim.** If all fifteen register values are at most $B$, the machine started in the answer state labeled by $r$, with register vector given by the state and no recorded result, halts with result $r$ and satisfies the guard at every earlier time.

**Proof.** The answer state labeled by $r$ executes the instruction that returns $r$. The register bound implies that the starting configuration satisfies the guard (`gb_of`). The one-step return principle for `AHalt` (`AHalt.ret`) then gives halting with result $r$ and verifies the guard at every earlier time.

**Key facts.** `Complexity.PathHard.gb_of`, `Complexity.LogProg.AHalt.ret`.
