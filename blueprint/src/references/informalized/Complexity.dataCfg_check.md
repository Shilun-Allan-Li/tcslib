<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean :: Complexity.dataCfg_check -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counter Test with a Unit Marker

**Claim.** If the base unary tape has a unit marker at coordinate $u$, one simulator step from macrostep-check enters seek-left with unary head still at $u$ and guide head at $0$. The data register receives the source action's output when present (otherwise retaining its old answer), the decoded payloads at coordinate $0$ as reads, and blank neighbor registers. Each data tape is updated at coordinate $0$ according to the source action's optional write, and the output is unchanged.

**Proof.** Apply the decorated-machine step description (`dataCfg_step`). The macrostep-check schedule transition tests the unary-tape symbol at its head position; the hypothesis that this symbol is the unit marker makes it enter seek-left, while keeping the unary and guide heads at $u$ and $0$ (`macroCfg_check`). The unary-head interpretation identifies the tested symbol with the base tape at $u$ (`macroCfg_unary`). In this branch, the visitor constructs the source action from the old state and the current payloads decoded at coordinate $0$. It retains the old answer if the action has no output and otherwise uses that output; it stores those decoded payloads as the new reads and resets the neighbor registers to blank. For each data lane it applies the action's optional write at coordinate $0$, exactly as expressed by the setup-write operation in the conclusion. The visitor emits no output, so the output word is unchanged. Substitution into the step formula gives the result.

**Key facts.** `Complexity.dataCfg_step`, `Complexity.macroCfg_check`, `Complexity.macroCfg_unary`.
