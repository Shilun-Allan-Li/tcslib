<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean :: Complexity.dataCfg_finish -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halt on an Exhausted Counter

**Claim.** If the unary tape has no unit marker at the unary head, then one simulator step from the macrostep-check phase halts and outputs the single symbol carrying the saved answer bit.

**Proof.** The schedule transition at the macrostep-check phase checks the unary symbol at the head. The hypothesis rules out a unit marker, so the schedule enters its halting state. In the same case, the data visit leaves the stored data unchanged and emits the saved bit as its output symbol. The decorated transition therefore has no successor state, and appending that one symbol to the initially empty output gives exactly $[\mathrm{bit}(d.2.1)]$.

**Key facts.** `Complexity.dataCfg_step`, `Complexity.macroCfg_check`, `Complexity.macroCfg_unary`.
