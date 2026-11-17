<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceTableauFront.lean :: Complexity.UTab.Front.goes_nil -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero-step Run at the Same State

**Claim.** For any label, register assignment, input position, and previously printed output, the program has a run of at most zero steps that stays at that label with the same registers and input position and appends no output.

**Proof.** For each prior output string, choose a run of length zero. The zero-iteration run is the identity on the entire state (`run_zero`), so it preserves the label, registers, input position, and output. Its length is at most zero, as required.

**Key facts.** `Complexity.CounterProg.run_zero`.
