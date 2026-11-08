<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CounterProgInput.lean :: Complexity.CounterProg.step_shiftInput -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input Prefix Shift Compatibility

**Claim.** Taking one step on the concatenation of a prefix and suffix from a state whose read position is shifted by the prefix length agrees with taking one step on the suffix and shifting the resulting state by that length.

**Proof.** If the state is halted, both sides are unchanged. At an active label, instructions other than reading do not depend on the input string or read position, so the same state update occurs on both sides. For a read instruction, the list-index identity $(\mathrm{pre}++\mathrm{suffix})[|\mathrm{pre}|+p]?=\mathrm{suffix}[p]? $ (`getElem?_append_length_add`) says that the symbol observed after the shifted prefix is exactly the symbol at position $p$ in the suffix. If no symbol is present, both executions take the end-of-input branch and keep their respective read positions; if a bit is present, both choose the same bit-dependent branch and advance the position by one. Hence the resulting states agree, including their shifted positions.

**Key facts.** `Complexity.CounterProg.getElem?_append_length_add`.
