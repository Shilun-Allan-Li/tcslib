<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.incrementTM_run_overflow_ofCfg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Overflow Run from a Configuration

**Claim.** Under the stated tape-agreement and run-phase hypotheses, overflow leads from an arbitrary configuration to the done phase with false verdict after exactly $2|w|+2$ steps, with no earlier done phase and with the stated head-position bounds.

**Proof.** First decompose $w$ into a run of $p$ true bits followed either by nothing or by a false bit and a remaining word (`catalog_increment_split`). The increment value on this decomposition (`catalog_increment_value`) shows that overflow is possible precisely in the empty-tail case: if a false bit is present, the result is defined, contradicting the overflow hypothesis. Thus $w$ is exactly $p$ true bits and its length is $p. The trace description (`catalog_increment_trace`) now gives the machine configuration at every time as an explicit forward-and-return trace with false verdict. Evaluating that trace at $2p+2$ yields the stated terminal configuration: the selected tape has been cleared across the word's interval, and the other cells retain their original values. At any earlier time, the trace is in its forward or return portion, so its state is not done. The same trace shows that the selected head stays between one cell left of its initial position and $p$ cells to its right, inclusive; each other head remains fixed. Replacing $p$ by $|w|$ gives all the claimed bounds.

**Key facts.** `Turing.catalog_increment_split`, `Turing.catalog_increment_value`, `Turing.catalog_increment_trace`.
