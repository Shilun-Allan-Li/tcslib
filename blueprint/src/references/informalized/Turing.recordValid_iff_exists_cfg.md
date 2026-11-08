<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/RecordTable.lean :: Turing.recordValid_iff_exists_cfg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Valid Records on a Fixed Input

**Claim.** For a fixed Boolean input $x$, a list is valid for parameters $k$, $|x|$, and $s$ exactly when it is the record of a configuration on that very input, with some tag, whose work-tape heads and nonblank cells lie in the window of radius $s$.

**Proof.** For the forward direction, validity supplies an input $y$, a configuration on $y$, and a tag, with $|y|=|x|$. Reinterpret the same configuration data on input $x$: the input-head position remains in range because the two input lengths agree, and all work-tape data, state, and output are unchanged. The record depends on the input length and configuration data, so this new configuration has the same record and retains the window condition. Conversely, a configuration on $x$ with the stated window condition and record equality witnesses validity directly, using $x$ itself as the input.
