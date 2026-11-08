<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.MachineFormat.exists_canonSeekOnBank -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Canonical Seek on a Tape Bank

**Claim.** For every format, number of work tapes, and injection of a two-tape machine's tapes into that bank, there is a finite-state machine on the bank that performs the specified input-head seek while preserving the configuration, within the stated bound and with no earlier visit to its exit state.

**Proof.** Use the two-tape input-seek machine from `Turing.exists_inputSeekTM`, which reaches input position $p$ while preserving the rest of its configuration and has no earlier visit to its exit. Extract the two selected tapes from the given bank configuration to form a two-tape configuration with the same state, input-head position, and output. The word and blank-tape hypotheses transfer directly to these selected tapes, so the input-seek result applies. Run the bank machine obtained by embedding the two-tape machine along $\iota$. The equality `Turing.canonEmbedEq` identifies the embedded starting configuration with the given bank configuration, and `Turing.embedEmitTM_runFrom` transports the entire run step by step, so the first-arrival bound is unchanged. At the final time, `canonEmbedEq` again identifies the embedded result with the original configuration having only its state changed to the exit state and its input head moved to $p$; every tape, tape-head position, and output is preserved. The integer-position bounds on the represented word and the blankness of the second selected tape are exactly the hypotheses needed by the two-tape seek result; the constraint $p\le |x|+1$ supplies its allowed target range.

**Key facts.** `Turing.exists_inputSeekTM`, `Turing.canonEmbedEq`, `Turing.embedEmitTM_runFrom`.
