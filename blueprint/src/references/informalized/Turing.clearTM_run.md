<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.clearTM_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clearing from an initialized configuration

**Claim.** For the chosen tape and initial words, the clearing machine reaches the done state within $2|w_i|+2$ steps, is not done earlier, and at that time its configuration is the initial one with tape $i$ empty.

**Proof.** Apply the configuration-level clearing theorem (`clearTM_run_ofCfg`) to the initial configuration. Its hypotheses hold because the initial state is sweep and the tape contents at offsets from the head agree with the buffered word. It gives the exact run time $T=2|w_i|+2$, the fact that done is not reached earlier, and the final configuration with every cell in the interval occupied by the word blanked. To identify this final configuration with the initial configuration formed from the updated word, compare configuration fields: the state, head positions, input position, and output agree, and the tape functions agree because the updated word is empty on tape $i$ and leaves every other tape unchanged. The empty buffer contains no symbols (`Turing.FinTM.bufferTape_nil`).

**Key facts.** `Turing.clearTM_run_ofCfg`, `Turing.FinTM.bufferTape_nil`.
