<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.copyTM_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Copying Machine Run

**Claim.** For a Boolean tape family with empty destination tape, the copying machine reaches its done state with the source word copied to the destination within $3|w_{\mathrm{src}}|+3$ steps, and is not done at any earlier time.

**Proof.** Apply the general copying-run result to the initial configuration determined by the tape words and to the source word $w_{\mathrm{src}}$. Its hypotheses hold because the initial state is sweep and the source tape agrees with the word-buffer representation at every relevant offset. It gives completion after $T=2|w_{\mathrm{src}}|+2$ steps, no earlier visit to the done state, and a destination tape containing the copied word in the described interval. The assumed destination word is empty, so its initial buffer is nowhere defined; hence this interval update agrees at every cell with the buffer representation of the full source word, while all cells outside the interval retain the original blank destination. The other tapes retain their original contents, so componentwise configuration equality gives the claimed final configuration. Finally, $2|w_{\mathrm{src}}|+2\le 3|w_{\mathrm{src}}|+3$.

**Key facts.** `Turing.copyTM_run_ofCfg`, `Turing.FinTM.bufferTape_nil`.
