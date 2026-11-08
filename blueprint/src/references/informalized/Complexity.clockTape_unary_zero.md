<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean :: Complexity.clockTape_unary_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Empty Clock and Unary Tapes

**Claim.** At every integer coordinate $z$, the captured clock tape of the empty bit word and the unary tape with zero markers have the same content.

**Proof.** Compare the tapes at an arbitrary coordinate. The empty word has blank buffer at every position, by the fact that buffering an empty list always returns blank (`Turing.FinTM.bufferTape_nil`). Consequently the captured clock tape contains the origin marker at $0$ and is blank elsewhere. The unary tape with zero markers has the same values: its marker interval $1\le z\le 0$ is empty, leaving only the origin marker at $0$.

**Key facts.** `Turing.FinTM.bufferTape_nil`.
