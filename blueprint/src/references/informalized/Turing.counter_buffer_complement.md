<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean :: Turing.counter_buffer_complement -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complementing a Buffered Word

**Claim.** For every Boolean word $w$ and integer cell position $p$, the tape storing the bitwise complement of $w$ at $p$ contains the complement of the symbol stored by the tape for $w$ at $p$, with a blank remaining blank.

**Proof.** Apply the general fact that mapping an embedding over a word commutes with reading the corresponding buffered tape cell. Take the embedding to be Boolean negation. The resulting identity says exactly that the buffered tape for the complemented word is obtained by mapping negation over the original cell value; since mapping a function over an optional value preserves absence, blank cells remain blank.

**Key facts.** `Turing.FinTM.bufferTape_map`.
