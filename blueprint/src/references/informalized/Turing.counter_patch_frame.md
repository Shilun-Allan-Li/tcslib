<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean :: Turing.counter_patch_frame -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counter Patch on the Frame

**Claim.** If $v$ and $w$ have equal lengths and $ct$ agrees with the buffered tape for $w$ throughout the stated range, then patching $ct$ with $v$ gives the buffered tape for $v$ throughout the corresponding range.

**Proof.** Fix a position $p$ in the required range. If $p$ lies within the word, the patch selects the buffered tape for $v$ directly. Otherwise, the bounds force $p$ to be one of the two boundary positions: $-1$ or the word length. At $-1$, the buffered tape is empty, and the assumed agreement identifies the original tape value there. At the right boundary, the equal lengths identify the boundary positions for $v$ and $w$; the assumed agreement and the buffered-tape value at the word length give the desired equality.

**Key facts.** `Turing.FinTM.bufferTape_left`, `Turing.FinTM.bufferTape_nat`.
