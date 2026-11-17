<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UniversalStartup.lean :: Turing.universal_marker -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Marker Tape Contents

**Claim.** At natural-number cell $p$, the buffer tape storing the one-bit word $1$ contains $1$ if $p=0$ and is blank otherwise.

**Proof.** For a natural-number position, the buffer tape reads the corresponding list entry (Turing.FinTM.bufferTape_nat). The one-bit list $[1]$ has entry $1$ at index zero and no entry at any positive index, yielding the stated cases.

**Key facts.** `Turing.FinTM.bufferTape_nat`.
