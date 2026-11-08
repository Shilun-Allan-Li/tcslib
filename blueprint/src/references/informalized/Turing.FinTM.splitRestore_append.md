<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.splitRestore_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cleanup scan completion

**Claim.** One cleanup step from the scan configuration at count $|s|$ reaches phase $(1,\mathrm{false})$, erases the scratch tapes, and appends a $1$ to $s$ exactly when $|s|\le |w|$.

**Proof.** At count $|s|$, the scratch-tape head is on the first blank cell, so the cleanup transition takes its blank-cell branch. If $|s|\le |w|$, the flag is false: the machine writes a $1$ at the end of the first tape and moves the heads left. The tape change is the append identity `bufferTape_append`; the scratch tape is erased at the scanned cell, and `splitScratch_erase` identifies the resulting scratch contents. If $|s|>|w|$, the flag is true: the machine leaves the first tape unchanged, moves the heads left, and erases the scanned scratch cell, again using `splitScratch_erase`. In both cases the input head stays fixed by `moveInputPos_zero`, the output stays empty, and the resulting tape and head positions are those of the cleanup configuration at displacement $|s|-1$.

**Key facts.** `Turing.moveInputPos_zero`, `Turing.FinTM.bufferTape_append`, `Turing.FinTM.splitScratch_erase`.
