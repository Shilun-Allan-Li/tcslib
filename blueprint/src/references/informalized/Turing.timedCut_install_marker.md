<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timedCut_install_marker -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Installing a Marker on a Blank Tape

**Claim.** Writing either Boolean symbol $b$ at cell $0$ of an everywhere-blank tape produces the tape encoding the one-symbol word $[b]$.

**Proof.** The tape-append identity (`bufferTape_append`) says that appending $b$ to the empty word updates its blank tape at position $0$ with value `some b`. The tape of the empty word is everywhere blank, so this update is exactly the stated function; reversing the identity gives the claimed equality.

**Key facts.** `Turing.FinTM.bufferTape_append`.
