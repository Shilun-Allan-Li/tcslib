<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean :: Turing.universal_install_marker -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Installing a Tape Marker

**Claim.** For either bit $b$, the tape blank except for $b$ at cell $0$ is the buffer tape storing the one-bit word $b$.

**Proof.** Apply the buffer-tape append identity (Turing.FinTM.bufferTape_append) to the empty word followed by $b$. The empty buffer tape is blank everywhere, and the appended symbol is installed at position $|[]|=0$. Since $[]++[b]=[b]$, reversing the identity gives exactly the claimed equality.

**Key facts.** `Turing.FinTM.bufferTape_append`.
