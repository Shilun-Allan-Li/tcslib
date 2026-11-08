<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDClockHost.lean :: Turing.ClockHost.yard_of_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Contents of the Yardstick Tape

**Claim.** For every natural number $m$ and integer cell $z$, if $0\le z$ and $z<m$, then the yardstick tape of length $m$ contains the bit $1$ at cell $z$.

**Proof.** Since $z$ is nonnegative, write it as the natural number $n$. The yardstick tape is the buffer tape of a list consisting of $m$ copies of $1$; at a nonnegative position, the buffer tape returns the list entry at that index (`Turing.FinTM.bufferTape_nat`). The bound $z<m$ gives $n<m$, so the $n$th entry of the replicated list is $1$. Thus the tape contains `some true` at $z$.

**Key facts.** `Turing.FinTM.bufferTape_nat`.
