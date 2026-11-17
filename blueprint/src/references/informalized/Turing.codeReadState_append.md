<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeParser.lean :: Turing.codeReadState_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successor-state decoding

**Claim.** For every bound $n$, optional state $s$, and bit string $x$, reading the encoding of $s$ followed by $x$ succeeds and returns $(s,x)$.

**Proof.** Split on whether $s$ is absent or present. If it is absent, its encoding is the single bit $0$, so the reader consumes that bit and returns the empty state together with the untouched suffix. If $s$ is present, its encoding begins with $1$, followed by the unary encoding of the state index and then $x$. The reader consumes the initial $1$ and delegates the rest to the bounded unary-state reader. The prefix-inverse property of that reader (`codeReadFin_append`) says it returns the given state and leaves $x$ unchanged; hence the successor-state reader returns $(s,x)$.

**Key facts.** `Turing.codeReadFin_append`.
