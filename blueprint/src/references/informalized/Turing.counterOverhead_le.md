<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean :: Turing.counterOverhead_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on counter overhead

**Claim.** For every Boolean word $w$, the overhead accumulated through the first $V(w)+1$ rounds is at most $4V(w)+2|w|+2$, where $V(w)$ is the binary value of $w$.

**Proof.** Write $V=V(w)$. The counter-potential identity at round $V$ says that the overhead through round $V$, plus twice the number of true bits in the original word, equals $4V$ plus twice the number of true bits in the counter word at round $V$. By `counter_word_exhausted`, that final word consists entirely of false bits, so its true-bit count is zero. Hence the overhead through round $V$ is at most $4V$, since the original word's true-bit count is nonnegative. The next round's contribution is $2|w|+2$: the exhausted word has length $|w|$ and begins with that many false bits. Splitting off this last summand gives the claimed bound.

**Key facts.** `Turing.counter_potential`, `Turing.counter_word_exhausted`.
