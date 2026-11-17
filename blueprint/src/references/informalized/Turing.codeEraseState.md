<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeParser.lean :: Turing.codeEraseState -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successor-state erasure

**Claim.** For every $n$ and bit string $x$, discarding the decoded successor state from the state reader with bound $n$ gives exactly the suffix returned by the successor-field skipper with bound $n$.

**Proof.** If the input is empty, both procedures fail. If its first bit is $0$, both succeed immediately with the rest of the input as suffix, representing no successor state. If its first bit is $1$, the reader proceeds by reading a bounded unary index from the remaining bits, while the skipper applies the corresponding bounded-index skipper. Bounded-index erasure (`Turing.codeEraseFin`) says these leave the same suffix or both fail, completing this case.

**Key facts.** `Turing.codeEraseFin`.
