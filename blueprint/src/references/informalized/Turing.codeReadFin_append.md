<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeParser.lean :: Turing.codeReadFin_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Unary Index Decoding

**Claim.** For an index $i<n$ and any bit string $x$, the bounded unary index reader succeeds on the unary code of $i$ followed by $x$, returning $(i,x)$.

**Proof.** The unary decoder reads a block of $i$ ones followed by a zero as the natural number $i$ and leaves the suffix $x` untouched (`Turing.codeReadUnary_append`). The bounded reader then checks that the decoded number is below $n$. This holds because $i$ is an element of the index set of size $n$. It therefore returns the same index, with suffix $x$.

**Key facts.** `Turing.codeReadUnary_append`.
