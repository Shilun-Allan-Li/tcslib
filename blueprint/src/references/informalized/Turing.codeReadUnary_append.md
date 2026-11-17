<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeParser.lean :: Turing.codeReadUnary_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary decoding

**Claim.** For every natural number $n$ and bit string $x$, the unary reader applied to $n$ ones followed by a zero and then $x$ returns $(n,x)$.

**Proof.** Proceed by induction on $n$. At $n=0$, the input starts with $0$, which the reader consumes and returns value $0$ with suffix $x$. For the successor case, the input has one initial $1$ followed by the encoding for $n$ and suffix $x$. By the induction hypothesis, reading that tail returns $(n,x)$. The reader's rule for an initial $1$ increments the decoded value while preserving the suffix, so the result is $(n+1,x)$.
