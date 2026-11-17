<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeParser.lean :: Turing.codeReadUnary_sound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary decoding is sound

**Claim.** If the unary reader successfully returns value $n$ and suffix $r$ on a bit string $x$, then $x$ consists of exactly $n$ ones, followed by a zero and then $r$.

**Proof.** Induct on the input string, allowing the decoded number to vary. The empty input cannot be read successfully. If the input begins with $0$, the reader returns value $0$ and the remaining tail; equality of the returned value and suffix identifies $n=0$ and $r$ with that tail, giving the required form. If the input begins with $1$, the reader must successfully read the tail as some value $k$ and suffix $r$. Its rule increments the value, so the assumed result identifies $n=k+1$. By the induction hypothesis, the tail is $k$ ones followed by a zero and $r$; adding the initial $1$ gives the required string of $k+1$ ones followed by the same zero and suffix.
