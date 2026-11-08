<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeParser.lean :: Turing.codeReadState_sound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successor-state decoding is sound

**Claim.** Whenever the successor-state reader returns an optional state $s$ and suffix $r$ on input $x$, the input is the encoding of $s$ followed by $r$.

**Proof.** If $x$ is empty, the reader cannot succeed, so this case is impossible. For a nonempty input, split on its first bit. If that bit is $0$, the reader returns no state and the remaining tail as suffix. The input is therefore exactly the encoding of no state followed by that tail. If the first bit is $1$, inspect the bounded state reader's result on the tail. Failure cannot produce the assumed successful result. On success, the returned state and suffix must agree with $s$ and $r$. The soundness of bounded state decoding (`codeReadFin_sound`) identifies the tail as the unary encoding of the returned state followed by $r$. Prefixing the initial $1$ gives precisely the encoding of the successor state followed by $r$.

**Key facts.** `Turing.codeReadFin_sound`.
