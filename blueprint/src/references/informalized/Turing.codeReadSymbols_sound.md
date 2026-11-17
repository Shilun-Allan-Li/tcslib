<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeParser.lean :: Turing.codeReadSymbols_sound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Symbol-row decoding is sound

**Claim.** If the three-entry symbol-row reader returns a function $f$ and suffix $r$ on input $x$, then $x$ is the concatenation of the encodings of $f$ at blank, $0$, and $1$, followed by $r$.

**Proof.** Unpack the three successive successful reads performed by the row reader. They give values $a,b,c$ and intermediate suffixes $r_1,r_2$, with final suffix $r$. The returned function is assembled from $a,b,c$; since it equals $f$, its values at blank, $0$, and $1$ are respectively $f(\text{blank})$, $f(0)$, and $f(1)$. Apply the assumed soundness of the value reader to each successful read: the original input is the encoding of $a$ followed by $r_1$, that suffix is the encoding of $b$ followed by $r_2$, and that suffix is the encoding of $c$ followed by $r$. Combining these equalities and reassociating concatenation yields the claimed serialization followed by $r$.
