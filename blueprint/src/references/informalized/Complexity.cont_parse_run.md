<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.cont_parse_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parsing an Encoded Prefix

**Claim.** If $y=pre\,\langle x,u\rangle$, then the pair loader, started at the beginning of the encoded $x$ with buffer $a$, reaches parser state $3$ after $2|x|+2$ steps, having appended $x$ to the buffer and advanced past the encoding of $x$ and its separator.

**Proof.** Proceed by induction on $x$. If $x$ is empty, the input begins with the separator $0,1$ after $pre$. The two-step separator-recognition result (`Complexity.cont_parse_separator`) moves the parser to state $3$, advances the input head by two, and leaves the buffer unchanged, giving the claim. For $x=b::x'$, the encoding begins with the repeated pair $b,b$, followed by the encoding of $x'$. First apply the two-step repeated-bit result (`Complexity.cont_parse_double`): it consumes that pair, appends $b$ to the buffer, and returns the parser to state $0$. The remaining input has the same form with prefix $pre\,b\,b$ and buffer $a\,b$. The run-length addition law (`Turing.MultiTapeTM.runFrom_add`) splits the total run into these two initial steps and the remaining $2|x'|+2$ steps. The induction hypothesis handles the remainder, and the lengths and concatenations simplify to the stated endpoint.

**Key facts.** `Complexity.cont_parse_separator`, `Complexity.cont_parse_double`, `Turing.MultiTapeTM.runFrom_add`.
