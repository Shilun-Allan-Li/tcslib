<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeParser.lean :: Turing.codeReadSign_sound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Movement Reader Soundness

**Claim.** If the movement reader returns movement $s$ and suffix $r$ on input $x$, then $x$ is the two-bit code for $s$ followed by $r$.

**Proof.** Inspect the input according to its length. Inputs of length zero or one cannot be read successfully. For an input with at least two bits, examine the first two bits: the only successful cases are $11$, $00$, and $10$, decoded respectively as left, stay, and right. In each case the reader returns the remaining tail $r$, so the input is the stated movement code followed by $r$.
