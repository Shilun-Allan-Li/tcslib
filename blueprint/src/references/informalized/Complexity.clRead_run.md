<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clRead_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parsing a complete encoded field

**Claim.** Starting with the reader at the beginning of the encoded field and target $o$, where $|o|\le |w|$, after $3|w|+3$ steps it reaches completed control, leaves the stream unchanged, has target $w$, and has stream and target heads at the stated positions.

**Proof.** First apply the forward-decoding result to the $|w|$ doubled bits, taking the written prefix to be empty and the unread target to be $o$. Since $|o|\le |w|$, the leftover suffix after decoding is empty, so this phase leaves target $w$ and advances the stream cursor by $2|w|$. The stream now presents the two separator bits `false,true`. The separator-reading result consumes those two bits and enters rewind control with the target head at $|w|-1$ and the stream cursor at $|u|+2|w|+2$. Finally apply the rewind result with $j=|w|$: it takes $|w|+1$ steps, leaves the stream fixed, and returns the target head to zero in completed control. The phases total $2|w|+2+(|w|+1)=3|w|+3$ steps. Their run lengths concatenate by `Turing.MultiTapeTM.runFrom_add`; the doubled-prefix length is $2|w|$, and the encoding’s remaining suffix is exactly the separator followed by the tail.

**Key facts.** `Complexity.clRead_forward`, `Complexity.clRead_separator`, `Complexity.clRead_rewind`, `Turing.MultiTapeTM.runFrom_add`.
