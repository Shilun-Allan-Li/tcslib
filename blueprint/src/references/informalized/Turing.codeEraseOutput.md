<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeParser.lean :: Turing.codeEraseOutput -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output field erasure

**Claim.** For every bit string $x$, discarding the optional output decoded by the output reader leaves exactly the suffix returned by the pair skipper accepting $(a,b)$ when $a=1$ or $b=0$.

**Proof.** Inspect the input by its length and, when it has at least two bits, by its first two bits. Inputs shorter than two bits make both procedures fail. On the three accepted pairs, $00$, $10$, and $11$, the reader returns the suffix after those two bits, and the skipper accepts because respectively $a=1$ or $b=0$. On the remaining pair $01$, both fail. Hence the erased reader and skipper agree for every input.
