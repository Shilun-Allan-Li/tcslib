<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeParser.lean :: Turing.codeEraseSign -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Movement field erasure

**Claim.** For every bit string $x$, discarding the decoded head movement leaves exactly the suffix returned by the pair skipper accepting $(a,b)$ when $a=1$ or $b=0$.

**Proof.** Split according to whether the input has fewer than two bits, and otherwise according to its first two bits. Inputs too short for a pair make both procedures fail. For $00$, $10$, and $11$, the movement reader succeeds and returns the suffix after the pair; the skipper accepts each of these. For $01$, the reader has no movement code and the skipper rejects. The two results therefore agree in every case.
