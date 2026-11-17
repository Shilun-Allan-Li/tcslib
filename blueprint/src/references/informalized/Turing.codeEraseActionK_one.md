<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeFormat.lean :: Turing.codeEraseActionK_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-tape action erasure

**Claim.** For every $n$ and bit string $x$, discarding the parsed action from the one-work-tape action reader over $n+1$ states gives exactly the suffix returned by the transition-record skipper for $n$.

**Proof.** Apply the general action erasure law with $k=1$ to identify the erased reader with the one-tape instance of the action skipper. The equality between the one-tape transition-record skipper and that instance (`Turing.codeSkipAction_eq_codeSkipActionK`) then identifies this result with the specified skipper.

**Key facts.** `Turing.codeEraseActionK`, `Turing.codeSkipAction_eq_codeSkipActionK`.
