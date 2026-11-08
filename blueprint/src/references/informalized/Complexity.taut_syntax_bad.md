<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Tautology.lean :: Complexity.taut_syntax_bad -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rejection from the Error State

**Claim.** For every binary string $x$, the syntax scanner started in its error state rejects $x$.

**Proof.** Induct on the length of $x$. The empty string is rejected because the error state is not the accepting state. For a nonempty string $b::x$, scanning its first bit moves the scanner from the error state back to the error state. The one-step scanner identity (`Complexity.taut_syntax_cons`) therefore reduces acceptance of $b::x$ to acceptance of $x$ from the error state, which is false by the induction hypothesis.

**Key facts.** `Complexity.taut_syntax_cons`.
