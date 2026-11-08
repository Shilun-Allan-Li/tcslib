<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Tautology.lean :: Complexity.taut_syntax_done -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance from the Exact-End State

**Claim.** For every binary word $x$, the scanner started in its exact-end state accepts $x$ if and only if $x$ is empty.

**Proof.** If $x$ is empty, the scanner remains in the exact-end state, which is accepting. If $x$ is nonempty, its first bit moves the scanner to the error state. The remaining suffix is rejected from that state by `Complexity.taut_syntax_bad`. Hence acceptance occurs exactly for the empty word.

**Key facts.** `Complexity.taut_syntax_bad`.
