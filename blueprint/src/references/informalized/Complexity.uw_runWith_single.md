<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Diagonalization/Relativization.lean :: Complexity.uw_runWith_single -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A one-choice run

**Claim.** For any Boolean choice $b$, input $x$, and configuration $c$ on input $x$, running the machine with the one-bit choice string $[b]$ gives the same configuration as taking one step with choice $b$.

**Proof.** By the definition of a run, processing a nonempty choice string first takes one step using its head bit, then processes the remaining choices. For $[b]$, the remaining string is empty, whose run leaves the configuration unchanged. Hence the result is exactly the single step with choice $b$.
