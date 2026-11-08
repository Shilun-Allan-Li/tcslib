<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.captureEmission_correct -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Summary Update Under an Emitted Bit

**Claim.** For every finite bit word $w$ and optional bit $e$, updating the summary of $w$ with $e$ gives the summary of the word formed by appending the contents of $e$ to $w$.

**Proof.** If no bit is emitted, its list of contents is empty, so appending it leaves $w$ unchanged, and the update returns the original summary. If a bit $b$ is emitted and $w$ is empty, both sides record the singleton word $[b]$ as `some b`. If $w$ has exactly one bit, appending $b$ makes a two-bit word, whose summary is `some false`; updating the existing summary with an emitted bit also gives `some false`. If $w$ already has at least two bits, its summary is `some false`, and the appended word still has at least two bits, so both sides again give `some false`.
