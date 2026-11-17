<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.capturedSummary_true -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Summary Recognizes the Singleton One

**Claim.** For every finite bit word $w$, its summary is `some true` exactly when $w=[true]$.

**Proof.** Split by the length of $w$. For the empty word, the summary is `none`, so neither side holds. For a one-bit word $[b]$, the summary is `some b`; this equals `some true` exactly when $b=true$, which is exactly the condition that the word is $[true]$. For a word with at least two bits, the summary is `some false`, so it cannot equal `some true`, and the word is not the singleton $[true]$.
