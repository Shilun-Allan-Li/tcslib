<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimeBlockLoop.lean :: Complexity.length_xorPairStep_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pairing-step length bound

**Claim.** For every bit string $s$, encoding the strings obtained by removing the first bit from each of its total pair projections produces a bit string of length at most $\max(|s|,2)$.

**Proof.** Apply the general length bound for encoding the two pair projections after dropping arbitrary prefixes (Complexity.length_pairEncode_drop_le), taking both drop lengths to be $1$. The resulting encoded list is exactly the pairing-step output, so its length is at most $\max(|s|,2)$.

**Key facts.** `Complexity.length_pairEncode_drop_le`.
