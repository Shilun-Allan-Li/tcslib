<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPRun.lean :: Randomized.PIT.scan_ctx -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary Scan Context

**Claim.** For every bit string $x$, the head transducer output paired with the empty string has the same encoding as the context with unary prefix length equal to the output length and empty remaining components.

**Proof.** Rewrite the context using its definition. The head transducer output is a unary string by the fact that its output equals the all-$1$ string of the same length (`Randomized.PIT.uHead_eq_replicate`). Substituting this representation makes both sides identical by the definition of pairing.

**Key facts.** `Randomized.PIT.uHead_eq_replicate`.
