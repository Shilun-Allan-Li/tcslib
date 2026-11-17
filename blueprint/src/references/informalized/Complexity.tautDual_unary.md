<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Tautology.lean :: Complexity.tautDual_unary -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scan of a Unary Run

**Claim.** For every $n\in\mathbb{N}$ and binary string $r$, scanning $n$ consecutive $1$s followed by $r$ from the unary-index state preserves those $1$s and then gives the scan of $r$ from the unary-index state.

**Proof.** Induct on $n$. At $n=0$ the two lists being scanned are just $r$, so the claim is immediate. For the successor case, the scanner in the unary-index state reads the leading $1$ and remains in that same state; it also leaves that bit unchanged. Apply the induction hypothesis to the remaining $n$ ones followed by $r$, and prepend the unchanged leading bit. This yields the claimed output.
