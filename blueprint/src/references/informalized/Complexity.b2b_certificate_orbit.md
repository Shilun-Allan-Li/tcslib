<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Inclusions.lean :: Complexity.b2b_certificate_orbit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Orbit of Fixed-Width Binary Increment

**Claim.** If $r<2^Q$, then iterating fixed-width little-endian increment $r$ times from the length-$Q$ zero word produces the binary representation of $r$ in width $Q$.

**Proof.** Induct on $r$. At $r=0$, the zero word is the length-$Q$ representation of zero, by `Complexity.Meyer.enumWord_zero`. For the successor case, the induction hypothesis identifies the current iterate with the representation of $r$. The bound on the successor, $r+1<2^Q$, lets the fixed-width increment theorem apply: incrementing the representation of $r$ returns the representation of $r+1$ (`Complexity.Meyer.incFixed_enumWord`). In particular, the increment result is present rather than absent, so the iteration function, which uses the original word only as a fallback on overflow, returns that incremented representation. This proves the successor case.

**Key facts.** `Complexity.Meyer.enumWord_zero`, `Complexity.Meyer.incFixed_enumWord`.
