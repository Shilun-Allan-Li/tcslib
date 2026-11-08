<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/KarpLiptonPrefix.lean :: Complexity.KarpLipton.mem_prefixLang_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Prefix Membership Criterion

**Claim.** The encoded pair of $y$ with $k$ ones followed by $0p$ belongs to the polynomial prefix language exactly when some suffix $s$ makes $ps$ have length $C(|\pi_1(y)|+1)^c$ and makes the encoding of $y$ paired with $ps$ belong to $V$.

**Proof.** Use the marker-run characterization of prefix membership (`mem_prefixLangOf_iff`) with the length function defining this polynomial prefix language. Its bound evaluated at $y$ is $C(|\pi_1(y)|+1)^c$, yielding the claimed equivalence.

**Key facts.** `Complexity.KarpLipton.mem_prefixLangOf_iff`.
