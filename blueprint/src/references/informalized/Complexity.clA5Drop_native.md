<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Drop_native -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Counted Suffix

**Claim.** If $s$ and $u$ are polynomial-time computable binary-word functions, then mapping $x$ to the suffix of $s(x)$ after dropping its first $|u(x)|$ bits is polynomial-time computable.

**Proof.** Use the shrinking iterator theorem with the operation that removes the first bit (`clA5Iter_shrinking`, `clA5_pt_tail`). Removing a first bit never increases list length, and the required unary iteration count is polynomial-time computable: fill a list with true bits whose length equals the length of $u(x)$, then compose this construction with $u$ (`clNative_fill`, `PolyTimeComputable.comp`). The theorem therefore gives polynomial-time computation of the result of applying `tail` exactly $|u(x)|$ times to $s(x)$. Repeatedly removing the first bit is exactly dropping that many bits, including when the count is zero or exceeds the list length, so the result is the stated suffix.

**Key facts.** `Complexity.clA5Iter_shrinking`, `Complexity.clA5_pt_tail`, `Complexity.clNative_fill`, `Complexity.PolyTimeComputable.comp`.
