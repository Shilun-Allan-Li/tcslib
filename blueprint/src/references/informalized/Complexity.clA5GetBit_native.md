<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5GetBit_native -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Indexed Bit Read

**Claim.** If $f$ is polynomial-time computable and the unary word of length $i(x)$ is polynomial-time computable from $x$, then returning the bit of $f(x)$ at index $i(x)$, with false as the out-of-range default, is polynomial-time computable.

**Proof.** First compute the suffix of $f(x)$ obtained by dropping its first $i(x)$ bits; this is polynomial-time by `Complexity.clA5Drop_native`, from the assumed computation of $f$ and the unary index. Take the first bit of that suffix, padding by false when the suffix is empty. The Boolean-valued first-bit test is polynomial-time: compute the first bit by comparing the one-bit prefix with the fixed word $[\mathrm{true}]$ (`Complexity.clA5_pt_head`, `Complexity.clA5_pt_eq`, and composition via `Complexity.PolyTimeComputable.comp`). For any word $w$, this test equals its head bit, defaulting to false when empty. Applying it to the suffix gives the desired bit, since the head of $f(x)$ after dropping $i(x)$ entries is exactly the indexed bit with the specified default.

**Key facts.** `Complexity.clA5Drop_native`, `Complexity.clA5_pt_head`, `Complexity.clA5_pt_eq`, `Complexity.PolyTimeComputable.comp`.
