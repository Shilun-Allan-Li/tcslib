<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Field_native -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Time Variable Header Access

**Claim.** If $s$ and the unary encoding of the index function $u$ are polynomial-time computable, then selecting field $(u(x))$ from the header $s(x)$ is polynomial-time computable.

**Proof.** Iterate the one-step header-tail operation on $s(x)$ a number of times equal to the length of the unary encoding of $u(x)$. Each tail operation is polynomial-time computable (`clHeaderTail_native`). Its output never exceeds the input length, by the tail-size bound in `clA5Pair_sizes`; hence iteration for a polynomially bounded number of steps remains polynomial-time computable (`clA5Iter_shrinking`). The iteration count is available in unary and polynomial time because the unary encoding of $u$ is polynomial-time computable; the proof obtains that encoding by filling a string of the same length as the output of $u$ (`clNative_fill`) and composing with $u$ (`PolyTimeComputable.comp`). Finally, apply the polynomial-time operation that extracts the first field (`clHeaderField_native`, at index zero) to the remaining header tail. Iterating the tail operation $u(x)$ times agrees with the header-tail operation indexed by $u(x)$, so this extraction returns precisely the desired field.

**Key facts.** `Complexity.clHeaderTail_native`, `Complexity.clNative_fill`, `Complexity.PolyTimeComputable.comp`, `Complexity.clA5Pair_sizes`, `Complexity.clA5Iter_shrinking`, `Complexity.clHeaderField_native`.
