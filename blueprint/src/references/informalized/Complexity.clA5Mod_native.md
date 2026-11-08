<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Mod_native -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary Remainder Is Polynomial-Time

**Claim.** If the unary encoding of a natural-valued function is polynomial-time computable, then for every natural number $k$ its unary remainder modulo $k$ is polynomial-time computable.

**Proof.** Use the division closure result to compute the unary encoding of $f(x)/k$ (`clA5Div_native`). Multiplying that value by the fixed number $k$ preserves polynomial-time computability (`clA5Times_native`), so the unary encoding of $k(f(x)/k)$ is also computable in polynomial time. Apply closure under truncated subtraction to subtract this product from the unary encoding of $f(x)$ (`clA5Sub_native`). The resulting natural number is $f(x)-k(f(x)/k)$, which equals $f(x)\bmod k$ by the division algorithm. Thus the resulting polynomial-time function is exactly the required unary remainder function. This also covers $k=0$ under the usual natural-number remainder convention, for which the remainder is $f(x)$.

**Key facts.** `Complexity.clA5Div_native`, `Complexity.clA5Times_native`, `Complexity.clA5Sub_native`.
