<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Sub_native -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Unary Truncated Subtraction

**Claim.** If the unary words of lengths $f(x)$ and $g(x)$ are polynomial-time computable, then the unary word of length $f(x)-g(x)$, with natural-number subtraction, is polynomial-time computable.

**Proof.** Apply the polynomial-time unary-drop construction (\texttt{clA5Drop\_native}) to the two given unary functions. It computes the first unary word after dropping as many symbols as the length of the second. Since the inputs are unary words of lengths $f(x)$ and $g(x)$, the remaining word is unary and has length $\max(f(x)-g(x),0)$, which is exactly $f(x)-g(x)$ under natural-number subtraction. Hence it is the required output.

**Key facts.** `Complexity.clA5Drop_native`.
