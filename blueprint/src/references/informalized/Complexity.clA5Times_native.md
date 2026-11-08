<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Times_native -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Unary Multiplication

**Claim.** If the unary word of length $f(x)$ is polynomial-time computable, then for every fixed natural number $k$, the unary word of length $kf(x)$ is polynomial-time computable.

**Proof.** Induct on $k$. For $k=0$, the required word is always empty, hence is a constant function and is polynomial-time computable (`clA5_pt_const`). In the successor case, $(k+1)f(x)=kf(x)+f(x)$, so the desired unary word is the concatenation of the unary words for these two lengths. The induction hypothesis handles the first word, the assumption handles the second, and concatenation preserves polynomial-time computability (`clNative_append`).

**Key facts.** `Complexity.clA5_pt_const`, `Complexity.clNative_append`.
