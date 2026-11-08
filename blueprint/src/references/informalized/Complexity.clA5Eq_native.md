<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Eq_native -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Time Equality of Unary Values

**Claim.** If unary encodings of the natural-number-valued functions $f$ and $g$ are polynomial-time computable, then the Boolean-valued function returning true exactly when $f(x)=g(x)$ is polynomial-time computable.

**Proof.** Compute the two polynomial-time tests $f(x)\le g(x)$ and $g(x)\le f(x)$ using the unary comparison result (`clA5Le_native`). Combine their Boolean outputs by conjunction, which preserves polynomial-time computability (`clA5_pt_and`). For natural numbers, both inequalities hold exactly when the numbers are equal. Therefore the conjunction is the required equality test.

**Key facts.** `Complexity.clA5Le_native`, `Complexity.clA5_pt_and`.
