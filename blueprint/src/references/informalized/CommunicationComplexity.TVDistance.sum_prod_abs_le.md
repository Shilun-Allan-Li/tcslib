<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/TVDistance.lean :: CommunicationComplexity.TVDistance.sum_prod_abs_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product weight gap bound

**Claim.** Under the stated nonnegativity and unit-sum assumptions, the sum of absolute differences between the product weights is at most the sum of the two marginal absolute-difference sums.

**Proof.** First rewrite the sum over pairs as an iterated sum, summing over $y$ for each fixed $x$. For each pair, the estimate $|ab-cd|\le |a-c|b+c|b-d|$ holds when $b,c\ge0$ (`abs_mul_sub_mul_le`). Apply it with $a=a(x)$, $b=b(y)$, $c=c(x)$, and $d=d(y)$, then sum over both indices. Distributing the sums turns the first term into $|a(x)-c(x)|\sum_y b(y)$ and the second into $c(x)\sum_y|b(y)-d(y)|$. The first inner sum is one, and summing the coefficient $c(x)$ in the second term also gives one. The result is precisely the sum of the two claimed marginal bounds.

**Key facts.** `CommunicationComplexity.TVDistance.abs_mul_sub_mul_le`.
