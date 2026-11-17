<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/TVDistance.lean :: CommunicationComplexity.TVDistance.abs_mul_sub_mul_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product difference bound

**Claim.** For real numbers $a,b,c,d$ with $b,c\ge 0$, one has $|ab-cd|\le |a-c|b+c|b-d|$.

**Proof.** Rewrite the difference as $ab-cd=(a-c)b+c(b-d)$. The triangle inequality bounds its absolute value by $|(a-c)b|+|c(b-d)|$. Since $b$ and $c$ are nonnegative, absolute values of these products simplify to $|a-c|b$ and $c|b-d|$, respectively, proving the inequality.
