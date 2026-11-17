<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/Expressions.lean :: Light.Expr.height_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positivity of Expression Height

**Claim.** Every expression $e$ has strictly positive height: $0<\mathrm{height}(e)$.

**Proof.** Induct on the expression. Constants and variables have height $1$. For an operation applied to $a$ and $b$, its height is $\max(\mathrm{height}(a),\mathrm{height}(b)+1)$, which is at least the positive height of $a$. For a load, the height equals that of its argument, so positivity follows from the induction hypothesis.
