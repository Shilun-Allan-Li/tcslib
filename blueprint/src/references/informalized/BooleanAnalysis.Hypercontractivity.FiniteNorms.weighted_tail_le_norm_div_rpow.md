<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/Norms.lean :: BooleanAnalysis.Hypercontractivity.FiniteNorms.weighted_tail_le_norm_div_rpow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Weighted moment tail bound

**Claim.** For nonnegative weights, a function on a finite set, and positive $q,c$, the weighted mass of the points where $c\le |f|$ is bounded by the $q$-th power of the weighted $q$-norm divided by $c$.

**Proof.** The weighted $q$-moment $M=\sum_x w_x|f_x|^q$ is nonnegative. On the event $c\le|f_x|$, monotonicity of the positive power gives $c^q\le|f_x|^q$; off that event, its indicator is zero. Multiplying these pointwise comparisons by the nonnegative weights and summing shows that $c^q$ times the weighted tail mass is at most $M$. Divide by $c^q>0$, and rewrite $M/c^q$ as $((M^{1/q})/c)^q$, which gives the claimed bound.
