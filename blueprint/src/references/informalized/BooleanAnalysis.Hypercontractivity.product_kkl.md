<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/Applications.lean :: BooleanAnalysis.Hypercontractivity.product_kkl -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product KKL Influence Bound

**Claim.** There is a universal positive constant $c$ such that for every product space and Boolean function satisfying the stated assumptions, some coordinate has influence at least $\frac{c}{\log(1/\lambda)}\operatorname{Var}[f]\frac{\log n}{n}$.

**Proof.** Take $c=1/100$. The logarithmic parameter bounds give $\frac12\le L\le D\le5L$, where $L=\log(1/\lambda)$ and $D=\log(9/\lambda)$; in particular, $L>0$. The proof also uses $\log n\ge0$. If the variance is zero, the target lower bound is nonpositive, while every coordinate influence is nonnegative, so the conclusion follows immediately.

Now suppose the variance is positive, and write $t=I[f]/\operatorname{Var}[f]$, where $I[f]$ is total influence. The variance-to-noisy-influence comparison, together with the identity expressing total influence as the sum of component energies weighted by their set sizes, gives $\operatorname{Var}[f]\le I[f]$, so $t>0$. Apply the scalar dichotomy to $L,D,\log n,t$. Its first alternative bounds the target by the average influence $I[f]/n$. Since the sum of coordinate influences is $I[f]$, some coordinate has influence at least this average, proving the result in that branch.

In the second alternative, the product KKL isoperimetric theorem supplies a coordinate whose influence is at least $t^{-2}(9/\lambda)^{-t}=t^{-2}e^{-Dt}$. Booleanity gives $\operatorname{Var}[f]\le1$. The scalar dichotomy bounds the target by this same isoperimetric quantity after using that variance bound, so this coordinate also suffices.

**Key facts.** `BooleanAnalysis.Hypercontractivity.ComparisonAux.kkl_log_parameters`, `BooleanAnalysis.Hypercontractivity.ComparisonAux.variance_rpow_ratio_le_noisy_total`, `BooleanAnalysis.Hypercontractivity.RandomizationAux.totalInfluence_eq_sum_card_components`, `BooleanAnalysis.Hypercontractivity.ComparisonAux.kkl_scalar_dichotomy`, `BooleanAnalysis.Hypercontractivity.RandomizationAux.boolean_variance_le_one`, `BooleanAnalysis.Hypercontractivity.product_kkl_isoperimetric`.
