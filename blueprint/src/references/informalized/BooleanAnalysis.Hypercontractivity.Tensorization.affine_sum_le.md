<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Tensorization.lean :: BooleanAnalysis.Hypercontractivity.Tensorization.affine_sum_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Affine Sum Contraction

**Claim.** Under the stated one-dimensional contraction assumptions for the two probability measures, the affine function of the sum contracts from the $L^p$ seminorm under the product measure to the $L^q$ seminorm.

**Proof.** If $q<\infty$, the result is exactly the finite-exponent tensorization theorem (affine_sum_le_of_ne_top). Suppose instead that $q=\infty$. When $p<\infty$, choose a natural number $N$ with $p\le N$. For every integer $n\ge N$, monotonicity of the $L^r$ seminorm in the exponent gives each one-dimensional contraction at exponent $n$ from the assumed contraction into $L^\infty$. The finite-exponent result then bounds the product-space $L^n$ seminorm of the output by the input's $L^p$ seminorm. The theorem that uniform bounds on all sufficiently high integer moments control the essential supremum (eLpNorm_top_le_of_forall_nat) gives the desired $L^\infty$ bound.

It remains to handle $p=q=\infty$. Let $C$ be the essential supremum of the input function $(x,y)\mapsto a+b(x+y)$. Thus the input is bounded by $C$ almost everywhere under the product measure. Fubini's theorem first gives, for almost every $x$, that $a+bx+by$ is bounded by $C$ for almost every $y$. The one-dimensional $L^\infty$ contraction for $\nu$ transfers this bound to $a+bx+\rho by$. Measurability and the commutation of almost-everywhere quantifiers on the product let us reverse the order of sections, obtaining this bound for almost every $x$ for almost every $y$. Applying the contraction for $\mu$ to those sections transfers it to $a+\rho b(x+y)$. The product-measure section theorem then gives the bound almost everywhere on the product. Hence the output's essential supremum, and therefore its $L^\infty$ seminorm, is at most $C$.

**Key facts.** `BooleanAnalysis.Hypercontractivity.Tensorization.affine_sum_le_of_ne_top`, `BooleanAnalysis.Hypercontractivity.Tensorization.eLpNorm_top_le_of_forall_nat`.
