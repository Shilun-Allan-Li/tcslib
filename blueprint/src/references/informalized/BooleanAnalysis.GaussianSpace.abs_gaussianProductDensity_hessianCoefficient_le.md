<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/ProductHessian.lean :: BooleanAnalysis.GaussianSpace.abs_gaussianProductDensity_hessianCoefficient_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Product Gaussian Hessian Coefficient Bound

**Claim.** Under the stated coordinatewise bounds on the Gaussian densities and their second-score terms, the absolute product-density Hessian coefficient for any pair of indices is at most $(1+2/v)\prod_k a(k)$.

**Proof.** Write $K=\prod_k p_v(c(k),z(k))$ and $A=\prod_k a(k)$. Nonnegativity of the Gaussian density and the coordinatewise density bounds imply $0\le K\le A$. For each index $i$, the squared-score estimate (BooleanAnalysis.GaussianSpace.gaussianProductDensity_squaredScore_le) bounds $((z(i)-c(i))^2/v^2)K$ by $(1+1/v)A$. Apply it at both $i$ and $j$. The product-Hessian estimate (BooleanAnalysis.GaussianSpace.abs_productHessian_mul_le), with its auxiliary scalar equal to $K$, bounds the absolute value in question by $[((z(i)-c(i))^2+(z(j)-c(j))^2)/(2v^2)+1/v]K$; its scalar hypothesis holds since $0\le K\le A$ is not itself a bound by $1$, so instead use the proof's direct premise: the stated application requires $|K|\le1$. Thus, as supplied, this step is not justified by the visible hypotheses unless an additional fact gives $K\le1$.

**Key facts.** `BooleanAnalysis.GaussianSpace.gaussianProductDensity_squaredScore_le`, `BooleanAnalysis.GaussianSpace.abs_productHessian_mul_le`.

**Caveat.** The source applies abs_productHessian_mul_le with scalar $K$ and claims its required hypothesis $|K|\le1$ using only norm_num. That does not follow from the displayed hypotheses for general nonnegative variance $v$; the proof source as supplied appears invalid at this step.
