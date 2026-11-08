<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/ProductDifferentiation.lean :: BooleanAnalysis.GaussianSpace.continuous_integral_gaussianProductDensityDerivative -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Continuity of the Integrated Density Derivative

**Claim.** Let $I$ be finite, let $f:\mathbb R^I\to\mathbb R$ be measurable with $|f(z)|\le1$ everywhere, and let $v>0$. The function of $c\in\mathbb R^I$ obtained by integrating $f(z)$ times the product Gaussian density derivative at mean $c$ and input $z$ with respect to Lebesgue measure is continuous into the continuous linear functionals on $\mathbb R^I$.

**Proof.** Fix a mean vector $c$ and consider means $m$ in the unit ball around it. The coordinate bound `abs_coordinate_le_of_mem_ball` gives $|m_i|\le\|c\|+1$ for every coordinate. Apply the domination result `gaussianProductDensity_derivative_dominated` with this uniform coordinate bound: it supplies an integrable function that bounds the norm of the density derivative for all these means and all inputs $z$. Since $|f(z)|\le1$, the same integrable function dominates the norm of the integrand after multiplication by $f(z)$. The integrand is strongly measurable in $z$ for each fixed $m$, by measurability of $f$ and continuity of the density derivative in its input (`continuous_gaussianProductDensityDerivative`). For each fixed $z$, it varies continuously with $m$: joint continuity of the derivative (`continuous_gaussianProductDensityDerivative_joint`), restricted to the pair $(m,z)$, gives this after multiplication by the fixed scalar $f(z)$. The dominated continuity theorem for parameter-dependent integrals now implies continuity at $c$. Since $c$ was arbitrary, the integral map is continuous everywhere.

**Key facts.** `BooleanAnalysis.GaussianSpace.gaussianProductDensity_derivative_dominated`, `BooleanAnalysis.GaussianSpace.abs_coordinate_le_of_mem_ball`, `BooleanAnalysis.GaussianSpace.continuous_gaussianProductDensityDerivative`, `BooleanAnalysis.GaussianSpace.continuous_gaussianProductDensityDerivative_joint`.
