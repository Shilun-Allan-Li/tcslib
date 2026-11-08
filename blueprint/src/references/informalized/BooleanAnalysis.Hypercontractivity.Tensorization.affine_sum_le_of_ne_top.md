<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Tensorization.lean :: BooleanAnalysis.Hypercontractivity.Tensorization.affine_sum_le_of_ne_top -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finite-Exponent Affine Sum Contraction

**Claim.** If each of two probability measures contracts affine functions from $L^p$ to $L^q$, where $1\le p\le q<\infty$, then their product measure contracts the corresponding affine function of the sum by the same bound.

**Proof.** Since $q$ is finite and $p\le q$, both exponents are positive and finite. Write $p_0=p$ and $q_0=q$ for their real values. Fix $a,b$. For each fixed $y$, apply the assumed inequality for $\mu$ to the affine function with constant term $a+\rho by$ and slope $b$. Expressing the finite-exponent seminorms as integrals of powers and raising the inequality to the appropriate power gives
\[\int \lvert a+\rho b(x+y)\rvert^{q_0}\,d\mu(x)\le \left(\int \lvert a+bx+\rho by\rvert^{p_0}\,d\mu(x)\right)^{q_0/p_0}.\]
Integrate this in $y$ and take the $q_0$-th root. Tonelli's theorem identifies the left side with the product-space output norm.

Next exchange the order of the mixed norms using the comparison of mixed nonnegative integrals (mixed_lintegral_le), applied to $g(x,y)=|a+bx+\rho by|$ with exponents $p_0\le q_0$. Finally, for each fixed $x$, apply the assumed inequality for $\nu$ to the affine function with constant term $a+bx$ and slope $b$. In integral form this bounds the resulting inner $L^{q_0}$ integral, after taking the $p_0/q_0$ power, by $\int |a+b(x+y)|^{p_0}\,d\nu(y)$. Integrating in $x$, taking the $p_0$-th root, and using Tonelli again yields the input norm on the product space. Combining the inequalities proves the claim.

**Key facts.** `BooleanAnalysis.Hypercontractivity.Tensorization.mixed_lintegral_le`.
