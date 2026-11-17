<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Reverse/TwoPoint.lean :: BooleanAnalysis.Hypercontractivity.reverse_two_point_normalized -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Normalized reverse two-point inequality

**Claim.** For $0<q<p<1$, $\rho\ge0$ with $\rho^2=(1-p)/(1-q)$, and $|a|<1$, the affine function $f(x)=1+a\sigma(x)$ on the one-dimensional cube satisfies $M_q(T_\rho f)\ge M_p(f)$.

**Proof.** The relation on $\rho^2$ and $0<q<p<1$ imply $0\le\rho<1$; hence both $|a|$ and $|\rho a|$ are less than $1$. The noise operator sends the affine function with coefficient $a$ to the same form with coefficient $\rho a$ (`noiseOp_affine_one_bit`). The positive-exponent mean formula and the two-point expectation formula (`expect_abs_rpow_affine`) therefore reduce the desired inequality to comparing the symmetrized moments $P=((1+a)^p+(1-a)^p)/2$ and $Q=((1+\rho a)^q+(1-\rho a)^q)/2$: it is enough to show $P\le Q^{p/q}$.

Expand the even parts of the generalized binomial series. Their constant terms are $1$, and their remaining terms are indexed by $2(k+1)$. For each such term, the coefficient comparison `choose_even_ratio_le`, together with $\rho\ge0$ and the even power of $a$, bounds the $p$-series term by $p/q$ times the corresponding $q$-series term at $\rho a$. Summability permits summing these inequalities, giving $P\le1+(p/q)(Q-1)$. Since $Q>0$, the tangent-line inequality for the power function at $1$ gives $1+(p/q)(Q-1)\le Q^{p/q}$. Thus $P\le Q^{p/q}$. Taking the increasing $1/p$ power, with $p>0$, gives the desired comparison of means.

**Key facts.** `BooleanAnalysis.Hypercontractivity.summable_choose_even`, `BooleanAnalysis.Hypercontractivity.even_part_rpow_eq_tsum`, `BooleanAnalysis.Hypercontractivity.choose_even_ratio_le`, `BooleanAnalysis.Hypercontractivity.expect_abs_rpow_affine`, `BooleanAnalysis.Hypercontractivity.lpMean_of_pos`, `BooleanAnalysis.Hypercontractivity.noiseOp_affine_one_bit`.
