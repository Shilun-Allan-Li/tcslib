<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/Applications.lean :: BooleanAnalysis.Hypercontractivity.product_boolean_residual_abs_expect -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Absolute Residual Moment Identity

**Claim.** For a finite product probability space with strictly positive coordinate weights, a Boolean-valued function $f$, and a coordinate set $S$, the expectation of $|f-E_Sf|$ equals the expectation of $(f-E_Sf)^2$.

**Proof.** Write $m=E_Sf$. First, $|m(x)|\le 1$ for every $x$: the conditional expectation is a weighted average of values in $\{-1,1\}$, and the product masses sum to $1$. Since $f(x)$ is either $-1$ or $1$, this bound gives the pointwise identity $|f(x)-m(x)|=1-f(x)m(x)$.

The conditional expectation is self-adjoint with respect to expectation, and conditioning twice on $S$ is the same as conditioning on the intersection $S\cap S=S$. Consequently, $\mathbb E[f m]=\mathbb E[f E_Sm]=\mathbb E[m^2]$. Thus $\mathbb E|f-m|=1-\mathbb E[m^2]$, using that the total mass is $1$.

Finally, Booleanity gives $f^2=1$, so $(f-m)^2=1-2fm+m^2$ pointwise. Taking expectations and substituting $\mathbb E[fm]=\mathbb E[m^2]$ yields $\mathbb E[(f-m)^2]=1-\mathbb E[m^2]$, proving the identity.

**Key facts.** `BooleanAnalysis.Hypercontractivity.FiniteProduct.mass_sum`, `BooleanAnalysis.Hypercontractivity.FiniteProduct.condExp_comp`, `BooleanAnalysis.Hypercontractivity.FiniteProduct.condExp_selfAdjoint`, `BooleanAnalysis.Hypercontractivity.FiniteProduct.expect_const`, `BooleanAnalysis.Hypercontractivity.FiniteProduct.expect_const_mul`.
