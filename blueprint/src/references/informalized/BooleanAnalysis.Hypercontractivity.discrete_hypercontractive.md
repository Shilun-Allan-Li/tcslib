<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Discrete.lean :: BooleanAnalysis.Hypercontractivity.discrete_hypercontractive -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Discrete Centered Hypercontractivity

**Claim.** Under the stated finite-support and atom-mass assumptions, a centered random variable is affine hypercontractive from exponent $2$ to exponent $q$ with parameter $\lambda^{1/2-1/q}/(2\sqrt{q-1})$, and also from exponent $q/(q-1)$ to exponent $2$ with the same parameter.

**Proof.** Put $A=\lambda^{1/2-1/q}$, let $N$ be the $L^2$ norm of $X$, and write $r=A/(2\sqrt{q-1})$. The finite atom hypothesis ensures that $X$ belongs to both $L^2$ and $L^q$ (the finite-support integrability fact `HasAtomLowerBound.memLp`). Since $q>2$ and $0<\lambda\le 1$, we have $0<A\le1$ and $\sqrt{q-1}>1$, so $0\le r<1$.

If $N=0$, then $X=0$ almost everywhere. Thus each affine perturbation $a+cX$ agrees almost everywhere with the constant $a$. On a probability space, the norm of that constant is the same at either exponent, so the required norm inequality follows.

Otherwise, normalize by setting $Y=X/N$. Its $L^2$ norm is $1$, and its mean is zero. Let $C$ be its $L^q$ norm. Monotonicity of norms on a probability space gives $C\ge1$. The centered-variable hypercontractivity estimate (`mean_zero_hypercontractive`) therefore applies to $Y$, giving parameter $1/(2C\sqrt{q-1})$. Rescaling from $Y$ to $X$ preserves this estimate (`IsHypercontractive.const_mul`).

The finite atom norm bound (`discrete_lp_norm_le`) gives $\|X\|_q\le A^{-1}N$, hence $C=\|Y\|_q\le A^{-1}$ and $AC\le1$. Consequently $r\le1/(2C\sqrt{q-1})$. Decreasing the nonnegative parameter preserves hypercontractivity for a centered variable (`IsHypercontractive.mono_radius`), proving the forward assertion with parameter $r$. Finally, the conjugation principle for centered variables converts the $2$-to-$q$ estimate into the $q/(q-1)$-to-$2$ estimate (`IsHypercontractive.conjugate`).

**Key facts.** `BooleanAnalysis.Hypercontractivity.HasAtomLowerBound.memLp`, `BooleanAnalysis.Hypercontractivity.mean_zero_hypercontractive`, `BooleanAnalysis.Hypercontractivity.IsHypercontractive.const_mul`, `BooleanAnalysis.Hypercontractivity.discrete_lp_norm_le`, `BooleanAnalysis.Hypercontractivity.IsHypercontractive.mono_radius`, `BooleanAnalysis.Hypercontractivity.IsHypercontractive.conjugate`.
