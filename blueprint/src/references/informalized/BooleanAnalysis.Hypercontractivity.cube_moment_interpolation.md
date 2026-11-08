<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Basic.lean :: BooleanAnalysis.Hypercontractivity.cube_moment_interpolation -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Interpolation of Cube Moments

**Claim.** If $0<p<2<q$, then $\mathbb E[f^2]\le(\mathbb E|f|^p)^{(q-2)/(q-p)}(\mathbb E|f|^q)^{(2-p)/(q-p)}$.

**Proof.** Set $r=(q-p)/(2-p)$, so $r\ge1$ because $q>2$, and define $w(x)=|f(x)|^p$ and $v(x)=|f(x)|^{2-p}$. The finite-sum weighted Hölder inequality bounds the expectation of $wv$ by $(\mathbb E w)^{1-1/r}(\mathbb E(wv^r))^{1/r}$. Both $w$ and $v$ are nonnegative, as required for this inequality. Pointwise, $w(x)v(x)=|f(x)|^2=f(x)^2$. Also, $(2-p)r=q-p$, so $w(x)v(x)^r=|f(x)|^{p+(2-p)r}=|f(x)|^q$. Rewriting the two exponents, $1-1/r=(q-2)/(q-p)$ and $1/r=(2-p)/(q-p)$, gives the stated estimate. Here the conversion from the finite uniform sum to the expectation notation uses $\mathbb E_x F(x)=\mathbb E F$ (\texttt{BooleanAnalysis.expect_eq_fintypeExpect}).

**Key facts.** `BooleanAnalysis.expect_eq_fintypeExpect`.
