<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Bonami.lean :: BooleanAnalysis.Hypercontractivity.moment_eq_expect -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Moments Equal Uniform Expectations on the Hypercube

**Claim.** Let $f:\{0,1\}^n\to\mathbb{R}$ be a Boolean function of arity $n$, let $p\in\mathbb{N}$, and let $P$ be a probability measure on the Boolean hypercube $\{0,1\}^n$ whose mass on each singleton $\{x\}$ equals the uniform weight $2^{-n}$. Then the $p$-th moment of $f$ under $P$ coincides with the expectation of $f^p$ under the uniform law: $\int f^p\,dP = \mathbb{E}[f^p] = 2^{-n}\sum_{x\in\{0,1\}^n} f(x)^p$.

**Proof.** The argument simply unwinds both sides to the same finite sum and matches it termwise; every step is forced once one recalls that the hypercube is a finite set.

1. **Unfold the moment as an integral.** By definition the $p$-th moment of $f$ under $P$ is the integral of the $p$-th power of $f$ against $P$, i.e. $\int f^p\,dP = \int_{\{0,1\}^n} f(x)^p\,dP(x)$, where $f^p$ is understood pointwise, $(f^p)(x)=f(x)^p$.

2. **Reduce the integral to a finite weighted sum.** The domain $\{0,1\}^n$ (formally $\mathrm{Fin}\,n\to\mathrm{Bool}$) is a finite set. A real-valued function on a finite type is automatically integrable against any measure, so no integrability side-condition survives. On a finite type an integral is literally a sum over the points, each weighted by the real-valued mass the measure assigns to that singleton:
\[
  \int_{\{0,1\}^n} f(x)^p\,dP(x) \;=\; \sum_{x\in\{0,1\}^n} P(\{x\})\, f(x)^p,
\]
where $P(\{x\})$ denotes the real number $(P\{x\}).\mathrm{toReal}$, and the scalar action is ordinary multiplication of reals.

3. **Unfold the right-hand side.** By definition the expectation under the uniform law is $\mathbb{E}[f^p] = 2^{-n}\sum_{x\in\{0,1\}^n} f(x)^p$, with the uniform weight $2^{-n}$ (written $(2^{-1})^n$). Distributing the constant $2^{-n}$ through the sum turns this into
\[
  \mathbb{E}[f^p] \;=\; \sum_{x\in\{0,1\}^n} 2^{-n}\, f(x)^p.
\]

4. **Match the sums termwise.** Both sides are now sums over $x\in\{0,1\}^n$ with the same summand up to the coefficient. For each fixed $x$ the hypothesis on $P$ says precisely that $P(\{x\}) = 2^{-n}$, so the term $P(\{x\})\,f(x)^p$ equals $2^{-n}\,f(x)^p$. Summing these equalities gives $\int f^p\,dP = \mathbb{E}[f^p]$, as claimed.
