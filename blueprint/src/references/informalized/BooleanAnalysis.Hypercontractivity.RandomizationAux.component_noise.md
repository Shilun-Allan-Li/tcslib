<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Randomization/Basic.lean :: BooleanAnalysis.Hypercontractivity.RandomizationAux.component_noise -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Noise multiplier on components

**Claim.** For every coordinate set $S$ and outcome $x$, the $S$-component of the noise transform of $f$ is $[?]$ times the $S$-component of $f$, namely $[?]$.

**Proof.** Expand the noise transform inside the definition of the component. Linearity of product expectation moves its finite sum outside the expectation, and interchanging the two finite sums gives
\[
P.\mathrm{component}\,S(P.\mathrm{noise}\,\rho\,f)(x)=\sum_T \rho^{|T|}P.\mathrm{component}\,S(P.\mathrm{component}\,T f)(x).
\]
Here the expectation of a finite weighted sum is the corresponding weighted sum of expectations (\texttt{expect\_sum\_mul}). Each inner component is zero unless $S=T$, in which case it is the $S$-component of $f$ (\texttt{component\_component}). Thus only the term $T=S$ remains, giving $\rho^{|S|}P.\mathrm{component}\,S f(x)$.

**Key facts.** `BooleanAnalysis.Hypercontractivity.FiniteProduct.expect_sum_mul`, `BooleanAnalysis.Hypercontractivity.RandomizationAux.component_component`.
