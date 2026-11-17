<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Randomization/Basic.lean :: BooleanAnalysis.Hypercontractivity.RandomizationAux.condExp_component -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Conditional expectation of a component

**Claim.** Conditioning the $S$-component over coordinates outside $J$ returns that component when $S\subseteq J$, and returns zero otherwise.

**Proof.** Expand the component as its signed sum of conditional expectations. Linearity of expectation moves this finite sum outside the outer conditional expectation (\texttt{expect\_sum\_mul}). Composing the two conditional expectations replaces the conditioning set by the intersection, so the result is
\[
\sum_{T\subseteq S}(-1)^{|S|-|T|}P.\mathrm{condExp}(T\cap J)f(x)
\]
(\texttt{condExp\_comp}). If $S\subseteq J$, then every $T\subseteq S$ also lies in $J$, hence $T\cap J=T$; the displayed sum is exactly the $S$-component. If $S\nsubseteq J$, the signed intersection sum cancels to zero (\texttt{signed\_intersection\_zero}).

**Key facts.** `BooleanAnalysis.Hypercontractivity.FiniteProduct.expect_sum_mul`, `BooleanAnalysis.Hypercontractivity.FiniteProduct.condExp_comp`, `BooleanAnalysis.Hypercontractivity.RandomizationAux.signed_intersection_zero`.
