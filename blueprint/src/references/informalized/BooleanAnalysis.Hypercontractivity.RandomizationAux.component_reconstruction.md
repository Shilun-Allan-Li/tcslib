<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Randomization/Basic.lean :: BooleanAnalysis.Hypercontractivity.RandomizationAux.component_reconstruction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reconstruction from components

**Claim.** At every outcome $x$, summing all coordinate components of $f$ gives $f(x)$.

**Proof.** Substitute the definition of each component into the sum over all coordinate sets. Reordering the resulting finite sums gives the signed powerset sum
\[
\sum_{S\subseteq [n]}\sum_{T\subseteq S}(-1)^{|S|-|T|}P.\mathrm{condExp}\,T f(x).
\]
The signed powerset identity says that this sum equals its summand function evaluated at the full set, so it is $P.\mathrm{condExp}\,[n] f(x)$ (\texttt{sum\_powerset\_signed\_sum}). Conditioning on every coordinate leaves the input unchanged: the function inside the expectation is constantly $f(x)$. Since the product masses sum to one, the expectation of this constant is $f(x)$ (\texttt{expect\_const}).

**Key facts.** `BooleanAnalysis.Hypercontractivity.RandomizationAux.sum_powerset_signed_sum`, `BooleanAnalysis.Hypercontractivity.FiniteProduct.expect_const`.
