<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Randomization/Basic.lean :: BooleanAnalysis.Hypercontractivity.RandomizationAux.condExp_residual_secondMoment -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Conditional residual second moment

**Claim.** The product expectation of $(f-E_Jf)^2$ equals the sum of squared-component expectations over coordinate sets not contained in $J$.

**Proof.** Apply Parseval to the function $g=f-E_Jf$, expressing its second moment as the sum of the second moments of its components (\texttt{parseval}). By linearity in the defining signed sums, the $S$-component of $g$ is the $S$-component of $f$ minus the $S$-component of $E_Jf$. The latter component equals the former when $S\subseteq J$ and vanishes otherwise (\texttt{component\_condExp}). In the first case the component of $g$ is zero; in the second it is the component of $f$. Substituting these two cases into Parseval gives exactly the asserted sum.

**Key facts.** `BooleanAnalysis.Hypercontractivity.FiniteProduct.parseval`, `BooleanAnalysis.Hypercontractivity.RandomizationAux.component_condExp`.
