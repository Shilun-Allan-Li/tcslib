<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Randomization/General.lean :: BooleanAnalysis.Hypercontractivity.randomization_condExp_average -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Average of masked randomizations

**Claim.** Averaging, over uniform Boolean strings, the conditional expectation of each masked randomization gives the product noise operator at rate \(1/2\).

**Proof.** Fix a Boolean string \(r\) and expand its randomization as a sum of components. Conditional expectation is linear across this finite sum (\(\texttt{FiniteProduct.expect\_sum\_mul}\)). A component indexed by \(S\) survives conditioning on the positive mask exactly when \(S\) is contained in that mask; otherwise its conditional expectation is zero (\(\texttt{RandomizationAux.condExp\_component}\)). Thus the conditional expectation is a sum whose coefficient for \(S\) is \(\chi_S(r)\) when \(S\) lies in the mask, and zero otherwise. Averaging this coefficient over \(r\) gives \((1/2)^{|S|}\) (\(\texttt{positiveMask\_coefficient\_expect}\)). Interchanging the finite sum and average, the resulting component sum is precisely the product noise expansion at rate \(1/2\).

**Key facts.** `BooleanAnalysis.Hypercontractivity.FiniteProduct.expect_sum_mul`, `BooleanAnalysis.Hypercontractivity.RandomizationAux.condExp_component`, `BooleanAnalysis.Hypercontractivity.positiveMask_coefficient_expect`, `BooleanAnalysis.expect_eq_fintypeExpect`.
