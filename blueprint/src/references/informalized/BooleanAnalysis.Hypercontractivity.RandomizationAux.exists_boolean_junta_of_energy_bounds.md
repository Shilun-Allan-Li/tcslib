<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Randomization/Basic.lean :: BooleanAnalysis.Hypercontractivity.RandomizationAux.exists_boolean_junta_of_energy_bounds -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Boolean Junta Approximation

**Claim.** Under the stated tail and low-degree energy bounds, there is a Boolean function depending only on coordinates in $J$ whose disagreement probability with $f$ is at most $a+b$.

**Proof.** Take the conditional expectation of $f$ given the coordinates in $J$. It depends only on those coordinates: if two inputs agree on $J$, the integrands defining their conditional expectations agree at every outcome. The residual second moment identity ( `condExp_residual_secondMoment`) expresses the expected squared difference between $f$ and this conditional expectation as the sum of component energies over sets not contained in $J$. Split these sets into those of size greater than $k$ and those of size at most $k$. Each component energy is nonnegative, so the residual sum is bounded by the sum of the two given energy sums, hence by $a+b$. Finally, the Boolean rounding result (`exists_boolean_rounding`) gives a Boolean function depending only on $J$ whose disagreement probability is at most this residual second moment. Combining the bounds proves the claim.

**Key facts.** `BooleanAnalysis.Hypercontractivity.RandomizationAux.condExp_residual_secondMoment`, `BooleanAnalysis.Hypercontractivity.FiniteProduct.exists_boolean_rounding`.
