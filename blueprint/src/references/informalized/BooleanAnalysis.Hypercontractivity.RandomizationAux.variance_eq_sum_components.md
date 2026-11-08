<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Randomization/Basic.lean :: BooleanAnalysis.Hypercontractivity.RandomizationAux.variance_eq_sum_components -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Variance Decomposition

**Claim.** The variance is the sum of the expected squared components over all nonempty coordinate subsets.

**Proof.** First expand the square in the definition of variance and use linearity of expectation. The expectation of a constant is that constant, and expectation pulls out a constant factor (`expect_const`, `expect_const_mul`), yielding $\operatorname{Var}_P(f)=\mathbb E_P[f^2]-(\mathbb E_P f)^2$. Next apply Parseval's identity (`parseval`) to express $\mathbb E_P[f^2]$ as the sum of all component energies. The empty-set component is the constant function with value $\mathbb E_P f$, so its energy is $(\mathbb E_P f)^2$. Separating this term from the other components and subtracting it leaves precisely the sum over nonempty sets.

**Key facts.** `BooleanAnalysis.Hypercontractivity.FiniteProduct.expect_const`, `BooleanAnalysis.Hypercontractivity.FiniteProduct.expect_const_mul`, `BooleanAnalysis.Hypercontractivity.FiniteProduct.parseval`.
