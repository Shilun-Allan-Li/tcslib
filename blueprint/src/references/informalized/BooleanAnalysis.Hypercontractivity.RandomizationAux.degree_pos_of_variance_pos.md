<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Randomization/Basic.lean :: BooleanAnalysis.Hypercontractivity.RandomizationAux.degree_pos_of_variance_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive variance forces positive degree

**Claim.** If all components indexed by sets of size greater than $k$ vanish and $f$ has positive variance, then $k>0$.

**Proof.** Suppose instead that $k$ is not positive. Since $k$ is a natural number, it must be zero. Reconstruction expresses $f(x)$ as the sum of all its components (\texttt{component\_reconstruction}). Every nonempty coordinate set has positive cardinality, so under the degree hypothesis all its components vanish. The only remaining term is the component indexed by the empty set; its defining formula is the unconditional expectation of $f$, namely $P.\mathrm{expect}\,f$. Hence $f$ is constant. A constant function has zero variance, since its difference from its expectation vanishes everywhere and the product masses sum to one (\texttt{expect\_const}), contradicting the assumed positive variance. Therefore $k>0$.

**Key facts.** `BooleanAnalysis.Hypercontractivity.RandomizationAux.component_reconstruction`, `BooleanAnalysis.Hypercontractivity.FiniteProduct.expect_const`.
