<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Randomization/Basic.lean :: BooleanAnalysis.Hypercontractivity.RandomizationAux.hasDegreeLE_sub_const -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree Bound Under Constant Subtraction

**Claim.** If all components of $f$ indexed by sets larger than $k$ vanish, then the same is true of $f-c$ for every real constant $c$.

**Proof.** Fix a set $S$ with $|S|>k$. Such an $S$ is nonempty, so it is not contained in the empty set. The component of the constant function with value $c$ is therefore zero: its conditional expectations are all $c$, and the alternating sum over subsets cancels by the signed intersection cancellation identity (`signed_intersection_zero`), with the expectation of a constant equal to that constant (`expect_const`). The component construction is linear in the function, so the $S$-component of $f-c$ is the component of $f$ minus that of the constant function. Both are zero, the first by hypothesis and the second by the cancellation just shown. Since this holds for every such $S$ and every input, the degree bound follows.

**Key facts.** `BooleanAnalysis.Hypercontractivity.FiniteProduct.expect_const`, `BooleanAnalysis.Hypercontractivity.RandomizationAux.signed_intersection_zero`.
