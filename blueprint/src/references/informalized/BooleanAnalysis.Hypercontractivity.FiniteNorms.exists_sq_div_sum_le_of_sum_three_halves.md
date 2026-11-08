<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/Norms.lean :: BooleanAnalysis.Hypercontractivity.FiniteNorms.exists_sq_div_sum_le_of_sum_three_halves -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Large term from a three-halves sum

**Claim.** Given nonnegative $a_i$ with positive total sum and a nonnegative $A$ bounded by $\sum_i a_i^{3/2}$, some term $a_i$ is at least $\left(A/\sum_j a_j\right)^2$.

**Proof.** Choose an index $i$ where $a_i$ is maximal; such an index exists because the finite set is nonempty, as its sum is positive. For each $j$, nonnegativity gives $a_j^{3/2}=a_j\sqrt{a_j}$, and maximality implies $\sqrt{a_j}\le\sqrt{a_i}$. Thus $a_j^{3/2}\le a_j\sqrt{a_i}$. Summing and using the bound on $A$ yields $A\le(\sum_j a_j)\sqrt{a_i}$. Divide by the positive sum to obtain $A/\sum_j a_j\le\sqrt{a_i}$. Both sides are nonnegative, so squaring preserves the inequality and gives the conclusion.
