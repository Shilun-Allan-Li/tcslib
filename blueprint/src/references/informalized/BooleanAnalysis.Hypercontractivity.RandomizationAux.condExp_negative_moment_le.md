<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Randomization/Basic.lean :: BooleanAnalysis.Hypercontractivity.RandomizationAux.condExp_negative_moment_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Conditional reflected-moment contraction

**Claim.** Under the stated scalar inequality and bounds on $q$ and $c$, the product expectation of $|E_Jf-c(f-E_Jf)|^q$ is at most that of $|f|^q$.

**Proof.** First average the target expression over a second sample in the coordinates outside $J$. Swapping the two samples shows that this does not change its product expectation; averaging a constant over a probability distribution leaves it unchanged (\texttt{expect\_swap\_samples}, \texttt{expect\_const}). In this two-sample expression, $E_Jf$ is unchanged when the coordinates outside $J$ are varied, since it depends only on the coordinates in $J$. Thus the conditional value at the mixed outcome equals its value at the fixed sample. For each fixed sample, apply the weighted reflected-moment inequality: with the conditional mean as the average, the assumed scalar inequality and $0<q$, $0\le c\le1$ bound the weighted average of $|E_Jf-c(f-E_Jf)|^q$ by the weighted average of $|f|^q$ (\texttt{weighted\_negative\_moment\_le}). Sum over the fixed samples, multiplying by their nonnegative masses. Finally, swapping samples again identifies the resulting iterated expectation of the conditioned $|f|^q$ with the full product expectation of $|f|^q$ (\texttt{expect\_swap\_samples}).

**Key facts.** `BooleanAnalysis.Hypercontractivity.FiniteProduct.expect_swap_samples`, `BooleanAnalysis.Hypercontractivity.FiniteProduct.expect_const`, `BooleanAnalysis.Hypercontractivity.RandomizationAux.weighted_negative_moment_le`.
