<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Randomization/Basic.lean :: BooleanAnalysis.Hypercontractivity.RandomizationAux.condExp_moment_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Conditional moment contraction

**Claim.** For $q\ge1$, the product expectation of $|E_Jf|^q$ is at most the product expectation of $|f|^q$.

**Proof.** Fix the coordinates in $J$. The conditional expectation is a weighted average over the remaining outcomes, with nonnegative weights summing to one. Convexity of $t\mapsto |t|^q$ gives that the $q$th absolute power of this average is at most the weighted average of the $q$th absolute powers (\texttt{weighted\_abs\_rpow\_sum\_le}). Multiply by the nonnegative mass of the fixed outcome and sum over it. The resulting iterated expectation of the conditioned function equals the expectation of $|f|^q$: swapping the two samples in the product expectation restores the original full sample, and averaging a constant over a probability distribution leaves it unchanged (\texttt{expect\_swap\_samples}, \texttt{expect\_const}).

**Key facts.** `BooleanAnalysis.Hypercontractivity.RandomizationAux.weighted_abs_rpow_sum_le`, `BooleanAnalysis.Hypercontractivity.FiniteProduct.expect_swap_samples`, `BooleanAnalysis.Hypercontractivity.FiniteProduct.expect_const`.
