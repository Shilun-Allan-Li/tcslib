<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FourierCoefficientsOfMajority.lean :: FABL.sum_middleLayerIndicator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size of the middle layer

**Claim.** For each nonnegative integer $m$, the sum of the indicator over sign vectors of length $2m$ that have exactly $m$ positive coordinates is $\binom{2m}{m}$.

**Proof.** Identify each sign vector with the subset of coordinates on which it is positive. This is a bijection, and the associated subset has cardinality equal to the number of positive coordinates (\(\texttt{FABL.signCubeEquivFinset_apply_card}\)). Reindexing the sum therefore gives one for each subset of $[2m]$ of size $m$, and zero for every other subset. The sum counts precisely the size-$m$ subsets. There are \(\binom{2m}{m}\) such subsets, so the asserted identity follows.

**Key facts.** `FABL.signCubeEquivFinset_apply_card`.
