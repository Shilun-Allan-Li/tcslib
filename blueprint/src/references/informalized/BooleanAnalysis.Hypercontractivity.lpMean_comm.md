<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Reverse/Basic.lean :: BooleanAnalysis.Hypercontractivity.lpMean_comm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Commutation of equal-exponent means

**Claim.** For $p>0$, taking uniform power means first over the one-bit variable and then over the $n$-bit variable gives the same result as taking them in the reverse order.

**Proof.** Since $p>0$, each power mean is the usual $p$-norm expression. The inner expectations of $|F|^p$ are nonnegative, so raising each inner mean to the $p$th power cancels the corresponding $1/p$ power. After this cancellation, both sides are the same overall $1/p$ power of the average of $|F(x,y)|^p$ over all pairs $(x,y)$. The finite double sum can be summed in either order, and the uniform weights factor as the product of the weights on the two cubes. Thus the two iterated means agree.

**Key facts.** `BooleanAnalysis.Hypercontractivity.lpMean_of_pos`, `BooleanAnalysis.expect_eq_fintypeExpect`.
