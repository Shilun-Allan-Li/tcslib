<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Reverse/Basic.lean :: BooleanAnalysis.Hypercontractivity.lpMean_collapse_last -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Collapse of the last-coordinate power mean

**Claim.** For $p>0$, the uniform power mean of a function on the $(n+1)$-bit cube equals the uniform power mean over the first $n$ bits of its two-value power mean in the last bit.

**Proof.** Because $p>0$, the power mean agrees with the usual expression $(\mathbb E|f|^p)^{1/p}$, both for the full function and for each inner two-point mean. For fixed first $n$ coordinates, the inner mean is nonnegative. Raising it to the $p$th power cancels the outer exponent $1/p$, leaving the average over the last bit of $|f|^p$. The identity that collapses the full-cube expectation into the average of these last-bit expectations then identifies the two expressions. Explicitly, the last bit has exactly two values, false and true, each of weight $1/2$, so its average is their arithmetic mean.

**Key facts.** `BooleanAnalysis.Hypercontractivity.lpMean_of_pos`, `BooleanAnalysis.Hypercontractivity.norm_collapse_rpow`, `BooleanAnalysis.expect_eq_fintypeExpect`.
