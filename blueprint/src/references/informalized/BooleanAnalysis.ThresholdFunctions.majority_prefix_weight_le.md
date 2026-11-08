<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/Majority.lean :: BooleanAnalysis.ThresholdFunctions.majority_prefix_weight_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cumulative Majority Fourier Weight Comparison

**Claim.** For every $j\leq2(m+1)+2$, the cumulative Fourier weight of majority on the cube of dimension $2(m+1)+1$ through levels below $j$ is at most the corresponding cumulative weight for majority on the cube of dimension $2m+1$.

**Proof.** First compare the weights level by level through level $2m+1$. At even levels both weights vanish (`majority_weightLevel_even`); at odd levels the larger majority has strictly smaller weight (`majority_weight_strictAnti`). If $j\leq2m+2$, summing these comparisons over the levels below $j$ proves the result.

If $j>2m+2$, the smaller majority's sum through levels below $j$ equals its total Fourier weight: all levels above its dimension have weight zero (`weightLevel_eq_zero_of_lt`), and its total is $1$ because it is $\{\pm1\}$-valued (`sum_weightLevel_eq_one`, using `majority_isPmOne`). The larger majority's sum over the same initial range is at most its total weight, since every level weight is nonnegative (`weightLevel_nonneg`). Its total is likewise $1$. Thus the desired comparison follows in this case as well.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.majority_weightLevel_even`, `BooleanAnalysis.ThresholdFunctions.majority_weight_strictAnti`, `BooleanAnalysis.ThresholdFunctions.weightLevel_eq_zero_of_lt`, `BooleanAnalysis.ThresholdFunctions.majority_isPmOne`, `BooleanAnalysis.ThresholdFunctions.sum_weightLevel_eq_one`, `BooleanAnalysis.ThresholdFunctions.weightLevel_nonneg`.
