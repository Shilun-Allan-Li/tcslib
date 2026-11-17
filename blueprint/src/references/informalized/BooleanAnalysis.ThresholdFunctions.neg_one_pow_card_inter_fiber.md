<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/BitFlipSets.lean :: BooleanAnalysis.ThresholdFunctions.neg_one_pow_card_inter_fiber -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parity Product Over a Color Class

**Claim.** The sign $(-1)$ raised to the size of the intersection of $T$ with the fiber of $j_0$ equals the product over all indices of the indicated signs, which are negative exactly when the index belongs to $T$ and maps to $j_0$.

**Proof.** In the product, factors outside $T$ are $1$, and for indices in $T$ the factor is $-1$ precisely when the index lies in the fiber of $j_0$. Thus the product has one factor of $-1$ for each element of $T\cap F_{j_0}(\pi)$ and is $1$ for every other index. It is therefore $(-1)^{|T\cap F_{j_0}(\pi)|}$.
