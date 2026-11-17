<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/BitFlipSets.lean :: BooleanAnalysis.ThresholdFunctions.sum_pi_sign -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parity sum over coordinate colorings

**Claim.** For positive $m$, the sum over all colorings $\pi$ of $(-1)^{|T\cap F_{j_0}(\pi)|}$ is $m^n(1-2/m)^{|T|}$.

**Proof.** For each coloring, express the sign as a product over coordinates: a coordinate contributes $-1$ exactly when it lies in $T$ and is colored $j_0$, and otherwise contributes $1$ (`neg_one_pow_card_inter_fiber`). Summing this product over all colorings factors into a product of independent sums, one for each coordinate. If a coordinate is outside $T$, its color has $m$ choices, each contributing $1$, so the factor is $m$. If it lies in $T$, one color contributes $-1$ and the other $m-1$ colors contribute $1$, giving $m-2=m(1-2/m)$. Multiplying the factors gives $m^n(1-2/m)^{|T|}$.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.neg_one_pow_card_inter_fiber`.
