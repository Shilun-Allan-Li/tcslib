<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/BitFlipSets.lean :: BooleanAnalysis.ThresholdFunctions.flipDisagreement_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Formula for Flip Disagreement

**Claim.** For a function taking values in $\{-1,1\}$, its flip disagreement on a set $S$ equals half of one minus the Fourier sum weighted by $(-1)^{|T\cap S|}$.

**Proof.** At each point, the two values $f(x)$ and $f(x^S)$ are signs. Thus $(f(x)-f(x^S))^2/4$ equals $0$ when they agree and $1$ when they differ; equivalently it is $1/2-(1/2)f(x)f(x^S)$. Take expectations and use linearity, the expectation of a constant, and constant scaling to obtain one half of one minus the expectation of the product. The Fourier identity for the correlation with a flipped input (`expect_mul_flipSet`) expresses that product expectation as $\sum_T(-1)^{|T\cap S|}\widehat f(T)^2$. Substitution gives the formula.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.expect_add`, `BooleanAnalysis.ThresholdFunctions.expect_const`, `BooleanAnalysis.ThresholdFunctions.expect_const_mul`, `BooleanAnalysis.ThresholdFunctions.expect_mul_flipSet`.
