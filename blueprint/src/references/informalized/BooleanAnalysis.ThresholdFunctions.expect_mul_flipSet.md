<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/BitFlipSets.lean :: BooleanAnalysis.ThresholdFunctions.expect_mul_flipSet -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Formula for Flip Correlation

**Claim.** The uniform expectation of $f(x)f(x^S)$ is the sum over all subsets $T$ of $(-1)^{|T\cap S|}\widehat f(T)^2$.

**Proof.** Regard the left side as the inner product of $f$ with the function $x\mapsto f(x^S)$. Parseval's identity (BooleanAnalysis.plancherel) expresses this inner product as the sum, over $T$, of the product of the corresponding Fourier coefficients. The Fourier coefficient of the flipped function is $(-1)^{|T\cap S|}\widehat f(T)$ (BooleanAnalysis.ThresholdFunctions.fourierCoeff_comp_flipSet). Substituting this formula makes each product $(-1)^{|T\cap S|}\widehat f(T)^2$, as claimed.

**Key facts.** `BooleanAnalysis.plancherel`, `BooleanAnalysis.ThresholdFunctions.fourierCoeff_comp_flipSet`.
