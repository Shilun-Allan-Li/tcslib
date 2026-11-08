<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedAnalysis.lean :: FABL.sum_productMean_biasedSignPMF_discreteDerivative -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Biased Derivative Sum and Fourier Coefficients

**Claim.** For $0<p<1$ and a real-valued function $f$ on the sign cube, the sum of the biased expectations of its coordinate derivatives equals the Fourier sum weighted by subset size and the corresponding power of the bias mean.

**Proof.** Apply the coordinatewise Fourier formula for the biased expectation of the derivative (`FABL.productMean_biasedSignPMF_discreteDerivative`). For each coordinate $i$, it expresses that expectation as a sum over subsets $S$ containing $i$, with summand $\widehat f(S)(1-2p)^{|S|-1}$. Interchange the finite sums to sum first over $S$. For a fixed $S$, the same summand occurs once for each of its $|S|$ coordinates; subsets of size zero contribute nothing. The result is $\sum_S |S|(1-2p)^{|S|-1}\widehat f(S)$, as asserted.

**Key facts.** `FABL.productMean_biasedSignPMF_discreteDerivative`.
