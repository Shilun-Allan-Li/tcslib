<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedAnalysis.lean :: FABL.biasedExpectationPolynomial_biasMean -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Biased Expectation as a Product Mean

**Claim.** For $p\in[0,1]$, the biased expectation polynomial of $f$ at the bias mean $1-2p$ equals the product mean of $f$ under the biased sign distribution.

**Proof.** Let the product law be the product of the one-coordinate biased sign law. For each coordinate set $S$, its monomial has product mean $(1-2p)^{|S|}$ (`productMean_biasedSignPMF_monomial`). Thus each term in the biased expectation polynomial is the Fourier coefficient of $f$ multiplied by the product mean of that monomial. Linearity of expectation over the finite sum lets us combine these terms into the product mean of the function $x\mapsto\sum_S \widehat f(S)\,\chi_S(x)$. The Fourier expansion identity (`fourier_expansion`) identifies this sum pointwise with $f$, proving the equality.

**Key facts.** `FABL.productMean_biasedSignPMF_monomial`, `FABL.pmfExpectation_sum`, `FABL.pmfExpectation_const_mul`, `FABL.fourier_expansion`.
