<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedAnalysis.lean :: FABL.hasDerivAt_biasedExpectationPolynomial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative of the biased expectation polynomial

**Claim.** For every real-valued function $f$ on the Boolean cube and real number $\mu$, the biased expectation polynomial is differentiable at $\mu$ with derivative $\sum_{S\subseteq[n]} |S|\mu^{|S|-1}\widehat f(S)$.

**Proof.** The polynomial is a finite sum, over subsets $S$, of terms $\mu^{|S|}\widehat f(S)$. Differentiate each term: its Fourier coefficient is constant in $\mu$, so the power rule and constant-multiple rule give derivative $|S|\mu^{|S|-1}\widehat f(S)$. The derivative of a finite sum is the sum of the derivatives, giving the stated formula.
