<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedAnalysis.lean :: FABL.continuous_biasedMinusProbabilityPolynomial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Continuity of the biased minus-probability polynomial

**Claim.** For a Boolean-valued function on the sign cube, the function of $p$ given by $(1-P_f(1-2p))/2$ is continuous on $\mathbb R$.

**Proof.** The biased expectation is a finite sum, indexed by subsets of the finite cube, of terms of the form $(1-2p)^{|S|}\widehat f(S)$. Each term is a polynomial in $p$, hence continuous; their finite sum is continuous as well. Subtracting that sum from $1$ and dividing by $2$ preserves continuity, giving the stated function.
