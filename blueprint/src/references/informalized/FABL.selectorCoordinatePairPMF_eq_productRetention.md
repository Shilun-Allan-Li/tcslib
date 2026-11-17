<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductLTFNoiseCorrection.lean :: FABL.selectorCoordinatePairPMF_eq_productRetention -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Selector Law as Product Retention

**Claim.** For a finite type $\Omega$, a probability mass function $\pi$ on it, and $\theta\in[-1,1]$, the pair distribution produced by selecting between two independent $\pi$-distributed values with a correlated sign pair equals the distribution obtained by drawing the first value from $\pi$ and retaining it in the second coordinate with probability $(1+\theta)/2$, otherwise drawing independently from $\pi$.

**Proof.** The retention parameter $(1+\theta)/2$ lies in $[0,1]$ (`selectorRetention_mem_Icc`), so the product-retention distribution in the claim is defined. The proof compares the two probability mass functions at each pair $z\in\Omega\times\Omega$. It uses the selector-pair expectation identity (`pmfExpectation_selectorCoordinatePairPMF`) with the indicator function of the singleton $\{z\}$. The expectation of this indicator under a probability mass function is its mass at $z$; hence the identity says the two distributions assign the same mass to every pair. Equality of all point masses gives equality of the distributions.

**Key facts.** `FABL.selectorRetention_mem_Icc`, `FABL.pmfExpectation_selectorCoordinatePairPMF`.
