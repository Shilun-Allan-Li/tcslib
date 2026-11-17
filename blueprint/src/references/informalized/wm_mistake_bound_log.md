<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/MistakeBounds/WeightedMajority.lean :: wm_mistake_bound_log -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Logarithmic mistake bound

**Claim.** Under the stated potential inequality, the number of weighted-majority mistakes times $\log(2/(1+\beta))$ is at most $\log n+M^*\log(1/\beta)$.

**Proof.** The two sides of the assumed potential inequality are positive, so monotonicity of the logarithm gives $\log(\beta^{M^*})\le\log(n((1+\beta)/2)^{M_{\mathrm{WM}}})$. Expand the logarithm of the product and the logarithms of the powers to obtain $M^*\log\beta\le\log n+M_{\mathrm{WM}}\log((1+\beta)/2)$. Since $\log((1+\beta)/2)=-\log(2/(1+\beta))$ and $\log\beta=-\log(1/\beta)$, rearranging gives the claimed inequality.
