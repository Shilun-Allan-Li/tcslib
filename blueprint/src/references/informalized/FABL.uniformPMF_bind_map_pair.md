<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevin/RestrictedWeights.lean :: FABL.uniformPMF_bind_map_pair -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product of uniform distributions

**Claim.** If $a$ is uniform on a finite nonempty set $\alpha$ and $b$ is independently uniform on a finite nonempty set $\beta$, then $(a,b)$ is uniform on $\alpha\times\beta$.

**Proof.** Compare the probabilities assigned to each pair $(a,b)$. In the bind-and-map construction, only the outer outcome equal to $a$ contributes to the probability of this pair, and within that outcome only the inner outcome equal to $b$ contributes. Their probabilities multiply to $|\alpha|^{-1}|\beta|^{-1}$. Since $|\alpha\times\beta|=|\alpha||\beta|$, this is exactly the uniform probability of the pair in the product set. Equality of these point probabilities proves equality of the distributions.
