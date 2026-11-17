<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevin/RestrictedWeights.lean :: FABL.uniformPMF_bind_bind_map_triple -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Three independent uniform samples

**Claim.** Three independent uniform samples from a finite nonempty set $\alpha$ have joint distribution uniform on $\alpha\times\alpha\times\alpha$.

**Proof.** Fix the first sample $a$. The second and third samples, drawn independently and uniformly from $\alpha$, form a uniform pair on $\alpha\times\alpha$ by the product rule for uniform distributions (\texttt{uniformPMF\_bind\_map\_pair}). Attaching the fixed coordinate $a$ to that pair transports this distribution to the law of $(a,(b,c))$. Now sample $a$ uniformly as well. Applying the same product rule to the uniform law on $\alpha$ and the uniform law on $\alpha\times\alpha$ shows that the resulting triple is uniform on $\alpha\times(\alpha\times\alpha)$, as claimed.

**Key facts.** `FABL.uniformPMF_bind_map_pair`.
