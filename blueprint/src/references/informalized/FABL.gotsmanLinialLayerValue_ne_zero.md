<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GotsmanLinialExtremizer.lean :: FABL.gotsmanLinialLayerValue_ne_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonvanishing of the Layer Product

**Claim.** For all natural numbers $a,k,c$, the product $\prod_{j=0}^{k-1}(2c-2(a+j)-1)$ is nonzero.

**Proof.** A finite product is nonzero if each factor is nonzero. If a factor vanished, then the corresponding integer expression $2c-2(a+j)-1$ would be zero, by equality of the real and integer expressions. But this would assert that an even integer equals an odd integer, which is impossible. Hence every factor is nonzero, and so is the product; for $k=0$ the empty product is $1$.
