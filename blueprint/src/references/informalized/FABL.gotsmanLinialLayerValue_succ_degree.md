<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GotsmanLinialExtremizer.lean :: FABL.gotsmanLinialLayerValue_succ_degree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Layer Product Recurrence

**Claim.** For all natural numbers $a,s,c$, the layer product with parameters $(a,s+1,c)$ equals the layer product with parameters $(a,s,c)$ multiplied by $2c-2a-2s-1$.

**Proof.** Writing the product over the first $s+1$ indices as the product over the first $s$ indices times its final factor, the new factor is the term at index $j=s$. Substituting $j=s$ gives $2c-2(a+s)-1$, which rearranges to $2c-2a-2s-1$.
