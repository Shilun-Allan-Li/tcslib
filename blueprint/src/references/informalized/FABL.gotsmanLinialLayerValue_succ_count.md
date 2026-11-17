<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GotsmanLinialExtremizer.lean :: FABL.gotsmanLinialLayerValue_succ_count -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Layer Product Count Recurrence

**Claim.** For natural numbers $a,s,c$, the layer product with parameters $(a,s+1,c+1)$ equals $2c-2a+1$ times the layer product with parameters $(a,s,c)$.

**Proof.** In the product with parameters $(a,s+1,c+1)$, separate the final factor indexed by $s$. That factor simplifies to $2c-2a+1$. For every earlier index $j<s$, the factor $2(c+1)-2(a+j)-1$ simplifies to $2c-2(a+j)-1$, which is precisely the corresponding factor in the product with parameters $(a,s,c)$. Multiplying the separated factor by the remaining product proves the recurrence.
