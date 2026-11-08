<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPConstructions.lean :: FABL.mem_propertyIndexSet -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Property Index Set Membership

**Claim.** The index assigned to a Boolean string belongs to the set of indices for strings satisfying $P$ if and only if that string satisfies $P$.

**Proof.** The property index set is formed by filtering all indices according to whether the string decoded from that index satisfies $P$. For the index assigned to $w$, decoding returns $w$, since the encoding is an equivalence. Thus the filter condition is exactly $P(w)$.
