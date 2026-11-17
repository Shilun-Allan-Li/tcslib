<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/LMN.lean :: FABL.mem_embeddingPreimage -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Embedding preimage membership

**Claim.** An index belongs to the embedding preimage of $A$ exactly when its image under the embedding belongs to $A$.

**Proof.** The embedding preimage is defined by filtering all indices in the domain to retain those whose images lie in $A$. Since $i$ is already an index in the domain, membership is equivalent to the filter condition $e(i)\in A$.
