<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPThreeQuery.lean :: FABL.localPrefixEmbedding_natAdd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Embedding of Appended Coordinates

**Claim.** The embedding from tuples of length $r+a$ into tuples of length $r+K$ sends an appended coordinate $i<a$ to the appended coordinate with index $i$, included into the larger block of length $K$.

**Proof.** The embedding preserves the initial block of length $r$ and includes the appended block of length $a$ into the appended block of length $K$. Therefore the appended coordinate indexed by $i$ maps to the appended coordinate with the same index, now viewed in the larger block.
