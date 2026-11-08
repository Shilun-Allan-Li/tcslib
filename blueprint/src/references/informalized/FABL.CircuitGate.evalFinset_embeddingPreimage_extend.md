<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/LMN.lean :: FABL.CircuitGate.evalFinset_embeddingPreimage_extend -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation Under Coordinate Embedding

**Claim.** Extending the sign assignment by the gate’s neutral sign outside an injective coordinate map makes evaluation on a set of larger coordinates agree with evaluation on its preimage.

**Proof.** Consider the two gate cases. For AND, the evaluation is $-1$ exactly when every selected coordinate has value $-1$. Each coordinate in the image of the embedding corresponds to a unique smaller coordinate, and membership in the preimage is equivalent to membership of its image in the original set (the membership characterization of `embeddingPreimage`, `FABL.mem_embeddingPreimage`). At coordinates outside the image, the extension assigns $-1$, the neutral value for AND, so these coordinates do not change the condition. Hence the all-$-1$ conditions on the preimage and on the larger set agree. For OR, evaluation is $-1$ exactly when some selected coordinate has value $-1$. A witness in the preimage maps to such a witness in the larger set; conversely, a witness in the larger set either lies in the image and comes from a smaller coordinate, or lies outside it. In the latter case its extended value is $1$, so it cannot be a witness. Thus the existence conditions agree. In both cases, the gate evaluations themselves agree because they are determined by these respective conditions.

**Key facts.** `FABL.mem_embeddingPreimage`.
