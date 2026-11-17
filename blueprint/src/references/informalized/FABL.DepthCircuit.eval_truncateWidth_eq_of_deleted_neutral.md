<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/LMN.lean :: FABL.DepthCircuit.eval_truncateWidth_eq_of_deleted_neutral -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Neutral Deleted Gates Preserve Evaluation

**Claim.** If every omitted first-layer gate evaluates at $x$ to the neutral value for the dual gate type, then truncating the circuit to first-layer gates of width at most $w$ preserves its value at $x$.

**Proof.** By the evaluation formula for width truncation (`eval_truncateWidth`), the truncated circuit is evaluated by feeding the original tail an assignment that uses the original values on retained indices and the dual gate’s neutral value elsewhere. Fix an original first-layer index $j$. If $j$ lies in the embedding’s image, injectivity of the embedding’s extension shows that the extended assignment at $j$ is the original gate value there. If it does not lie in the image, then $j$ is omitted: indeed, any retained index whose image were $j$ would contradict this case, and every retained index has an image in the embedding. The hypothesis therefore says the original gate value at $j$ is the same neutral value used by the extension. Thus the extended assignment agrees everywhere with the original first-layer evaluation, so the original tail produces the original circuit’s value.

**Key facts.** `FABL.DepthCircuit.eval_truncateWidth`, `FABL.DepthCircuit.retainedLayer1Embedding_equivFin`.
