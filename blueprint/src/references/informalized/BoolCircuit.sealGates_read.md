<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StrictSize.lean :: BoolCircuit.sealGates_read -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Readability after gate sealing

**Claim.** If every eligible vertex other than the output and the indices to be sealed is read in the original gate list, then after sealing, every vertex below the new endpoint other than the new output is read in the resulting gate list.

**Proof.** Induct on the list of indices to seal. With no indices to seal, the claim is the assumed readability of the original list. For the inductive step, write $N=n+|G|$ and first append the sealing triple for the head $u$. The enlarged list has length $|G|+3$, and the triple is valid because $u<N$ and the old output $o<N$. Apply the induction hypothesis to the tail of the list, using the enlarged gate list and its new output $N+2$.

To check its readability premise, consider a vertex $v$ below the enlarged endpoint. Fanout splits as the sum of fanout in the old list and in the appended triple (`fanoutIn_append`), while the triple reads $u$ twice, $N$ once, $o$ once, and $N+1$ once (`fanoutIn_sealTriple`). If $v<N$ and is neither $o$ nor $u$, then it is not among the indices still to be sealed, so the original readability assumption says it is read already in $G$. If $v=u$, the triple itself reads it. If $v=o$, it is the new triple's AND gate that reads it. For $v\ge N$, the old list has no reads there by the bound on its indices; among these new vertices, $N$ and $N+1$ are read by the triple, while the remaining cases needed as premises are handled by the updated endpoint and output exclusions. Thus every vertex required by the induction hypothesis is read in the enlarged list, and the result follows.

**Key facts.** `BoolCircuit.fanoutIn_append`, `BoolCircuit.fanoutIn_sealTriple`.

**Caveat.** The final case split in the supplied proof uses arithmetic and endpoint/output exclusions to rule out the remaining indices at or above $N$; the payload does not include a separate statement of the relevant endpoint arithmetic.
