<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Parity.lean :: FABL.eval_parityDepthCircuitFromBlocks -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth-Circuit Evaluation by Blocks

**Claim.** For every input sign vector, the depth circuit constructed from blocks evaluates to the corresponding parity-tree value at level $q+2$ and group zero.

**Proof.** The circuit's evaluation is the evaluation of its tail on the first-layer values, with the appropriate cast accounting for the first layer's indexed size. The cast does not alter the evaluation except to reindex the input values (`FABL.circuitTail_eval_cast`). The first-layer evaluation theorem identifies each such value with the corresponding bottom-layer value (`FABL.eval_parityFirstLayer`); the lengths of the first layer and the indexed layer agree (`FABL.length_parityFirstLayer`), so these pointwise values align. The resulting tail evaluation is exactly the parity-padded-tail evaluation, which equals the level-$(q+2)$ parity-tree value at group zero (`FABL.parityPaddedTail_eval`).

**Key facts.** `FABL.length_parityFirstLayer`, `FABL.circuitTail_eval_cast`, `FABL.eval_parityFirstLayer`, `FABL.parityPaddedTail_eval`.
