<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/LMN.lean :: FABL.CircuitTail.eval_pullInputs -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation After Pulling Back Inputs

**Claim.** Pulling a circuit tail's inputs back along an injective map and evaluating it gives the same result as evaluating the original tail with the specified values on the image and the gate's neutral sign outside the image.

**Proof.** Split according to whether the tail is an output or a layered tail. For an output, the claim is exactly the fact that evaluating a gate on the preimage of an input set equals evaluating it on the original set after extending the assigned values by the gate's neutral sign (the neutral-sign extension property, `FABL.CircuitGate.evalFinset_embeddingPreimage_extend`). For a layered tail, unfold the pulled-back layer and its evaluation. The remaining tail has its input indices cast to the length of the mapped gate list; evaluation is unchanged by that cast (`FABL.CircuitTail.eval_castInput`). Each gate in the pulled-back list is the preimage of the corresponding original input set, so the same neutral-sign extension property identifies its value with the original gate's value under the extended assignment. These pointwise identifications give the desired equality for the layered tail.

**Key facts.** `FABL.CircuitGate.evalFinset_embeddingPreimage_extend`, `FABL.CircuitTail.eval_castInput`.
