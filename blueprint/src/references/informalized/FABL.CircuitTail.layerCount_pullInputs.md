<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/LMN.lean :: FABL.CircuitTail.layerCount_pullInputs -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Layer Count Under Input Pullback

**Claim.** Pulling each layer's input sets back along an injective map leaves a circuit tail's layer count unchanged.

**Proof.** Proceed by cases on the tail. For an output tail, pullback changes only the output layer's input set; its layer count is still $1$. For a layered tail, the pulled list of gates has the same length as the original list, and the remaining tail is only cast to the matching input type. Thus the outer layer still contributes $1$, and the remaining tail has the same layer count as before; adding these contributions proves the equality.
