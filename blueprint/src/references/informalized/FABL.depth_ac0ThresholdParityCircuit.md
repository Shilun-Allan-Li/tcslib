<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/AC0ThresholdParitySeparation.lean :: FABL.depth_ac0ThresholdParityCircuit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth of the threshold parity circuit

**Claim.** For every integer $m\ge 7$, the constructed circuit on $2^m$ inputs has depth exactly $3$.

**Proof.** The circuit's depth is one plus the layer count of its tail. Its tail is formed by casting a two-layer tail consisting of a middle layer followed by the output layer; casting along an equality of layer sizes preserves the layer count. The first layer has length equal to the block layer size, so this cast is well-typed, and the underlying two-layer tail has layer count $2$. Thus the circuit depth is $1+2=3$.

**Key facts.** `FABL.circuitTail_layerCount_cast`, `FABL.length_blockFirstLayer`.
