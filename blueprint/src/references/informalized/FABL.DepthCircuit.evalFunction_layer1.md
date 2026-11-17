<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/CircuitInfluence.lean :: FABL.DepthCircuit.evalFunction_layer1 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First-Layer Evaluation

**Claim.** Evaluating a circuit’s later layers on the functions computed by its first-layer gates gives exactly the function computed by the circuit.

**Proof.** At each input $x$, the first-layer function at an index $i$ returns the value of the circuit’s first-layer evaluation at $i$. Substituting these pointwise values into the tail’s function evaluation gives the tail evaluated on the circuit’s first-layer values, which is precisely the definition of the circuit’s computed function. The two functions therefore agree at every input.
