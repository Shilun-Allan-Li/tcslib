<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PairEncode.lean :: BoolCircuit.DAGCircuit.pairEncode_isFaninTwo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pair encoding preserves fan-in two

**Claim.** If $C$ has distinct input vertices at every gate, each NOT gate has exactly one input, and every gate has at most two inputs, then wiring $C$ to the pair encoding preserves all three properties.

**Proof.** Apply the structural theorem for input buffering (`DAGCircuit.bufferInputs_structure`) to $C$ and the wiring map `pairWiring n r`. Its middle conclusion says that the buffered circuit is fan-in two, which by definition includes well-formedness (distinct arguments and the required NOT-gate arity) and the bound of two on every gate's number of inputs. The pair-encoded circuit is precisely this buffered circuit, so it has the stated properties.

**Key facts.** `BoolCircuit.DAGCircuit.bufferInputs_structure`.
