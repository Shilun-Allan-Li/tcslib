<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyProgram.lean :: BoolCircuit.faninTwo_progGates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fan-in of program gates

**Claim.** For every number of program steps, each gate in the resulting circuit has distinct input vertices, every NOT gate has exactly one input, and each gate has at most two inputs.

**Proof.** Proceed by induction on the number of program steps. At zero steps, the circuit consists of the two constant gates; each has no arguments, so all three properties hold. For the successor step, the circuit is the concatenation of the circuit from the preceding step and the embedding of the gadgets for the next instruction. A gate in the first part satisfies the claim by the induction hypothesis. For a gate in the embedded part, apply the fan-in preservation result for embedding a list of circuits (BoolCircuit.faninTwo_embedAll): it is enough that each circuit in the gadget list is well formed and has fan-in at most two. Each gadget is obtained from a Boolean function by the construction whose fan-in property is established by BoolCircuit.gadget_isFaninTwo. The gadget list is formed by mapping over the output indices, so every circuit in it has that property. This proves the claim for the successor circuit.

**Key facts.** `BoolCircuit.faninTwo_embedAll`, `BoolCircuit.gadget_isFaninTwo`.
