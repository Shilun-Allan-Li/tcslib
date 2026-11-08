<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LayeredDAG.lean :: BoolCircuit.exists_gateShape -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Shapes of standard gate operations

**Claim.** If a Boolean gate operates by identity, unary negation, or conjunction of some arity, then its action can be represented by a wire, a negated wire, or a conjunction of a list of elements of its domain, respectively.

**Proof.** The allowed operations fall into three cases. If the operation is the identity on a single input, take the shape consisting of the wire fed by that input; its value is exactly the gate's output. If the operation is negation on one input, take the negated wire, whose value again agrees with the gate. In the remaining case the operation is a conjunction indexed by some finite arity. Take the list of the gate's inputs in that order and form their conjunction shape. Its evaluation is the product of the corresponding Boolean values, exactly the gate operation. Thus each allowed gate has a shape with the same value under every assignment.
