<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGFanin.lean :: BoolCircuit.DAGCircuit.deMorgan_depth_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth of the De Morgan transformation

**Claim.** If every gate has distinct arguments and every NOT gate has exactly one argument, then the De Morgan transformed circuit has depth at most three times the depth of the original circuit.

**Proof.** The general rewrite depth theorem (`DAGCircuit.rewrite_depth_le`) bounds the depth after rewriting by $c$ times the original depth, provided each gate's replacement gadget increases depth according to the parameter $c$. For the De Morgan transformation, the gadget correctness theorem supplies this bound with $c=3$ (`deMorganGadget_correct`). The circuit's well-formedness and argument-count bound provide the hypotheses required for those gadgets. Applying the rewrite depth theorem therefore gives the desired factor-three estimate.

**Key facts.** `BoolCircuit.DAGCircuit.rewrite_depth_le`.
