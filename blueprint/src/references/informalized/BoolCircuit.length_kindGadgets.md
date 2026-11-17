<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyProgram.lean :: BoolCircuit.length_kindGadgets -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Number of kind gadgets

**Claim.** For any chosen kind $\kappa_0$, the list of associated gadgets has length $w$.

**Proof.** By definition, the list of kind gadgets is obtained by mapping a construction over the indices in `List.range w`. A range of length $w$ has exactly $w$ elements, and mapping preserves list length. Thus the gadget list has length $w$.
