<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StrictCircuit.lean :: BoolCircuit.strictGate_args -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Inputs of a strictified gate

**Claim.** Each input vertex of the strictified gate is either the shifted image of an original input vertex or one of $n+1$ and $n+2$.

**Proof.** Inspect the gate’s kind and the length of its input list. Empty AND and OR gates are replaced by gates whose inputs are exactly $n+1,n+2$. A one-input AND or OR gate retains the shifted original input and adds, respectively, $n+1$ or $n+2$. In all other cases the original input list is mapped through the shift, so each resulting input is the shifted image of an original one. These cases exhaust the definition of strictification.
