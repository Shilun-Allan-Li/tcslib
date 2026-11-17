<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StrictCircuit.lean :: BoolCircuit.fanoutIn_last_eq_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero fan-out at the circuit boundary

**Claim.** In an acyclic list of gates on $n$ input vertices, if $n+|gs|\le v+1$, then vertex $v$ has zero fan-out in the list.

**Proof.** Suppose some gate reads $v$, and let $i<|gs|$ be its position. Acyclicity gives $v<n+i$. Since $i<|gs|$, we have $n+i<n+|gs|$, and the hypothesis gives $n+|gs|\le v+1$. Thus $v<n+i<v+1$, which is impossible for natural numbers. So no gate reads $v$, and its fan-out is zero.
