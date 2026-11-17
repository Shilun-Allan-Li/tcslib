<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/FanOut.lean :: BoolCircuit.fanoutIn_eq_zero_of_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero fan-out beyond the circuit

**Claim.** If an acyclic gate list on $n$ input vertices satisfies the condition that gate $i$ reads only vertices below $n+i$, then any vertex $v$ with $n+|G|\le v$ has zero fan-out in the list.

**Proof.** It suffices to show that no gate in the list reads $v$. If a gate did, choose its position $i$, where $i<|G|$. Acyclicity says that every argument of this gate is less than $n+i$. Since $i<|G|$, we have $n+i<n+|G|\le v$, contradicting that the gate reads $v$. Thus no gate is counted in the fan-out, which is zero.
