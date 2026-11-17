<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauCircuit.lean :: BoolCircuit.copyGate_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Copy gate evaluation

**Claim.** For any natural number $v$ and Boolean list $\mathrm{vals}$, the gate that copies the value at index $v$ evaluates to $\mathrm{vals}[v]$, with the value taken to be false when the list has no entry at that index.

**Proof.** The copy gate is labelled AND and has the single argument $v$. Evaluating an AND gate on this one-element argument list returns the conjunction of its sole value, namely the list entry at index $v$, using false as the default if that entry is absent. A conjunction of one Boolean is that Boolean, giving the stated value.
