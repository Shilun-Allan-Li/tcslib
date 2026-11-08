<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean :: BoolCircuit.GatesAcyclic.snoc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acyclicity under appending a gate

**Claim.** If every source of gate $g_i$ in an ordered list of $r$ gates has index less than $n+i$, and every source of a further gate $g$ has index less than $n+r$, then appending $g$ preserves this property.

**Proof.** Consider a position in the appended list. If it is less than the original length $r$, its gate and position are unchanged, so the original acyclicity assumption supplies the required bound. The only other position is the new final position $r$, whose gate is $g$; its sources have index less than $n+r$ by hypothesis. This proves the condition at every position.
