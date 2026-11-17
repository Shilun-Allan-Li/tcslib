<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/FormulaFanOut.lean :: BoolCircuit.unfoldGate_congr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Congruence of Gate Unfolding

**Claim.** For a well-formed gate, if two assignments give equal circuits at every argument of the gate and every polarity, then unfolding the gate using either assignment gives the same circuit at each polarity.

**Proof.** Write the gate as its kind together with its argument list, and consider the three kinds. For an AND gate, unfolding forms a node whose children are the assigned circuits at each argument with the chosen polarity. The assumed pointwise equalities make the two corresponding child lists equal, hence the resulting nodes agree. For an OR gate the children are again taken at the chosen polarity, while the node records the opposite polarity; the same childwise argument gives equality. For a NOT gate, well-formedness says that its argument list has exactly one element, say $a$. The unfolding therefore selects $a$ and uses the opposite polarity in both constructions, so the hypothesis at $a$ gives equality.
