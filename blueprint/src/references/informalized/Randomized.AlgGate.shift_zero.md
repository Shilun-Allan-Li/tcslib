<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPReduce.lean :: Randomized.AlgGate.shift_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Identity of the Zero Shift

**Claim.** For every $n$, shifting an algebraic gate by offset zero leaves it unchanged; the zero-shift function is the identity on gates.

**Proof.** It suffices to check each gate constructor. Variables and the constant are unchanged by definition. In an addition, subtraction, or multiplication gate, shifting by zero replaces each node index $j$ by $j+0=j$, so the gate is unchanged. Thus the zero-shift function agrees with the identity on every gate.
