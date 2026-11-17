<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/AdderLanguage.lean :: BoolCircuit.adderFamily_hasFaninTwo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Adder Family Fan-In Bound

**Claim.** Every circuit in the adder family is well formed, with distinct input vertices at each gate and exactly one input at each negation gate, and every gate has at most two inputs.

**Proof.** Fix an input length $n$. The family definition splits into the adder circuit case and the constant-circuit case. In the first case, the adder circuit has the required well-formedness and fan-in bound (`BoolCircuit.adderCircuit_isFaninTwo`). In the second, the constant circuit has those same properties (`BoolCircuit.constCircuit_isFaninTwo`). Hence the required conditions hold for every member of the family.

**Key facts.** `BoolCircuit.adderCircuit_isFaninTwo`, `BoolCircuit.constCircuit_isFaninTwo`.
