<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StraightLine.lean :: BoolCircuit.SLOperand.Before.mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of the before relation

**Claim.** If an operand is before line $i$ and $i\le j$, then it is before line $j$.

**Proof.** Split according to the kind of operand. Input and negated-input operands are before every line by definition. For a line operand with index $r$, being before line $i$ means $r<i$. Since $i\le j$, transitivity gives $r<j$, which is exactly that the operand is before line $j$.
