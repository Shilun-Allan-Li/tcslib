<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StraightLineSmall.lean :: BoolCircuit.SLOperand.lit_before -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Literals precede every program line

**Claim.** For any input index $k\in\mathrm{Fin}(n)$, Boolean sign $b$, and natural number $i$, the operand representing $x_k$ when $b$ is true and $\neg x_k$ when $b$ is false precedes line $i$.

**Proof.** By definition, the literal operand is either the input operand or the negated-input operand, according to the sign $b$. Both kinds are before every line by the definition of the before relation. Therefore the literal operand is before line $i$.
