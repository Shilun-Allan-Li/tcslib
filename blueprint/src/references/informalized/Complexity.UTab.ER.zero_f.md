<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitter.lean :: Complexity.UTab.ER.zero_f -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinates of the Zero Record

**Claim.** The coordinate function of the zero record assigns $0$ to every slot from $0$ through $10$.

**Proof.** The zero record has every field equal to $0$. Evaluating its coordinate function at any slot therefore gives the corresponding field, hence $0$. Since this holds at each of the eleven slots, the coordinate function is the constant-zero function.
