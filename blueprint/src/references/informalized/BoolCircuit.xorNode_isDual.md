<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Parity.lean :: BoolCircuit.xorNode_isDual -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complementarity after one XOR step

**Claim.** If the two circuits in each input pair evaluate to complementary values, then the two circuits in the pair produced by one XOR step also evaluate to complementary values.

**Proof.** Write $a$ and $b$ for the evaluations of the first circuits of the two input pairs. The assumptions make the partner evaluations $\neg a$ and $\neg b$. The first output evaluates to $(a\wedge\neg b)\vee(\neg a\wedge b)$, while the second evaluates to $(a\wedge b)\vee(\neg a\wedge\neg b)$. The first expression is true exactly when $a$ and $b$ differ; the second is true exactly when they agree. These two Boolean values are complements, as required.
