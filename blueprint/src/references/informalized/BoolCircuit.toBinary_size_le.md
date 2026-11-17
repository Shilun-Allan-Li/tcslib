<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/TreeNCAC.lean :: BoolCircuit.toBinary_size_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size bound for binary conversion

**Claim.** For every circuit tree $c$, the size of its binary conversion is at most three times the size of $c$.

**Proof.** The preceding stronger estimate (toBinary_size_succ_le) states that the converted size plus one is at most three times the original size. Since a natural number is at most its successor, the converted size itself is also at most three times the original size.

**Key facts.** `BoolCircuit.toBinary_size_succ_le`.
