<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Basic.lean :: BoolCircuit.TreeCircuit.one_le_size -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive Circuit Size

**Claim.** Every Boolean circuit has size at least $1$.

**Proof.** A literal has size $1$. A gate has size $1$ plus a sum of child sizes, which is nonnegative, so its size is also at least $1$.
