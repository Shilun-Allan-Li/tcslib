<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StrictCircuit.lean :: BoolCircuit.shiftPrefix_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of the prefix shift

**Claim.** The map that fixes numbers below $n$ and adds three to numbers at least $n$ is injective.

**Proof.** Suppose two numbers have the same image. If both are below $n$, their images equal the numbers themselves, so they are equal. If both are at least $n$, adding three to each preserves equality, so they are equal. The two mixed cases are impossible: an unchanged number below $n$ is strictly less than $n$, whereas a shifted number from at least $n$ is at least $n+3$. Thus equal images imply equal inputs.
