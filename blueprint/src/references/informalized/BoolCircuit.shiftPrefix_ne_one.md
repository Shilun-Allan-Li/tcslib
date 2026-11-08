<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StrictCircuit.lean :: BoolCircuit.shiftPrefix_ne_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Avoiding the first shifted position

**Claim.** The prefix shift $f_n(v)$ is not equal to $n+1$.

**Proof.** Apply the general avoidance result with $k=1$. Since $1<3$, it says directly that $f_n(v)\ne n+1$.

**Key facts.** `BoolCircuit.shiftPrefix_ne`.
