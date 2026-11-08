<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyProgram.lean :: BoolCircuit.progBase_mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of Program Bases

**Claim.** For $i\le i'$, the program base at $i$ is at most the program base at $i'$.

**Proof.** The base is $n+2$ plus the sum of instruction widths among the first $i$ instructions. Since $i\le i'$, write $i'=i+d$ for some $d\ge0$. The first $i'$ instructions consist of the first $i$ followed by a further segment. After mapping instructions to their nonnegative widths, the sum over the longer prefix is the sum over the first prefix plus the sum over that additional segment. The latter is nonnegative, so the prefix sum, and hence the base, cannot decrease.
