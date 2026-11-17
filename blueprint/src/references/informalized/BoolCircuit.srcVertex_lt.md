<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyProgram.lean :: BoolCircuit.srcVertex_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Source vertices precede their instruction block

**Claim.** For every program index at most the program length and every bit source, its assigned vertex is strictly below the base of that instruction block.

**Proof.** The base is at least $n+2$, since it is $n+2$ plus a sum of nonnegative widths. Now split according to whether the source is valid. For a valid input source, its index is below $n$, hence below the base. A valid constant is assigned either $n$ or $n+1$, and both are below the base. For a valid reference to an earlier instruction $i'$, validity gives $i'<i$ and an output position $j<w$. The earlier block’s output vertex lies below the base immediately after that earlier instruction (`progVertex_lt`); since $i'+1\le i$, monotonicity of the program base (`progBase_mono`) places it below the current base as well. If the source is invalid, its assigned vertex is $n$, which is below the base because the base is at least $n+2$.

**Key facts.** `BoolCircuit.progVertex_lt`, `BoolCircuit.progBase_mono`.
