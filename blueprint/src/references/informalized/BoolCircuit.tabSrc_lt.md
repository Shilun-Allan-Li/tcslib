<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauCircuit.lean :: BoolCircuit.tabSrc_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Source vertices precede the stage base

**Claim.** For every stage and source, the vertex index assigned by the tabulation encoding is strictly less than the base vertex index of that stage.

**Proof.** First observe that the tabulation width is nonnegative, so its contribution at stage $i+1$ is at least one copy of that width. If the source is invalid, its assigned index is $n$, which is below the stage base. For a valid input source, split according to whether its index lies in the prefix $z$: in the prefix case its index is $n+2+k$ with $k<|z|$; otherwise it is the shifted original-input index $k-|z|$, with $k<|z|+n$. Either bound places it below the base, which includes the constants and the entire prefix. A valid constant is assigned to one of the two designated constant vertices, both below the base. Finally, for a valid earlier block bit $(i',j)$, we have $i'<i$ and $j<w$. Thus the offset from the current base is bounded by the width of one stage: the earlier block’s base is at most one stage-width before the current base, and its bit position plus the intervening $m$ and tabulation-width offsets is strictly less than that width. Hence this source index too lies below the current base.
