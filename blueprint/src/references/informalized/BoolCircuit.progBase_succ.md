<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyProgram.lean :: BoolCircuit.progBase_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successive program base offsets

**Claim.** For every valid instruction position $i$, the base offset after the first $i+1$ instructions is the base offset after the first $i$ instructions plus the width of instruction $i$'s kind.

**Proof.** Expand the definition of the base offset. Since $i$ is a valid position, the first $i+1$ instructions are the first $i$ instructions followed by instruction $i$. Mapping their kinds to widths therefore gives the list of the first $i$ widths with the width of instruction $i$ appended. The sum of this list is the sum of the first $i$ widths plus that final width; the common initial offset $n+2$ then yields the asserted equality.
