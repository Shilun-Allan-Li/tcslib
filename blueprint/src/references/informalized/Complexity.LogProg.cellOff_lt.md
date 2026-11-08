<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Layout.lean :: Complexity.LogProg.cellOff_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cell Offset Bound

**Claim.** If the cell position is less than the word length of the defaulted segment, then its cell offset is less than that segment's rendered length.

**Proof.** Fix the defaulted segment, writing it as a word $w$ and a flag $d$. If $d$ is false, the offset is $c$ and the rendered length is $|w|$, so the assumed inequality gives the result directly. If $d$ is true, the offset is $2c+p$, where $p$ is either $0$ or $1$, and the rendered length is $2|w|$. Since $c<|w|$, we have $2c+1<2|w|$; hence either possible offset is strictly below the rendered length.
