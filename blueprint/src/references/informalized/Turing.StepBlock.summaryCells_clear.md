<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepBlock.lean :: Turing.StepBlock.summaryCells_clear -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clearing the Summary Word Region

**Claim.** For every integer cell, replacing the content by blank on the interval $2\le z<2+|w|$ and retaining the original summary-cell content elsewhere gives the summary-cell function for the empty word.

**Proof.** Fix a cell $z$. The copying identity `summaryCells_copy` expresses the summary-cell content for $w$ as the shifted buffer content on the interval $2\le z<2+|w|$, and as the empty-word summary-cell content outside that interval. If $z$ lies in the interval, then $z\ne0$, so the summary-cell content for $w$ is exactly that buffer content; both sides of the desired equality are blank there. If $z$ lies outside the interval, the replacement retains the summary-cell content for $w$, which by the copying identity is the empty-word summary-cell content. Thus the functions agree at every cell.

**Key facts.** `Turing.StepBlock.summaryCells_copy`.
