<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerSound.lean :: Complexity.Meyer.ruleW_congr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Work-Tape Rule Congruence

**Claim.** If two tape-content functions agree at every integer within distance $|d|+1$ of the origin, then the work-tape update rule at offset $d$ gives the same result for both.

**Proof.** If the machine state is absent, the rule simply reads the content at offset $d$, and the hypothesis applies because $|d|\le |d|+1$. If the state is present, write $m$ for the work-tape head movement. When the updated head position $d+m$ is zero, both evaluations use the same local write-or-retain rule and the same currently read symbol, so their outputs agree. Otherwise, each result is read from the content function at $d+m$. Since a head movement is one of $-1,0,1$, the assumption $d+m\ne0$ implies $|d+m|\le |d|+1$; the two functions therefore agree at that position as well.
