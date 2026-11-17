<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean :: Turing.FinTM.dg_turn_with_growth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rightward Crossing with Window Growth

**Claim.** Under the stated positive-crossing and symbol-consistency hypotheses, the simulator reaches the reflected writing phase after $k+2$ steps, with the source transition’s updated input position and output. The right stack gains the reversed encoded guard block, the left stack is the boundary marker, and the work head remains in $[z-1,z+k]$.

**Proof.** Let $d$ be the initial read-phase configuration. Since the sweep reads at its frontier, its scanned work symbol is the boundary marker (`sweepTape_read`). The read-boundary transition rule (`dg_read_boundary`), together with the retraction identity (`dgInput_read`), the agreement of the table with the source tape reads, and the positive-crossing hypothesis, makes the first simulator step a stationary move into the initial right-growth state. Both endpoint head positions lie in $[z-1,z+k]$, so the one-step span result (`dgSpan_one`) records this step and its head bound.

Next, the right-growth sweep visits the $k$ work-tape positions. The growth-span result (`dg_right_span`) says that these $k$ steps append the reversed encoded guard block to the left stack, move the frontier to $z+k$, and consume the boundary entry from the right stack. Because $k>0$, dropping $k$ entries from the singleton boundary list leaves the empty list. Finally, the turn rule (`dg_turn`) gives the next step: it writes the boundary marker onto the right stack, reverses the sweep, and reaches the writing state at frontier $z+k-1$, with the source transition’s updated input position and output. Its endpoint head position also lies in the required interval. Composing these three spans with `dgSpan_add` gives $1+k+1=k+2$ steps and preserves the common head bound throughout.

**Key facts.** `Turing.FinTM.sweepTape_read`, `Turing.FinTM.dg_read_boundary`, `Turing.FinTM.dgInput_read`, `Turing.FinTM.dgSpan_one`, `Turing.FinTM.dg_right_span`, `Turing.FinTM.dg_turn`, `Turing.FinTM.dgSpan_add`.
