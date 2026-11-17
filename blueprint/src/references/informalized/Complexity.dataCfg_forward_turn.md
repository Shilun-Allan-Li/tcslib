<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean :: Complexity.dataCfg_forward_turn -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Forward Scan Boundary Turn

**Claim.** At the right boundary $R+1$, one forward-phase simulator step enters the backward phase at $R$, resets every neighbor register to the blank payload, and leaves the other data and the output unchanged.

**Proof.** Because the guide tape is the radius-$R$ guide, its symbol at $R+1$ is the right-edge marker. The forward transition therefore switches to the backward phase and moves the guide head to $(R+1)-1=R$. At this boundary the visit rule does not write data cells or emit output; it preserves the state, answer bit, saved reads, and tapes, while setting every neighbor register to the blank payload. Substituting these effects into the decorated transition yields the claimed configuration.

**Key facts.** `Complexity.dataCfg_step`, `Complexity.macroCfg_forward`, `Complexity.macroCfg_guide`, `Complexity.guideTape_right`.
