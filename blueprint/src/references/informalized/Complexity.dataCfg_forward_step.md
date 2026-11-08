<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean :: Complexity.dataCfg_forward_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Forward Scan Step

**Claim.** Away from the right guide boundary, one forward-phase simulator step advances the guide head from $g$ to $g+1$, updates the neighbor registers from the current payloads at $g$, and writes at $g$ a cell containing those current payloads together with the old neighbor registers; the other stored data and the output remain unchanged.

**Proof.** The guide-head symbol is read from the base guide tape. Since that tape is the radius-$R$ guide and $g\ne R+1$, the forward-scan transition takes its interior branch: it stays in the forward phase and moves the guide head to $g+1$. In that branch, the visit rule leaves the state, answer bit, saved reads, and output untouched; it replaces the neighbor registers by the decoded current payloads at $g$ and writes at $g$ a cell whose current component is that same decoded payload and whose left component is the old neighbor register. Unpacking the decorated transition gives precisely the stated configuration.

**Key facts.** `Complexity.dataCfg_step`, `Complexity.macroCfg_forward`, `Complexity.macroCfg_guide`, `Complexity.guideTape_right`.
