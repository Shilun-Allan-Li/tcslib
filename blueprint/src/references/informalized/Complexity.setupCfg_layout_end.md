<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean :: Complexity.setupCfg_layout_end -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# End of an Outward Allocation Pass

**Claim.** At the endpoint of either outward allocation pass, one step enters the corresponding edge phase, leaves the unary head at $B+1$, moves the guide head one cell in the chosen direction, and writes an interior mark at the guide head's former position.

**Proof.** At unary position $B+1$, the unary tape is blank by `unaryTape_end`. Therefore the allocation transition takes its endpoint branch: it enters the right-edge or left-edge phase according to the chosen direction, writes an interior mark at the current guide position, and moves the guide head one cell in that direction. It leaves the unary head and tape unchanged. Translating this action into the fields of a setup configuration using `setupCfg_apply` gives the stated head positions and updated guide tape.

**Key facts.** `Complexity.unaryTape_end`, `Complexity.setupCfg_apply`.
