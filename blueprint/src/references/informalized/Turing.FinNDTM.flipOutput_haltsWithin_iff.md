<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PTM.lean :: Turing.FinNDTM.flipOutput_haltsWithin_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output Flipping Preserves Halting

**Claim.** The machine obtained by complementing each emitted bit halts within $t$ steps on $x$ along every branch if and only if $N$ does.

**Proof.** Fix a choice word. Flipping the machine's output leaves the initial configuration equal to the output-flipped initial configuration (`Turing.NDTM.flipOutput_initCfg`), and running the flipped machine on that word produces the output-flipped version of the original run (`Turing.NDTM.flipOutput_runWith`). Output flipping changes only the output component of a configuration, not its state, so the two resulting states agree. Thus this branch ends in the halting state for one machine exactly when it does for the other. Applying this equivalence to every word of length $t$ gives both implications.

**Key facts.** `Turing.NDTM.flipOutput_initCfg`, `Turing.NDTM.flipOutput_runWith`.
