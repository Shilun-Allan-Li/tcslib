<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepBlockLoop.lean :: Turing.StepBlock.hostedLoop_read -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reading a Hosted Configuration

**Claim.** The virtual-host configuration built from the loop configuration has state $(q,b)$, input position $p$, output equal to the prefix followed by $e$'s output, and reads the output summary of $c'$ on the bank corresponding to the summary tape.

**Proof.** The representation relation says that the compiled configuration's summary tape stores the summary cells formed from the output summary of $c'$. Since the summary head is at position zero, the symbol under it is exactly that output summary. The counter-loop configuration preserves the compiled configuration's input position and output, and places the counter tape separately; the identity `counter_cfg_eq` makes these fields explicit. In the virtual-host configuration, the state is obtained by pairing the loop state with $b$, the input position is set to $p$, and the output is prefixed by `pre`. Its bank for the summary tape has the same head position and contents as that tape, so its scanned symbol is the same output summary. These field computations give the four asserted equalities.

**Key facts.** `Turing.counter_cfg_eq`.
