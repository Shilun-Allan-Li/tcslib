<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.emCall_track_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Time Cost of Tracking

**Claim.** If the source machine halts on $x$ after exactly $T$ steps with output $o$, then the tracked machine halts on $x$ after exactly $1+2T$ steps with the same output.

**Proof.** Unpack the source machine's time-and-output property using the characterization of computation (Turing.FinTM.computesInTime_iff): at time $T$ its state is absent and its output is $o$. The tracked-run identity (Turing.FinTM.emCall_track_run) says that after $1+2T$ steps the tracked machine is in the tracked configuration built from that source configuration. Its state is the image of the source state, hence is absent, and its output is unchanged, so it is $o$. The same computation characterization then gives the claimed time and output property, with a suitable space value supplied by its existential definition.

**Key facts.** `Turing.FinTM.computesInTime_iff`, `Turing.FinTM.emCall_track_run`.
