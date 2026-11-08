<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/VirtualInput.lean :: Turing.vhostSilentTM_runFrom -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Run Correspondence for the Silent Simulation

**Claim.** After $t$ steps, the silent simulation is exactly the encoded configuration of the corresponding $t$-step run of $M$, with a tag satisfying the boundary condition.

**Proof.** The extra final tape, called the cap tape, lies outside the image of the embedding of the first $m+1$ tapes; the layout result (`Turing.vhostSilent_layout`) supplies this disjointness. The silent-embedding run theorem (`Turing.embedSilentTM_runFrom`) therefore identifies the silent machine's run with the embedding of the emitting virtual-host machine's run, while keeping the cap tape's prescribed representation. Apply the emitting-machine run-correspondence theorem (`Turing.vhostEmitTM_runFrom`) for $t$ steps, starting with the empty output prefix. It gives a tag satisfying the boundary condition and identifies that emitting run with the encoded run of $M$. Substituting this equality into the embedding correspondence yields the claimed silent-simulation configuration.

**Key facts.** `Turing.vhostSilent_layout`, `Turing.vhostEmitTM_runFrom`, `Turing.embedSilentTM_runFrom`.
