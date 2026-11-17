<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.MachineFormat.exists_canonHeaderSeam -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Canonical Header Seam Machine

**Claim.** For every machine format $F$, a finite Boolean Turing machine with at least one work tape reaches a configuration containing the canonical header on tape zero, with the specified entry and exit states and unchanged input-head position and output, within linear time; its exit state is not reached earlier.

**Proof.** Start with the header-call machine supplied by `Turing.MachineFormat.exists_canonHeaderCall`. It reaches its designated exit configuration after a positive, linearly bounded number of steps, and does not reach that exit at any strictly intermediate positive time. There are two cases. If the entry and exit states differ, time zero is already distinct from the exit state. Thus the call machine itself has no earlier visit to its exit, including at time zero, and its run gives the required seam. If entry and exit coincide, use the release construction: `Turing.seamReleaseTM_firstReturn` converts the first positive return to the anchor state into a distinct released exit state and guarantees that this released state was not visited at any earlier time, including time zero. The final configuration is the original returned configuration with its state relabeled, so its tapes, input head, and output remain as required. In either case the same linear time bound and positive time are retained.

**Key facts.** `Turing.MachineFormat.exists_canonHeaderCall`, `Turing.seamReleaseTM_firstReturn`.
