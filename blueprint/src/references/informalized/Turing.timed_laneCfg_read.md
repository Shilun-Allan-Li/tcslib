<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timed_laneCfg_read -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reading the Active Lane

**Claim.** The zipper configuration reads the head entry of its right list on the selected lane, or blank if that list is empty.

**Proof.** At the selected lane, the updated tape and head position are the sweep tape determined by the frontier and the two lists, with the head located exactly at that frontier. The sweep-tape read identity (`Turing.FinTM.sweepTape_read`) says that reading there returns the head of the right list, joining the optional entry so that an empty list or blank entry yields blank. The update selects this lane, giving the result.

**Key facts.** `Turing.FinTM.sweepTape_read`.
