<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.copyTM_run_ofCfg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Copying from a General Configuration

**Claim.** Under the stated sweep-state and source-tape buffer hypotheses, after $2|w|+2$ steps the copying machine is done, has written the buffer representation of $w$ on the destination tape from its original head position, and satisfies the stated earlier-time and head-position bounds.

**Proof.** Use the exact run description supplied by the copying-trace formula (Turing.catalog_copy_trace), which expresses the configuration at every time as the explicitly defined forward and return portions of the copy schedule. At time $2|w|+2$, simplifying that description places the machine in the done state and gives the stated destination-tape update: on the interval from the destination head through the next $|w|$ cells it contains the buffer representation of $w$, and outside that interval its contents are unchanged. The same description shows that at every earlier time the state is not done. Finally, for each time up to and including the endpoint, its forward and return cases place the source and destination heads between their initial positions minus one and their initial positions plus $|w|$; all other heads remain fixed. These are direct integer bounds on the positions in the trace formula.

**Key facts.** `Turing.catalog_copy_trace`.
