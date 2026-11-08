<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSchedule.lean :: Complexity.obliviousSchedule_output -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# No output from schedule transitions

**Claim.** Every transition of the schedule machine emits no output symbol, for every state, scanned input symbol, and work-tape contents.

**Proof.** Inspect the transition by schedule phase. In every phase other than the simulation of a transition of the original machine, the schedule uses an action whose output component is defined to be absent. In the simulation phase, the schedule may use the original machine’s output to write a bit on its budget tape, but its constructed action still has output component `none`. Hence every branch has absent output.
